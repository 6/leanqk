//! The type checker and the declaration checks, following Lean's C++
//! kernel (`src/kernel` at v4.36.0): `type_checker.cpp` (`tc.rs`),
//! `inductive.cpp` (`inductive.rs`), `quot.cpp` (`quot.rs`),
//! `instantiate.cpp` and `abstract.cpp` (`subst.rs`), `level.cpp`
//! (`univ.rs`, which decides level constraints exactly) and
//! `environment.cpp` (this file).
//!
//! Declarations are checked in export order; each sees only the
//! declarations before it (and, for an unsafe or partial mutual group, the
//! rest of its group). Checking one declaration reads the environment and
//! writes only into its own [`store::Store`] and caches, so independent
//! declarations could be checked on several threads; for now there is one.

mod eval;
pub use eval::stats as eval_stats;
pub mod ext;
mod fingerprint;
mod fingerprint_table;
pub mod inductive;
pub mod pp;
mod quot;
pub mod store;
mod subst;
pub mod tc;
pub mod univ;

use std::panic::{AssertUnwindSafe, catch_unwind};

use crate::env::{Block, BlockKind, Decl, DeclKind, Env, Safety};
use crate::name::NameId;

use ext::Ext;
use inductive::{IndDecl, IndType, RecNaming, alpha_eq};
use store::{LOCAL, Store};
use tc::{KErr, Mode, R, Tc, err};

pub use fingerprint::{Checker as Fingerprints, hex as hex_digest, key as fingerprint_key};

/// Why checking stopped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FailKind {
    /// The declaration is not valid.
    Rejected,
    /// A resource limit was hit; this says nothing about validity.
    Resource,
}

#[derive(Clone, Debug)]
pub struct Failure {
    pub kind: FailKind,
    /// The declaration that failed (for an inductive block, its first type).
    pub decl: String,
    pub msg: String,
}

#[derive(Clone, Debug, Default)]
pub struct Report {
    pub declarations: usize,
    /// Built-in extensions that are off, and why.
    pub notes: Vec<String>,
}

/// Stack for the checker thread: the checker recurses on terms.
const STACK_BYTES: usize = 1 << 30;

/// Check every declaration of `env`, stopping at the first failure.
pub fn check_env(env: &Env) -> Result<Report, Failure> {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .name("nitrolean-check".into())
            .stack_size(STACK_BYTES)
            .spawn_scoped(s, || check_env_here(env))
            .expect("spawn checker thread")
            .join()
            .unwrap_or_else(|_| {
                Err(Failure {
                    kind: FailKind::Resource,
                    decl: String::new(),
                    msg: "checker thread failed".into(),
                })
            })
    })
}

fn check_env_here(env: &Env) -> Result<Report, Failure> {
    let fail = |msg: &str| Failure {
        kind: FailKind::Resource,
        decl: String::new(),
        msg: msg.into(),
    };
    for (n, what) in [
        (env.names.len(), "names"),
        (env.levels.len(), "levels"),
        (env.exprs.len(), "expressions"),
        (env.decls.len(), "declarations"),
    ] {
        if n >= LOCAL as usize {
            return Err(fail(&format!(
                "too many {what} (at most 2^31 are supported)"
            )));
        }
    }
    let ext = Ext::new(env);
    let mut tc = Tc::new(Store::new(env), &ext, 0);
    // `NITROLEAN_DECL_TIMES=FILE`: write each block's first name and check
    // time (seconds) to FILE, for benchmarks.
    let mut times = std::env::var_os("NITROLEAN_DECL_TIMES")
        .and_then(|p| std::fs::File::create(p).ok())
        .map(std::io::LineWriter::new);
    for b in &env.blocks {
        let decls = env.block_decls(b);
        let first = decls.first().map(|d| d.name);
        let t0 = std::time::Instant::now();
        let res = catch_unwind(AssertUnwindSafe(|| check_block(&mut tc, b)));
        if let (Some(w), Some(n)) = (times.as_mut(), first) {
            use std::io::Write;
            let _ = writeln!(
                w,
                "{}\t{:.6}",
                env.names.display(n),
                t0.elapsed().as_secs_f64()
            );
        }
        let res = match res {
            Ok(r) => r.map_err(|e| (FailKind::Rejected, e.0)),
            Err(p) => {
                let msg = p
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_else(|| "internal error".into());
                // Rebuild: the checker's state may be inconsistent.
                tc = Tc::new(Store::new(env), &ext, 0);
                Err((FailKind::Resource, msg))
            }
        };
        if let Err((kind, msg)) = res {
            let decl = match first {
                Some(n) => env.names.display(n).to_string(),
                None => String::new(),
            };
            return Err(Failure { kind, decl, msg });
        }
    }
    Ok(Report {
        declarations: env.decls.len(),
        notes: ext.notes.clone(),
    })
}

/// Whether Lean's checker skips `d`: like `Environment.replay`, which
/// `leanchecker --from-export` runs, nitrolean does not check unsafe and
/// partial declarations. They carry no logical content: no safe
/// declaration can refer to them.
fn skipped(d: &Decl) -> bool {
    match d.kind {
        DeclKind::Definition { safety, .. } => safety != Safety::Safe,
        _ => Tc::decl_is_unsafe(d),
    }
}

fn check_block(tc: &mut Tc<'_>, b: &Block) -> R<()> {
    tc.reset(b.start);
    let env = tc.st.env;
    let decls = env.block_decls(b);
    if decls.first().is_some_and(skipped) {
        return Ok(());
    }
    match b.kind {
        BlockKind::Single => check_single(tc, &decls[0]),
        BlockKind::Inductive { types, ctors, .. } => {
            check_inductive_block(tc, decls, types as usize, ctors as usize)
        }
    }
}

fn check_dup_lparams(tc: &Tc<'_>, d: &Decl) -> R<()> {
    let ps = tc.st.lparams(d);
    for (i, p) in ps.iter().enumerate() {
        if ps[i + 1..].contains(p) {
            return err(format!(
                "failed to add declaration to environment, duplicate universe level parameter: '{}'",
                tc.show(*p)
            ));
        }
    }
    Ok(())
}

/// Lean's `check_constant_val`: the type is a well-formed type.
fn check_header(tc: &mut Tc<'_>, d: &Decl) -> R<()> {
    check_dup_lparams(tc, d)?;
    let lps: Vec<NameId> = tc.st.lparams(d).to_vec();
    let s = tc.check(d.ty, &lps)?;
    tc.ensure_sort(s)?;
    Ok(())
}

fn check_value(tc: &mut Tc<'_>, d: &Decl, value: crate::expr::ExprId) -> R<()> {
    let lps: Vec<NameId> = tc.st.lparams(d).to_vec();
    let vt = tc.check(value, &lps)?;
    if !tc.is_def_eq(vt, d.ty)? {
        return err(format!(
            "declaration type mismatch, value has type {} but is expected to have type {}",
            tc.pp(vt),
            tc.pp(d.ty)
        ));
    }
    Ok(())
}

fn check_single(tc: &mut Tc<'_>, d: &Decl) -> R<()> {
    match d.kind {
        DeclKind::Axiom { is_unsafe } => {
            tc.mode = if is_unsafe { Mode::Unsafe } else { Mode::Safe };
            check_header(tc, d)
        }
        DeclKind::Definition {
            value, safety, all, ..
        } => {
            tc.mode = match safety {
                Safety::Safe => Mode::Safe,
                Safety::Unsafe => Mode::Unsafe,
                Safety::Partial => Mode::Partial,
            };
            if safety != Safety::Safe {
                // An unsafe or partial (mutual) group: its members may refer
                // to one another (Lean's `add_mutual`, and `add_definition`
                // for an unsafe one). They must agree on safety and
                // universe parameters.
                let env = tc.st.env;
                let mut extra = Vec::new();
                for &n in env.name_list(all) {
                    let Some(m) = env.find(n) else {
                        return err(format!("mutual declaration '{}' is missing", tc.show(n)));
                    };
                    match m.kind {
                        DeclKind::Definition { safety: s2, .. } if s2 == safety => {}
                        _ => {
                            return err(
                                "invalid mutual definition, declarations must have the same safety annotation",
                            );
                        }
                    }
                    if env.name_list(m.level_params) != env.name_list(d.level_params) {
                        return err(
                            "invalid mutual definition, declarations must have the same universe level parameters",
                        );
                    }
                    extra.push(n);
                }
                check_header(tc, d)?;
                tc.extra = extra;
                tc.extra.push(d.name);
                check_value(tc, d, value)
            } else {
                check_header(tc, d)?;
                check_value(tc, d, value)
            }
        }
        DeclKind::Theorem { value, .. } => {
            tc.mode = Mode::Safe;
            check_header(tc, d)?;
            if !tc.is_prop(d.ty)? {
                return err(format!("theorem type is not Prop: {}", tc.pp(d.ty)));
            }
            check_value(tc, d, value)
        }
        DeclKind::Opaque {
            value, is_unsafe, ..
        } => {
            tc.mode = if is_unsafe { Mode::Unsafe } else { Mode::Safe };
            check_header(tc, d)?;
            check_value(tc, d, value)
        }
        DeclKind::Quot { kind } => {
            check_dup_lparams(tc, d)?;
            tc.check_quot(d, kind)
        }
        DeclKind::Inductive { .. } | DeclKind::Constructor { .. } | DeclKind::Recursor { .. } => {
            err("inductive types, constructors and recursors must come in an inductive block")
        }
    }
}

fn check_inductive_block(tc: &mut Tc<'_>, decls: &[Decl], ntypes: usize, nctors: usize) -> R<()> {
    let env = tc.st.env;
    let (types, rest) = decls.split_at(ntypes);
    let (ctors, recs) = rest.split_at(nctors);
    let Some(first) = types.first() else {
        return err("invalid empty (mutual) inductive datatype declaration");
    };
    let DeclKind::Inductive {
        num_params,
        is_unsafe,
        ..
    } = first.kind
    else {
        return err("ill-formed inductive block");
    };
    let lparams: Vec<NameId> = env.name_list(first.level_params).to_vec();
    let mut claimed = vec![false; ctors.len()];
    let mut ind_types = Vec::new();
    for t in types {
        let DeclKind::Inductive {
            num_params: np,
            is_unsafe: u,
            ctors: cs,
            ..
        } = t.kind
        else {
            return err("ill-formed inductive block");
        };
        if np != num_params || u != is_unsafe || env.name_list(t.level_params) != lparams {
            return err(format!(
                "the types of mutual inductive block '{}' disagree on their parameters, universe parameters or safety",
                tc.show(first.name)
            ));
        }
        let mut cv = Vec::new();
        for &c in env.name_list(cs) {
            let Some(i) = ctors.iter().position(|d| d.name == c) else {
                return err(format!(
                    "constructor '{}' of '{}' is not in its inductive block",
                    tc.show(c),
                    tc.show(t.name)
                ));
            };
            if claimed[i] {
                return err(format!("constructor '{}' is claimed twice", tc.show(c)));
            }
            claimed[i] = true;
            cv.push((c, ctors[i].ty));
        }
        ind_types.push(IndType {
            name: t.name,
            ty: t.ty,
            ctors: cv,
        });
    }
    if let Some(i) = claimed.iter().position(|c| !c) {
        return err(format!(
            "constructor '{}' does not belong to any type of its inductive block",
            tc.show(ctors[i].name)
        ));
    }
    let decl = IndDecl {
        lparams: lparams.clone(),
        nparams: num_params,
        types: ind_types,
        is_unsafe,
    };
    let main_rec = tc.rec_name_of(first.name)?;
    let elim_param = recs.iter().find(|r| r.name == main_rec).and_then(|r| {
        let lps = env.name_list(r.level_params);
        (lps.len() == lparams.len() + 1).then(|| lps[0])
    });
    let generated = tc.add_inductive(&decl, &RecNaming { elim_param })?;
    // The export must contain exactly the derived declarations.
    for g in &generated {
        let Some(x) = decls.iter().find(|x| x.name == g.name) else {
            return err(format!(
                "the inductive block lacks the derived declaration '{}'",
                tc.show(g.name)
            ));
        };
        compare_decl(tc, g, x)?;
    }
    if generated.len() != decls.len() {
        let extra = decls
            .iter()
            .find(|x| !generated.iter().any(|g| g.name == x.name))
            .map(|x| tc.show(x.name))
            .unwrap_or_default();
        return err(format!(
            "the inductive block declares '{extra}', which is not derived from its types"
        ));
    }
    Ok(())
}

fn compare_decl(tc: &Tc<'_>, g: &Decl, x: &Decl) -> R<()> {
    let bad = |what: &str| -> R<()> {
        Err(KErr(format!(
            "'{}' does not match the declaration derived from its inductive type ({what})",
            tc.show(x.name)
        )))
    };
    let names = |l| tc.st.name_list(l).to_vec();
    if names(g.level_params) != names(x.level_params) {
        return bad("universe parameters");
    }
    if !alpha_eq(tc, g.ty, x.ty) {
        return bad("type");
    }
    match (g.kind, x.kind) {
        (
            DeclKind::Inductive {
                num_params: a1,
                num_indices: b1,
                all: c1,
                ctors: d1,
                num_nested: e1,
                is_rec: f1,
                is_reflexive: g1,
                is_unsafe: h1,
            },
            DeclKind::Inductive {
                num_params: a2,
                num_indices: b2,
                all: c2,
                ctors: d2,
                num_nested: e2,
                is_rec: f2,
                is_reflexive: g2,
                is_unsafe: h2,
            },
        ) => {
            if (a1, b1, e1, f1, g1, h1) != (a2, b2, e2, f2, g2, h2) {
                return bad("numParams, numIndices, numNested, isRec, isReflexive or isUnsafe");
            }
            if names(c1) != names(c2) || names(d1) != names(d2) {
                return bad("all or ctors");
            }
        }
        (
            DeclKind::Constructor {
                induct: a1,
                cidx: b1,
                num_params: c1,
                num_fields: d1,
                is_unsafe: e1,
            },
            DeclKind::Constructor {
                induct: a2,
                cidx: b2,
                num_params: c2,
                num_fields: d2,
                is_unsafe: e2,
            },
        ) => {
            if (a1, b1, c1, d1, e1) != (a2, b2, c2, d2, e2) {
                return bad("induct, cidx, numParams, numFields or isUnsafe");
            }
        }
        (
            DeclKind::Recursor {
                all: a1,
                num_params: b1,
                num_indices: c1,
                num_motives: d1,
                num_minors: e1,
                rules: f1,
                k: g1,
                is_unsafe: h1,
            },
            DeclKind::Recursor {
                all: a2,
                num_params: b2,
                num_indices: c2,
                num_motives: d2,
                num_minors: e2,
                rules: f2,
                k: g2,
                is_unsafe: h2,
            },
        ) => {
            if (b1, c1, d1, e1, g1, h1) != (b2, c2, d2, e2, g2, h2) {
                return bad(&format!(
                    "numParams, numIndices, numMotives, numMinors, k, isUnsafe: derived {:?}, exported {:?}",
                    (b1, c1, d1, e1, g1, h1),
                    (b2, c2, d2, e2, g2, h2)
                ));
            }
            if names(a1) != names(a2) {
                return bad("all");
            }
            let (r1, r2) = (tc.st.rec_rules(f1), tc.st.rec_rules(f2));
            if r1.len() != r2.len() {
                return bad("number of rules");
            }
            for (p, q) in r1.iter().zip(r2) {
                if p.ctor != q.ctor || p.nfields != q.nfields {
                    return bad("rule constructor or field count");
                }
                if !alpha_eq(tc, p.rhs, q.rhs) {
                    return bad("rule right-hand side");
                }
            }
        }
        _ => return bad("kind of declaration"),
    }
    Ok(())
}
