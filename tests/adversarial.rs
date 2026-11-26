//! Exports aimed at the checker's shortcuts: caches that are kept between
//! declarations, free variables shared between binders of the same type,
//! proof irrelevance and the order in which threads check declarations.
//! Each is written here with [`Export`], a builder of the export format
//! (3.1) that numbers names, levels and expressions itself.

use nitrolean::check::{FailKind, check_env_jobs};
use nitrolean::reader::read_str;

/// An export under construction. Ids start at 1 for names and levels (0 is
/// the anonymous name and level zero) and at 0 for expressions.
struct Export {
    out: String,
    names: u32,
    levels: u32,
    exprs: u32,
}

type E = u32;

impl Export {
    fn new() -> Self {
        Export {
            out: "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n".into(),
            names: 0,
            levels: 0,
            exprs: 0,
        }
    }

    fn name(&mut self, s: &str) -> u32 {
        self.names += 1;
        let id = self.names;
        self.out.push_str(&format!(
            "{{\"in\":{id},\"str\":{{\"pre\":0,\"str\":\"{s}\"}}}}\n"
        ));
        id
    }

    fn level(&mut self, node: &str) -> u32 {
        self.levels += 1;
        let id = self.levels;
        self.out.push_str(&format!("{{\"il\":{id},{node}}}\n"));
        id
    }

    fn param(&mut self, name: u32) -> u32 {
        self.level(&format!("\"param\":{name}"))
    }

    fn succ(&mut self, l: u32) -> u32 {
        self.level(&format!("\"succ\":{l}"))
    }

    fn expr(&mut self, node: String) -> E {
        let id = self.exprs;
        self.exprs += 1;
        self.out.push_str(&format!("{{\"ie\":{id},{node}}}\n"));
        id
    }

    fn sort(&mut self, l: u32) -> E {
        self.expr(format!("\"sort\":{l}"))
    }

    fn bvar(&mut self, i: u32) -> E {
        self.expr(format!("\"bvar\":{i}"))
    }

    fn cnst(&mut self, name: u32, us: &[u32]) -> E {
        self.expr(format!("\"const\":{{\"name\":{name},\"us\":{us:?}}}"))
    }

    fn app(&mut self, f: E, args: &[E]) -> E {
        args.iter().fold(f, |f, &a| {
            self.expr(format!("\"app\":{{\"fn\":{f},\"arg\":{a}}}"))
        })
    }

    fn binder(&mut self, kind: &str, ty: E, body: E) -> E {
        self.expr(format!(
            "\"{kind}\":{{\"binderInfo\":\"default\",\"body\":{body},\"name\":0,\"type\":{ty}}}"
        ))
    }

    fn lam(&mut self, ty: E, body: E) -> E {
        self.binder("lam", ty, body)
    }

    fn pi(&mut self, ty: E, body: E) -> E {
        self.binder("forallE", ty, body)
    }

    fn def(&mut self, name: u32, params: &[u32], ty: E, value: E) {
        self.out.push_str(&format!(
            "{{\"def\":{{\"all\":[{name}],\"hints\":\"opaque\",\"levelParams\":{params:?},\"name\":{name},\"safety\":\"safe\",\"type\":{ty},\"value\":{value}}}}}\n"
        ));
    }

    fn thm(&mut self, name: u32, params: &[u32], ty: E, value: E) {
        self.out.push_str(&format!(
            "{{\"thm\":{{\"all\":[{name}],\"levelParams\":{params:?},\"name\":{name},\"type\":{ty},\"value\":{value}}}}}\n"
        ));
    }

    /// The verdict with one checking thread, after checking that 2 and 8
    /// threads give the same one.
    fn check(&self) -> Result<(), (FailKind, String, String)> {
        let env = read_str(&self.out).unwrap();
        let one = check_env_jobs(&env, 1)
            .map(|_| ())
            .map_err(|f| (f.kind, f.decl, f.msg));
        for jobs in [2, 8] {
            let many = check_env_jobs(&env, jobs)
                .map(|_| ())
                .map_err(|f| (f.kind, f.decl, f.msg));
            assert_eq!(one, many, "{jobs} threads");
        }
        one
    }
}

fn rejected(r: Result<(), (FailKind, String, String)>, decl: &str, why: &str) {
    match r {
        Err((FailKind::Rejected, d, m)) if d == decl && m.contains(why) => {}
        other => panic!("expected '{decl}' to be rejected ({why}), got {other:?}"),
    }
}

/// `fun x y P h => h : (x y : α) → (P : α → Prop) → P x → P y`, under the
/// binders `outer` (closed types, outermost first) and with `α` the
/// expression `alpha` in the context of those binders: a transport of `P x`
/// to `P y` that only holds if `x` and `y` are the same variable, or proofs
/// of one proposition.
fn transport(x: &mut Export, outer: &[E], alpha: impl Fn(&mut Export, u32) -> E) -> (E, E) {
    let prop = x.sort(0);
    // Types: x : α, y : α, P : α → Prop, h : P x; result P y.
    let a0 = alpha(x, 0);
    let a1 = alpha(x, 1);
    let a2_for_p = alpha(x, 2);
    let p_ty = x.pi(a2_for_p, prop);
    let b0 = x.bvar(0);
    let b1 = x.bvar(1);
    let b2 = x.bvar(2);
    let p_x = x.app(b0, &[b2]); // under x, y, P
    let p_y = x.app(b1, &[b2]); // under x, y, P, h
    let ty_h = x.pi(p_x, p_y);
    let ty_p = x.pi(p_ty, ty_h);
    let ty_y = x.pi(a1, ty_p);
    let mut ty = x.pi(a0, ty_y);
    let h = x.bvar(0);
    let p_x_v = x.app(b0, &[b2]);
    let v_h = x.lam(p_x_v, h);
    let v_p = x.lam(p_ty, v_h);
    let v_y = x.lam(a1, v_p);
    let mut value = x.lam(a0, v_y);
    for &o in outer.iter().rev() {
        ty = x.pi(o, ty);
        value = x.lam(o, value);
    }
    (ty, value)
}

/// Two variables of the same type are not the same variable, wherever their
/// binders are: `(α : Type) → (x y : α) → P x → P y` has no proof by `h`.
#[test]
fn variables_of_one_type_stay_distinct() {
    let mut x = Export::new();
    let n = x.name("transport");
    let one = x.succ(0);
    let ty_sort = x.sort(one);
    // α is the outermost binder: bvar 0 under x's binder, then 1, 2.
    let (ty, value) = transport(&mut x, &[ty_sort], |x, depth| x.bvar(depth));
    x.def(n, &[], ty, value);
    rejected(x.check(), "transport", "type mismatch");
}

/// The same with `α : Sort u` for a universe parameter `u`, which may be
/// above `Prop`: proof irrelevance must not apply.
#[test]
fn proof_irrelevance_needs_a_proposition() {
    let mut x = Export::new();
    let n = x.name("transport");
    let u = x.name("u");
    let lu = x.param(u);
    let sort_u = x.sort(lu);
    let (ty, value) = transport(&mut x, &[sort_u], |x, depth| x.bvar(depth));
    x.def(n, &[u], ty, value);
    rejected(x.check(), "transport", "type mismatch");
}

/// With `α : Prop` the transport holds by proof irrelevance.
#[test]
fn proof_irrelevance_in_prop_is_accepted() {
    let mut x = Export::new();
    let n = x.name("transport");
    let prop = x.sort(0);
    let (ty, value) = transport(&mut x, &[prop], |x, depth| x.bvar(depth));
    x.thm(n, &[], ty, value);
    assert_eq!(x.check(), Ok(()));
}

/// A first declaration checks the transport at `α : Prop`, where it holds;
/// the same terms under `α : Type` must be checked again, not taken from
/// what the first declaration learned.
#[test]
fn checked_terms_are_not_reused_under_other_binders() {
    let mut x = Export::new();
    let good = x.name("good");
    let bad = x.name("bad");
    let prop = x.sort(0);
    let (ty, value) = transport(&mut x, &[prop], |x, depth| x.bvar(depth));
    x.thm(good, &[], ty, value);
    let one = x.succ(0);
    let ty_sort = x.sort(one);
    let (ty, value) = transport(&mut x, &[ty_sort], |x, depth| x.bvar(depth));
    x.def(bad, &[], ty, value);
    rejected(x.check(), "bad", "type mismatch");
}

/// A declaration may only use the declarations before it, however many
/// threads check the export and in whatever order they take its blocks:
/// `bad` applies a function to `c`, declared after it, and the declarations
/// after `c` check the same term, where `c` is in scope. With several
/// threads, one that has checked those may take over the blocks around
/// `bad` from another.
#[test]
fn forward_references_are_rejected_on_every_thread_count() {
    let mut x = Export::new();
    let t = x.name("T");
    let triv = x.name("t");
    let c = x.name("c");
    let bad = x.name("bad");
    let prop = x.sort(0);
    // T := (P : Prop) → P → P, t := fun P h => h.
    let b0 = x.bvar(0);
    let b1 = x.bvar(1);
    let p_to_p = x.pi(b0, b1);
    let t_ty = x.pi(prop, p_to_p);
    x.def(t, &[], prop, t_ty);
    let t_c = x.cnst(t, &[]);
    let id_h = x.lam(b0, b0);
    let t_v = x.lam(prop, id_h);
    x.def(triv, &[], t_c, t_v);
    let t_t = x.cnst(triv, &[]);
    // X := (fun _ : T => t) c.
    let k = x.lam(t_c, t_t);
    let c_c = x.cnst(c, &[]);
    let term = x.app(k, &[c_c]);
    let fillers = 3000;
    for i in 0..fillers {
        if i == 1400 {
            x.def(bad, &[], t_c, term);
        }
        if i == 2000 {
            x.def(c, &[], t_c, t_t);
        }
        let f = x.name(&format!("f{i}"));
        let v = if i > 2000 { term } else { t_t };
        x.def(f, &[], t_c, v);
    }
    rejected(x.check(), "bad", "unknown constant 'c'");
}

/// Two theorems that prove `∀ P : Prop, P` from each other.
#[test]
fn circular_theorems_are_rejected() {
    let mut x = Export::new();
    let a = x.name("a");
    let b = x.name("b");
    let prop = x.sort(0);
    let b0 = x.bvar(0);
    let false_ty = x.pi(prop, b0);
    let b_c = x.cnst(b, &[]);
    let a_c = x.cnst(a, &[]);
    x.thm(a, &[], false_ty, b_c);
    x.thm(b, &[], false_ty, a_c);
    rejected(x.check(), "a", "unknown constant 'b'");
}
