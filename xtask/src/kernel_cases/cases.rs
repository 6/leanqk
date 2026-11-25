//! The kernel test cases. Each case builds one export (a string) from a
//! toolchain.
//!
//! Expected verdicts:
//!   accept  a correct kernel must accept the export
//!   reject  a correct kernel must reject it
//!   either  the claims are true but need a resource the kernel may refuse
//!           (a Nat size limit); accepting and rejecting cleanly are both
//!           fine, crashing or hanging is not
//!
//! The order of the calls on an `Export` decides the ids of the new terms,
//! so the builders make their terms in a fixed order, one per statement.

use std::collections::BTreeSet;

use anyhow::Result;
use serde_json::{Value, json};

use super::Toolchain;
use super::export::{Binder, Export, Id, dumps};

type Build = Box<dyn Fn(&mut Toolchain) -> Result<String>>;

pub struct Case {
    pub id: &'static str,
    pub rule: &'static str,
    pub expected: &'static str,
    pub why: &'static str,
    pub build: Build,
}

/// The cases, in the order of cases.tsv.
pub fn cases() -> Vec<Case> {
    let mut v = Cases(Vec::new());
    nat_cases(&mut v);
    string_cases(&mut v);
    positivity_cases(&mut v);
    mutual_cases(&mut v);
    eta_cases(&mut v);
    meta_cases(&mut v);
    universe_cases(&mut v);
    quot_cases(&mut v);
    irrel_cases(&mut v);
    format_cases(&mut v);
    eval_cases(&mut v);
    fuzz_cases(&mut v);
    v.0
}

struct Cases(Vec<Case>);

impl Cases {
    /// A case whose builder returns the export's text.
    fn text(
        &mut self,
        id: &'static str,
        rule: &'static str,
        expected: &'static str,
        why: &'static str,
        f: impl Fn(&mut Toolchain) -> Result<String> + 'static,
    ) {
        assert!(matches!(expected, "accept" | "reject" | "either"));
        self.0.push(Case {
            id,
            rule,
            expected,
            why,
            build: Box::new(f),
        });
    }

    /// A case whose builder returns an export.
    fn add(
        &mut self,
        id: &'static str,
        rule: &'static str,
        expected: &'static str,
        why: &'static str,
        f: impl Fn(&mut Toolchain) -> Result<Export> + 'static,
    ) {
        self.text(id, rule, expected, why, move |tc| Ok(f(tc)?.text()));
    }
}

// ---------------------------------------------------------------------------
// helpers

/// A term: a Nat literal, a constant, or a constant applied to terms.
#[derive(Clone)]
enum Tm {
    N(String),
    C(&'static str),
    A(&'static str, Vec<Tm>),
}

use Tm::{A, C};

fn n(v: u128) -> Tm {
    Tm::N(v.to_string())
}

const U32: u128 = 1 << 32;
const P64: u128 = 1 << 64;
const P128: &str = "340282366920938463463374607431768211456";

fn consts_of(t: &Tm, acc: &mut BTreeSet<&'static str>) {
    match t {
        Tm::N(_) => {}
        Tm::C(s) => {
            acc.insert(s);
        }
        Tm::A(f, args) => {
            acc.insert(f);
            for a in args {
                consts_of(a, acc);
            }
        }
    }
}

fn term(e: &mut Export, t: &Tm) -> Id {
    match t {
        Tm::N(v) => e.nat(v),
        Tm::C(s) => e.c(s),
        Tm::A(f, args) => {
            let f = e.c(f);
            let args: Vec<Id> = args.iter().map(|a| term(e, a)).collect();
            e.app(f, &args)
        }
    }
}

fn eq(e: &mut Export, t: Id, a: Id, b: Id) -> Id {
    let one = e.lsucc(0);
    let f = e.konst("Eq", &[one]);
    e.app(f, &[t, a, b])
}

fn refl(e: &mut Export, t: Id, a: Id) -> Id {
    let one = e.lsucc(0);
    let f = e.konst("Eq.refl", &[one]);
    e.app(f, &[t, a])
}

/// theorem K.claim : @Eq ty lhs rhs := @Eq.refl ty lhs
fn claim(tc: &mut Toolchain, lhs: &Tm, rhs: &Tm, ty: &'static str) -> Result<Export> {
    let mut cs = BTreeSet::new();
    consts_of(lhs, &mut cs);
    consts_of(rhs, &mut cs);
    cs.insert("Eq.refl");
    cs.insert(ty);
    let cs: Vec<&str> = cs.into_iter().collect();
    let mut e = tc.export(&cs, false)?;
    let t = e.c(ty);
    let l = term(&mut e, lhs);
    let r = term(&mut e, rhs);
    let ty = eq(&mut e, t, l, r);
    let pf = refl(&mut e, t, l);
    e.add_thm("K.claim", ty, pf, &[]);
    Ok(e)
}

fn drop_sorry(e: &mut Export) {
    e.remove_decl("sorryAx");
}

/// Export `thm` and replace its proof by `Eq.refl` (making the statement
/// hold only if both sides are definitionally equal).
fn with_rfl(tc: &mut Toolchain, thm: &str, consts: &[&str]) -> Result<Export> {
    let mut all = vec![thm];
    all.extend_from_slice(consts);
    let mut e = tc.export(&all, false)?;
    let ty = e.decl_id(thm, "type");
    let v = e.rfl_proof(ty);
    e.set(thm, "value", json!(v));
    drop_sorry(&mut e);
    Ok(e)
}

fn as_is(tc: &mut Toolchain, thm: &str) -> Result<Export> {
    tc.export(&[thm], false)
}

fn ind_record<'a>(e: &'a mut Export, name: &str) -> &'a mut Value {
    let i = e.decl_index(name).expect("declared");
    &mut e.recs[i]["inductive"]
}

fn make_safe(e: &mut Export, name: &str) {
    let ind = ind_record(e, name);
    for part in ["types", "ctors", "recs"] {
        for x in ind[part].as_array_mut().unwrap() {
            x["isUnsafe"] = json!(false);
        }
    }
}

/// Remove de Bruijn index `cut` (at depth 0) from `x`, shifting the ones above it.
fn lower(e: &mut Export, x: Id, cut: u64) -> Id {
    let mut fe = |e: &mut Export, i: Id, k: &str, p: &Value, d: u64| {
        if k == "bvar" {
            let p = p.as_u64().unwrap();
            if p == cut + d {
                panic!("removed binder is still used");
            }
            if p > cut + d {
                return Some(e.bvar(p - 1));
            }
            return Some(i);
        }
        None
    };
    e.rebuild(x, Some(&mut fe), None)
}

fn drop_binder(e: &mut Export, ty: Id, k: usize) -> Id {
    let (bs, body) = e.binders(ty, "forallE");
    let mut out: Vec<Binder> = bs[..k].to_vec();
    for (j, (n, t, bi)) in bs.iter().enumerate().skip(k + 1) {
        let t = lower(e, *t, (j - k - 1) as u64);
        out.push((*n, t, bi.clone()));
    }
    let body = lower(e, body, (bs.len() - k - 1) as u64);
    e.close(&out, body, "forallE")
}

fn replace_sort0(e: &mut Export, x: Id, lvl: Id) -> Id {
    let mut fe = |e: &mut Export, _: Id, k: &str, p: &Value, _: u64| {
        (k == "sort" && p.as_u64() == Some(0)).then(|| e.sort(lvl))
    };
    e.rebuild(x, Some(&mut fe), None)
}

/// The meta line and the records of an export's text.
fn records(text: &str) -> (String, Vec<Value>) {
    let mut lines = text.trim_end_matches('\n').split('\n');
    let meta = lines.next().unwrap().to_string();
    (
        meta,
        lines.map(|l| serde_json::from_str(l).unwrap()).collect(),
    )
}

fn join(meta: &str, recs: &[Value]) -> String {
    let mut out = meta.to_string();
    for r in recs {
        out.push('\n');
        out.push_str(&dumps(r));
    }
    out + "\n"
}

fn last_decl(recs: &[Value], kind: &str) -> usize {
    recs.iter()
        .rposition(|r| r.get(kind).is_some())
        .unwrap_or_else(|| panic!("no {kind} record"))
}

/// Base for malformed-export cases: `theorem K.triv : True := True.intro`.
fn triv(tc: &mut Toolchain) -> Result<(String, Vec<Value>)> {
    Ok(records(&tc.export(&["K.triv"], false)?.text()))
}

// ---------------------------------------------------------------------------
// Nat literal extension: wrong answers must be rejected, edge answers accepted

fn nat(
    v: &mut Cases,
    id: &'static str,
    rule: &'static str,
    expected: &'static str,
    lhs: Tm,
    rhs: Tm,
    why: &'static str,
) {
    nat_ty(v, id, rule, expected, lhs, rhs, why, "Nat");
}

#[allow(clippy::too_many_arguments)]
fn nat_ty(
    v: &mut Cases,
    id: &'static str,
    rule: &'static str,
    expected: &'static str,
    lhs: Tm,
    rhs: Tm,
    why: &'static str,
    ty: &'static str,
) {
    v.add(id, rule, expected, why, move |tc| claim(tc, &lhs, &rhs, ty));
}

fn a2(f: &'static str, x: Tm, y: Tm) -> Tm {
    A(f, vec![x, y])
}

fn nat_cases(v: &mut Cases) {
    let tt = C("Bool.true");
    let b = "Bool";
    nat(
        v,
        "nat-add-wrap64",
        "nat.add",
        "reject",
        a2("Nat.add", n(P64 - 1), n(1)),
        n(0),
        "2^64-1 + 1 claimed 0: a kernel using machine words wraps around",
    );
    nat(
        v,
        "nat-add-carry64",
        "nat.add",
        "accept",
        a2("Nat.add", n(P64 - 1), n(1)),
        n(P64),
        "carry past 2^64 must give 2^64",
    );
    nat(
        v,
        "nat-add-zero-ctor",
        "nat.add",
        "accept",
        a2("Nat.add", C("Nat.zero"), n(0)),
        n(0),
        "Nat.zero counts as the literal 0 for the extension",
    );
    nat(
        v,
        "nat-sub-wrap",
        "nat.sub",
        "reject",
        a2("Nat.sub", n(0), n(1)),
        n(P64 - 1),
        "0 - 1 claimed 2^64-1: Nat subtraction truncates, it does not wrap",
    );
    nat(
        v,
        "nat-sub-trunc",
        "nat.sub",
        "accept",
        a2("Nat.sub", n(3), n(5)),
        n(0),
        "truncated subtraction gives 0",
    );
    nat(
        v,
        "nat-sub-big",
        "nat.sub",
        "accept",
        a2("Nat.sub", n(P64), n(P64 - 1)),
        n(1),
        "borrow across the 2^64 boundary",
    );
    nat(
        v,
        "nat-sub-succ-arg",
        "nat.sub",
        "accept",
        a2("Nat.sub", A("Nat.succ", vec![n(5)]), n(3)),
        n(3),
        "Nat.succ of a literal is reduced to a literal before the extension fires",
    );
    nat(
        v,
        "nat-mul-wrap64",
        "nat.mul",
        "reject",
        a2("Nat.mul", n(U32), n(U32)),
        n(0),
        "2^32 * 2^32 claimed 0 (64-bit overflow)",
    );
    nat(
        v,
        "nat-mul-big",
        "nat.mul",
        "accept",
        a2("Nat.mul", n(P64), n(P64)),
        Tm::N(P128.into()),
        "2^64 * 2^64 = 2^128",
    );
    nat(
        v,
        "nat-div-zero",
        "nat.div",
        "accept",
        a2("Nat.div", n(7), n(0)),
        n(0),
        "x / 0 = 0",
    );
    nat(
        v,
        "nat-div-zero-wrong",
        "nat.div",
        "reject",
        a2("Nat.div", n(7), n(0)),
        n(7),
        "x / 0 claimed x",
    );
    nat(
        v,
        "nat-div-big-wrong",
        "nat.div",
        "reject",
        a2("Nat.div", Tm::N(P128.into()), n(P64)),
        n(P64 + 1),
        "2^128 / 2^64 claimed 2^64+1",
    );
    nat(
        v,
        "nat-div-big",
        "nat.div",
        "accept",
        a2("Nat.div", n(u128::MAX), n(P64)),
        n(P64 - 1),
        "floor division of big literals",
    );
    nat(
        v,
        "nat-mod-zero",
        "nat.mod",
        "accept",
        a2("Nat.mod", n(7), n(0)),
        n(7),
        "x % 0 = x",
    );
    nat(
        v,
        "nat-mod-zero-wrong",
        "nat.mod",
        "reject",
        a2("Nat.mod", n(7), n(0)),
        n(0),
        "x % 0 claimed 0",
    );
    nat(
        v,
        "nat-mod-big-wrong",
        "nat.mod",
        "reject",
        a2("Nat.mod", n(P64 + 5), n(P64)),
        n(0),
        "(2^64+5) % 2^64 claimed 0 (low-word truncation)",
    );
    nat(
        v,
        "nat-gcd-zero",
        "nat.gcd",
        "accept",
        a2("Nat.gcd", n(0), n(0)),
        n(0),
        "gcd 0 0 = 0",
    );
    nat(
        v,
        "nat-gcd-zero-wrong",
        "nat.gcd",
        "reject",
        a2("Nat.gcd", n(0), n(0)),
        n(1),
        "gcd 0 0 claimed 1",
    );
    nat(
        v,
        "nat-gcd-big",
        "nat.gcd",
        "accept",
        a2("Nat.gcd", n(P64), n((1 << 96) * 3)),
        n(P64),
        "gcd of big literals",
    );
    nat(
        v,
        "nat-gcd-big-wrong",
        "nat.gcd",
        "reject",
        a2("Nat.gcd", n(P64), n((1 << 96) * 3)),
        n(3 * P64),
        "gcd of big literals claimed too large",
    );
    nat_ty(
        v,
        "nat-beq-trunc",
        "nat.beq",
        "reject",
        a2("Nat.beq", n(P64), n(0)),
        tt.clone(),
        "beq 2^64 0 claimed true (comparing only the low 64 bits)",
        b,
    );
    nat_ty(
        v,
        "nat-beq-big",
        "nat.beq",
        "accept",
        a2("Nat.beq", n(P64 + 1), n(P64 + 1)),
        tt.clone(),
        "beq of equal big literals",
        b,
    );
    nat_ty(
        v,
        "nat-beq-false-wrong",
        "nat.beq",
        "reject",
        a2("Nat.beq", n(1), n(2)),
        tt.clone(),
        "beq 1 2 claimed true",
        b,
    );
    nat_ty(
        v,
        "nat-ble-trunc",
        "nat.ble",
        "reject",
        a2("Nat.ble", n(P64), n(1)),
        tt.clone(),
        "ble 2^64 1 claimed true",
        b,
    );
    nat_ty(
        v,
        "nat-ble-big",
        "nat.ble",
        "accept",
        a2("Nat.ble", n(P64), n(P64 + 1)),
        tt.clone(),
        "ble of big literals",
        b,
    );
    nat_ty(
        v,
        "nat-ble-eq",
        "nat.ble",
        "accept",
        a2("Nat.ble", n(0), n(0)),
        tt.clone(),
        "ble 0 0 = true",
        b,
    );
    nat(
        v,
        "nat-land-wrong",
        "nat.land",
        "reject",
        a2("Nat.land", n(P64 + 1), n(1)),
        n(0),
        "land (2^64+1) 1 claimed 0",
    );
    nat(
        v,
        "nat-land-big",
        "nat.land",
        "accept",
        a2("Nat.land", n(P64 + 1), n(P64 + 3)),
        n(P64 + 1),
        "land above 2^64",
    );
    nat(
        v,
        "nat-lor-wrong",
        "nat.lor",
        "reject",
        a2("Nat.lor", n(1), n(2)),
        n(4),
        "lor 1 2 claimed 4",
    );
    nat(
        v,
        "nat-lor-big",
        "nat.lor",
        "accept",
        a2("Nat.lor", n(P64), n(1)),
        n(P64 + 1),
        "lor above 2^64",
    );
    nat(
        v,
        "nat-xor-wrong",
        "nat.xor",
        "reject",
        a2("Nat.xor", n(5), n(5)),
        n(10),
        "xor 5 5 claimed 10",
    );
    nat(
        v,
        "nat-xor-big",
        "nat.xor",
        "accept",
        a2("Nat.xor", n(P64 + 7), n(P64)),
        n(7),
        "xor cancels the high bit",
    );
    nat(
        v,
        "nat-shl-wrap",
        "nat.shiftLeft",
        "reject",
        a2("Nat.shiftLeft", n(1), n(64)),
        n(0),
        "1 <<< 64 claimed 0 (64-bit shift)",
    );
    nat(
        v,
        "nat-shl-big",
        "nat.shiftLeft",
        "accept",
        a2("Nat.shiftLeft", n(1), n(64)),
        n(P64),
        "1 <<< 64 = 2^64",
    );
    nat(
        v,
        "nat-shr-wrong",
        "nat.shiftRight",
        "reject",
        a2("Nat.shiftRight", n(P64), n(64)),
        n(0),
        "2^64 >>> 64 claimed 0",
    );
    nat(
        v,
        "nat-shr-big",
        "nat.shiftRight",
        "accept",
        a2("Nat.shiftRight", n(P64), n(64)),
        n(1),
        "2^64 >>> 64 = 1",
    );
    nat(
        v,
        "nat-shr-huge-shift",
        "nat.shiftRight",
        "accept",
        a2("Nat.shiftRight", n(1), n(P64)),
        n(0),
        "a shift amount of 2^64 bits is still fine for >>>",
    );
    nat(
        v,
        "nat-pow-wrap",
        "nat.pow",
        "reject",
        a2("Nat.pow", n(2), n(64)),
        n(0),
        "2^64 claimed 0",
    );
    nat(
        v,
        "nat-pow-big",
        "nat.pow",
        "accept",
        a2("Nat.pow", n(2), n(64)),
        n(P64),
        "2^64",
    );
    nat(
        v,
        "nat-pow-zero-zero",
        "nat.pow",
        "accept",
        a2("Nat.pow", n(0), n(0)),
        n(1),
        "0^0 = 1",
    );
    nat(
        v,
        "nat-pow-zero-zero-wrong",
        "nat.pow",
        "reject",
        a2("Nat.pow", n(0), n(0)),
        n(0),
        "0^0 claimed 0",
    );
    let p224 = |e: u128| a2("Nat.mod", a2("Nat.pow", n(2), n(e)), n(7));
    nat(
        v,
        "nat-pow-2-24",
        "nat.pow",
        "accept",
        p224(1 << 24),
        n(2),
        "2^(2^24) (a 2 MB literal) mod 7 = 2; the exponent is at Lean's limit",
    );
    nat(
        v,
        "nat-pow-2-24-wrong",
        "nat.pow",
        "reject",
        p224(1 << 24),
        n(4),
        "2^(2^24) mod 7 claimed 4",
    );
    nat(
        v,
        "nat-pow-2-24-plus1",
        "nat.size-limit",
        "either",
        p224((1 << 24) + 1),
        n(4),
        "true claim just past Lean's Nat.pow limit; Lean refuses, a kernel may compute it",
    );
    nat(
        v,
        "nat-pow-2-24-plus1-wrong",
        "nat.size-limit",
        "reject",
        p224((1 << 24) + 1),
        n(2),
        "false claim just past the Nat.pow limit: refusing or computing both reject",
    );
    nat(
        v,
        "nat-pow-exp-u32",
        "nat.size-limit",
        "either",
        a2("Nat.pow", n(1), n(U32)),
        n(1),
        "1^(2^32) = 1; Lean refuses exponents that do not fit in 32 bits",
    );
    nat(
        v,
        "nat-pow-exp-u32-wrong",
        "nat.size-limit",
        "reject",
        a2("Nat.pow", n(1), n(U32)),
        n(0),
        "1^(2^32) claimed 0",
    );
    nat_ty(
        v,
        "nat-pow-result-limit-wrong",
        "nat.size-limit",
        "reject",
        a2("Nat.ble", a2("Nat.pow", n(2), n(1 << 31)), n(0)),
        tt.clone(),
        "2^(2^31) (256 MB) claimed <= 0; must not be accepted whatever the size policy",
        b,
    );
    let shl = || {
        a2(
            "Nat.shiftRight",
            a2("Nat.shiftLeft", n(1), n(1 << 31)),
            n(1 << 31),
        )
    };
    nat(
        v,
        "nat-shl-limit",
        "nat.size-limit",
        "either",
        shl(),
        n(1),
        "(1 <<< 2^31) >>> 2^31 = 1 builds a 256 MB literal; Lean refuses it",
    );
    nat(
        v,
        "nat-shl-limit-wrong",
        "nat.size-limit",
        "reject",
        shl(),
        n(0),
        "the same claimed 0",
    );
    nat(
        v,
        "nat-shl-zero-u32",
        "nat.size-limit",
        "either",
        a2("Nat.shiftLeft", n(0), n(U32)),
        n(0),
        "0 <<< 2^32 = 0: the shift amount does not fit in 32 bits, the result is tiny",
    );
    nat(
        v,
        "nat-log2-small",
        "nat.log2",
        "accept",
        A("Nat.log2", vec![n(8)]),
        n(3),
        "Nat.log2 is not a kernel extension: it must be unfolded",
    );
    nat(
        v,
        "nat-log2-wrong",
        "nat.log2",
        "reject",
        A("Nat.log2", vec![n(8)]),
        n(4),
        "log2 8 claimed 4",
    );
    nat(
        v,
        "nat-log2-zero",
        "nat.log2",
        "accept",
        A("Nat.log2", vec![n(0)]),
        n(0),
        "log2 0 = 0",
    );
    nat(
        v,
        "nat-succ-big",
        "nat.lit",
        "accept",
        A("Nat.succ", vec![n(P64 - 1)]),
        n(P64),
        "Nat.succ of a literal at the 2^64 boundary",
    );
    nat(
        v,
        "nat-succ-wrong",
        "nat.lit",
        "reject",
        A("Nat.succ", vec![A("Nat.succ", vec![n(0)])]),
        n(3),
        "succ (succ 0) claimed 3",
    );
    nat(
        v,
        "nat-zero-lit",
        "nat.lit",
        "accept",
        C("Nat.zero"),
        n(0),
        "Nat.zero is defeq to literal 0",
    );
    nat(
        v,
        "nat-big-lit-neq",
        "nat.lit",
        "reject",
        n(P64),
        n(0),
        "2^64 claimed equal to 0 (a literal truncated to 64 bits)",
    );

    v.text(
        "nat-lit-negative",
        "nat.lit",
        "reject",
        "natVal \"-1\" is not a natural number",
        |tc| {
            let mut e = claim(tc, &n(0), &n(0), "Nat")?;
            Ok(e.text().replace("\"natVal\":\"0\"", "\"natVal\":\"-1\""))
        },
    );
}

// ---------------------------------------------------------------------------
// String literals

const STR_CONSTS: [&str; 5] = [
    "String.ofList",
    "Char.ofNat",
    "List.cons",
    "List.nil",
    "Eq.refl",
];

fn str_claim(tc: &mut Toolchain, s: &str, cps: &[u32], other: Option<&str>) -> Result<Export> {
    let mut e = tc.export(&STR_CONSTS, false)?;
    let t = e.c("String");
    let ch = e.c("Char");
    let nil = e.konst("List.nil", &[0]);
    let mut lst = e.app(nil, &[ch]);
    for c in cps.iter().rev() {
        let cons = e.konst("List.cons", &[0]);
        let of = e.c("Char.ofNat");
        let lit = e.nat(&c.to_string());
        let x = e.app(of, &[lit]);
        lst = e.app(cons, &[ch, x, lst]);
    }
    let rhs = match other {
        Some(o) => e.str_(o),
        None => {
            let f = e.c("String.ofList");
            e.app(f, &[lst])
        }
    };
    let lhs = e.str_(s);
    let ty = eq(&mut e, t, lhs, rhs);
    let pf = refl(&mut e, t, lhs);
    e.add_thm("K.claim", ty, pf, &[]);
    Ok(e)
}

fn str_case(
    v: &mut Cases,
    id: &'static str,
    expected: &'static str,
    s: &'static str,
    cps: &'static [u32],
    why: &'static str,
    other: Option<&'static str>,
) {
    v.add(id, "string.lit", expected, why, move |tc| {
        str_claim(tc, s, cps, other)
    });
}

fn string_cases(v: &mut Cases) {
    str_case(
        v,
        "str-empty",
        "accept",
        "",
        &[],
        "\"\" unfolds to String.ofList []",
        None,
    );
    str_case(
        v,
        "str-ab",
        "accept",
        "ab",
        &[97, 98],
        "\"ab\" unfolds to String.ofList ['a','b']",
        None,
    );
    str_case(
        v,
        "str-ab-swapped",
        "reject",
        "ab",
        &[98, 97],
        "\"ab\" claimed to be ['b','a']",
        None,
    );
    str_case(
        v,
        "str-ab-short",
        "reject",
        "ab",
        &[97],
        "\"ab\" claimed to be ['a']",
        None,
    );
    str_case(
        v,
        "str-2byte",
        "accept",
        "é",
        &[233],
        "a 2-byte UTF-8 char is one Char (U+00E9)",
        None,
    );
    str_case(
        v,
        "str-2byte-as-bytes",
        "reject",
        "é",
        &[0xC3, 0xA9],
        "a 2-byte char claimed to be its UTF-8 bytes",
        None,
    );
    str_case(
        v,
        "str-4byte",
        "accept",
        "\u{1F600}",
        &[0x1F600],
        "a 4-byte char is one Char",
        None,
    );
    str_case(
        v,
        "str-4byte-as-utf16",
        "reject",
        "\u{1F600}",
        &[0xD83D, 0xDE00],
        "a 4-byte char claimed to be its UTF-16 surrogate pair",
        None,
    );
    str_case(
        v,
        "str-nul",
        "accept",
        "a\u{0}b",
        &[97, 0, 98],
        "an embedded NUL is an ordinary char",
        None,
    );
    str_case(
        v,
        "str-nul-truncated",
        "reject",
        "a\u{0}b",
        &[97],
        "\"a\\0b\" claimed to be \"a\" (C-string truncation)",
        None,
    );
    str_case(
        v,
        "str-lit-neq",
        "reject",
        "a",
        &[],
        "two different literals are not defeq",
        Some("b"),
    );
    str_case(
        v,
        "str-invalid-char",
        "accept",
        "\u{0}",
        &[0xD800],
        "Char.ofNat of a surrogate is '\\0', so String.ofList [Char.ofNat 0xD800] is \"\\0\"",
        None,
    );
}

// ---------------------------------------------------------------------------
// Positivity (built as `unsafe` in Lean so the recursors exist, then made safe)

fn positivity_cases(v: &mut Cases) {
    let pos = |v: &mut Cases, id: &'static str, typ: &'static str, why: &'static str| {
        v.add(id, "inductive.positivity", "reject", why, move |tc| {
            let mut e = tc.export(&[typ], true)?;
            make_safe(&mut e, typ);
            Ok(e)
        });
    };
    pos(
        v,
        "pos-direct",
        "K.Neg",
        "Neg.mk : (Neg → Nat) → Neg (control)",
    );
    pos(
        v,
        "pos-nonstrict",
        "K.NonStrict",
        "((T → Nat) → Nat) → T is positive but not strictly",
    );
    pos(
        v,
        "pos-nested-list",
        "K.NegNested",
        "negative occurrence inside a nested List argument",
    );
    pos(
        v,
        "pos-nested-wrap",
        "K.NegWrap",
        "nested through Wrap, whose parameter is used negatively in Wrap's field",
    );
    pos(
        v,
        "pos-mutual",
        "K.NegA",
        "negative occurrence of the other type of a mutual block",
    );
    pos(
        v,
        "pos-mutual-nested",
        "K.NegNA",
        "mutual block, nested through List, negative in the other type",
    );
    v.add(
        "pos-nested-ok",
        "inductive.positivity",
        "accept",
        "List (Nat → T) → T is fine",
        |tc| as_is(tc, "K.PosNested"),
    );
    v.add(
        "pos-mutual-nested-ok",
        "inductive.positivity",
        "accept",
        "mutual + nested, strictly positive",
        |tc| as_is(tc, "K.PosA"),
    );
}

// ---------------------------------------------------------------------------
// Mutual blocks

fn rename_level(e: &mut Export, l: Id, u: Id, v: Id) -> Id {
    if l == 0 {
        return l;
    }
    let (k, p) = e.levels[&l].clone();
    if l == u {
        return v;
    }
    match k.as_str() {
        "succ" => {
            let x: Id = serde_json::from_str(&p).unwrap();
            let x = rename_level(e, x, u, v);
            e.lsucc(x)
        }
        "max" | "imax" => {
            let [a, b]: [Id; 2] = serde_json::from_str(&p).unwrap();
            let a = rename_level(e, a, u, v);
            let b = rename_level(e, b, u, v);
            if k == "max" {
                e.lmax(a, b)
            } else {
                e.limax(a, b)
            }
        }
        _ => l,
    }
}

fn mutual_cases(v: &mut Cases) {
    v.add(
        "mutual-param-type",
        "inductive.mutual",
        "reject",
        "MB's parameter is (α : Prop) while MA's is (α : Type)",
        |tc| {
            let mut e = tc.export(&["K.MA"], false)?;
            let ty = e.decl_id("K.MB", "type");
            let (bs, body) = e.binders(ty, "forallE");
            let (n, _, bi) = bs[0].clone();
            let s = e.sort(0);
            let t = e.close(&[(n, s, bi)], body, "forallE");
            e.set("K.MB", "type", json!(t));
            Ok(e)
        },
    );
    v.add(
        "mutual-levelparam-name",
        "inductive.mutual",
        "reject",
        "MV is declared over universe v, MU over u",
        |tc| {
            let mut e = tc.export(&["K.MU"], false)?;
            let u = e.lparam("u");
            let w = e.lparam("v");
            let nv = e.name("v");
            e.set("K.MV", "levelParams", json!([nv]));
            let ty = e.decl_id("K.MV", "type");
            let t = e.map_levels(ty, &mut |e, l| rename_level(e, l, u, w));
            e.set("K.MV", "type", json!(t));
            Ok(e)
        },
    );
    v.add(
        "mutual-levelparam-extra",
        "inductive.mutual",
        "reject",
        "MV lists level params [u, v], MU lists [u]",
        |tc| {
            let mut e = tc.export(&["K.MU"], false)?;
            let mut lps = e.decl("K.MV")["levelParams"].as_array().unwrap().clone();
            let nv = e.name("v");
            lps.push(json!(nv));
            e.set("K.MV", "levelParams", Value::Array(lps));
            Ok(e)
        },
    );
    v.add(
        "mutual-result-universe",
        "inductive.mutual",
        "reject",
        "MA : Type → Type but MB : Type → Type 1",
        |tc| {
            let mut e = tc.export(&["K.MA"], false)?;
            let ty = e.decl_id("K.MB", "type");
            let (bs, _) = e.binders(ty, "forallE");
            let l = e.lnum(2);
            let s = e.sort(l);
            let t = e.close(&bs, s, "forallE");
            e.set("K.MB", "type", json!(t));
            Ok(e)
        },
    );
    v.add(
        "mutual-numparams",
        "inductive.mutual",
        "reject",
        "MB's record says numParams 0, MA's says 1",
        |tc| {
            let mut e = tc.export(&["K.MA"], false)?;
            e.set("K.MB", "numParams", json!(0));
            Ok(e)
        },
    );
    v.add(
        "mutual-all",
        "inductive.mutual",
        "reject",
        "MB's `all` omits MA",
        |tc| {
            let mut e = tc.export(&["K.MA"], false)?;
            let n = e.name("K.MB");
            e.set("K.MB", "all", json!([n]));
            Ok(e)
        },
    );
}

// ---------------------------------------------------------------------------
// Structure eta and unit-like eta

fn proj_def(tc: &mut Toolchain, idx: u64, ret: &str) -> Result<Export> {
    let mut e = tc.export(&["K.S.eta"], false)?;
    let s = e.c("K.S");
    let r = e.c(ret);
    let ty = e.pi("s", s, r);
    let b = e.bvar(0);
    let p = e.proj("K.S", idx, b);
    let val = e.lam("s", s, p);
    e.add_def("K.p", ty, val, &[], "safe");
    Ok(e)
}

fn eta_cases(v: &mut Cases) {
    v.add(
        "eta-unit",
        "eta.unit",
        "accept",
        "any two values of a fieldless structure are defeq",
        |tc| as_is(tc, "K.U.uniq"),
    );
    v.add(
        "eta-unit-param",
        "eta.unit",
        "accept",
        "unit-like eta with a parameter",
        |tc| as_is(tc, "K.UP.uniq"),
    );
    v.add(
        "eta-unit-indexed",
        "eta.unit",
        "reject",
        "W : Nat → Type has one fieldless ctor but an index: not unit-like",
        |tc| with_rfl(tc, "K.W.uniq", &[]),
    );
    v.add(
        "eta-struct",
        "eta.struct",
        "accept",
        "p = (p.1, p.2) by eta for Prod",
        |tc| as_is(tc, "K.prod_eta"),
    );
    v.add(
        "eta-struct-S",
        "eta.struct",
        "accept",
        "s = ⟨s.x, s.y⟩ by eta",
        |tc| as_is(tc, "K.S.eta"),
    );
    v.add(
        "eta-recursive",
        "eta.struct",
        "reject",
        "R has one ctor but is recursive: x = R.mk (R.get x) is not defeq",
        |tc| with_rfl(tc, "K.R.eta", &[]),
    );
    v.add(
        "eta-recursive-isrec-lie",
        "eta.struct",
        "reject",
        "as eta-recursive, with R's record claiming isRec false",
        |tc| {
            let mut e = with_rfl(tc, "K.R.eta", &[])?;
            e.set("K.R", "isRec", json!(false));
            Ok(e)
        },
    );
    v.add(
        "eta-indexed",
        "eta.struct",
        "reject",
        "V : Nat → Type has one ctor but an index: no eta",
        |tc| with_rfl(tc, "K.V.eta", &[]),
    );
    v.add(
        "proj-recursive",
        "eta.proj",
        "accept",
        "projection out of the recursive one-ctor type R: allowed (only eta is restricted)",
        |tc| {
            let mut e = tc.export(&["K.R.get"], false)?;
            let r = e.c("K.R");
            let b = e.bvar(0);
            let p = e.proj("K.R", 0, b);
            let val = e.lam("x", r, p);
            e.set("K.R.get", "value", json!(val));
            Ok(e)
        },
    );
    v.add(
        "proj-indexed",
        "eta.proj",
        "accept",
        "projection out of the indexed one-ctor type V: allowed (only eta is restricted)",
        |tc| {
            let mut e = tc.export(&["K.V.get"], false)?;
            let ty = e.decl_id("K.V.get", "type");
            let (bs, _) = e.binders(ty, "forallE");
            let b = e.bvar(0);
            let p = e.proj("K.V", 0, b);
            let val = e.close(&bs, p, "lam");
            e.set("K.V.get", "value", json!(val));
            Ok(e)
        },
    );
    v.add(
        "proj-ok",
        "eta.proj",
        "accept",
        "proj S 0 : Nat (control)",
        |tc| proj_def(tc, 0, "Nat"),
    );
    v.add(
        "proj-out-of-range",
        "eta.proj",
        "reject",
        "proj S 2, S has two fields",
        |tc| proj_def(tc, 2, "Nat"),
    );
    v.add(
        "proj-wrong-type",
        "eta.proj",
        "reject",
        "proj S 1 is a Bool, claimed Nat",
        |tc| proj_def(tc, 1, "Nat"),
    );
}

// ---------------------------------------------------------------------------
// Constructor and recursor records that the kernel must recompute, not trust

fn meta_cases(v: &mut Cases) {
    v.add(
        "ctor-meta-cidx",
        "inductive.meta",
        "reject",
        "Bool.true claims cidx 0",
        |tc| {
            let mut e = tc.export(&["Bool.true"], false)?;
            e.set("Bool.true", "cidx", json!(0));
            Ok(e)
        },
    );
    v.add(
        "ctor-meta-numfields",
        "inductive.meta",
        "reject",
        "True.intro claims one field",
        |tc| {
            let mut e = tc.export(&["True.intro"], false)?;
            e.set("True.intro", "numFields", json!(1));
            Ok(e)
        },
    );
    v.add(
        "rec-rule-swap",
        "inductive.rec",
        "reject",
        "Bool.rec's two rule right-hand sides swapped",
        |tc| {
            let mut e = tc.export(&["Bool.rec"], false)?;
            let r = e.decl("Bool.rec").get_mut("rules").unwrap();
            let a = r[0]["rhs"].clone();
            r[0]["rhs"] = r[1]["rhs"].clone();
            r[1]["rhs"] = a;
            Ok(e)
        },
    );
    v.add(
        "rec-k-lie",
        "inductive.rec",
        "reject",
        "Bool.rec claims K-like reduction (k = true)",
        |tc| {
            let mut e = tc.export(&["Bool.rec"], false)?;
            e.set("Bool.rec", "k", json!(true));
            Ok(e)
        },
    );
    v.add(
        "rec-k-missing",
        "inductive.rec",
        "reject",
        "Eq.rec claims k = false (it is K-like)",
        |tc| {
            let mut e = tc.export(&["Eq.rec"], false)?;
            e.set("Eq.rec", "k", json!(false));
            Ok(e)
        },
    );
}

// ---------------------------------------------------------------------------
// Universe levels: `def K.f : Sort a → Sort b := fun x => x` needs a ≡ b

/// A level expression over the parameters u, v, w.
enum Lv {
    U,
    V,
    W,
    Z,
    Succ(Box<Lv>),
    Max(Box<Lv>, Box<Lv>),
    IMax(Box<Lv>, Box<Lv>),
}

fn succ(a: Lv) -> Lv {
    Lv::Succ(Box::new(a))
}
fn max(a: Lv, b: Lv) -> Lv {
    Lv::Max(Box::new(a), Box::new(b))
}
fn imax(a: Lv, b: Lv) -> Lv {
    Lv::IMax(Box::new(a), Box::new(b))
}

/// Evaluates arguments left to right before the call, as Python does.
fn level(e: &mut Export, l: &Lv, uvw: [Id; 3]) -> Id {
    match l {
        Lv::U => uvw[0],
        Lv::V => uvw[1],
        Lv::W => uvw[2],
        Lv::Z => 0,
        Lv::Succ(a) => {
            let a = level(e, a, uvw);
            e.lsucc(a)
        }
        Lv::Max(a, b) => {
            let a = level(e, a, uvw);
            let b = level(e, b, uvw);
            e.lmax(a, b)
        }
        Lv::IMax(a, b) => {
            let a = level(e, a, uvw);
            let b = level(e, b, uvw);
            e.limax(a, b)
        }
    }
}

fn univ(v: &mut Cases, id: &'static str, expected: &'static str, a: Lv, b: Lv, why: &'static str) {
    v.add(id, "universe.level", expected, why, move |tc| {
        let meta = tc.export(&["K.triv"], false)?.meta;
        let mut e = Export::empty(&meta);
        let u = e.lparam("u");
        let vv = e.lparam("v");
        let w = e.lparam("w");
        let la = level(&mut e, &a, [u, vv, w]);
        let lb = level(&mut e, &b, [u, vv, w]);
        let sa = e.sort(la);
        let sb = e.sort(lb);
        let ty = e.pi("x", sa, sb);
        let sa = e.sort(la);
        let x = e.bvar(0);
        let val = e.lam("x", sa, x);
        e.add_def("K.f", ty, val, &["u", "v", "w"], "safe");
        Ok(e)
    });
}

fn lp_arity(tc: &mut Toolchain, f: fn(&[Value]) -> Vec<Value>) -> Result<Export> {
    let mut e = tc.export(&["K.lp", "Eq.refl"], false)?;
    let n = e.name("Eq.refl");
    let ty = e.decl_id("K.lp", "type");
    let pf = e.rfl_proof(ty);
    let mut hit = 0;
    let mut fe = |e: &mut Export, _: Id, k: &str, p: &Value, _: u64| {
        if k == "const" && p["name"] == json!(n) {
            hit += 1;
            return Some(e.expr(
                "const",
                json!({"name": n, "us": f(p["us"].as_array().unwrap())}),
            ));
        }
        None
    };
    let val = e.rebuild(pf, Some(&mut fe), None);
    assert!(hit > 0);
    e.set("K.lp", "value", json!(val));
    Ok(e)
}

/// Large elimination from Prop.
fn large_rec(tc: &mut Toolchain, ind: &str) -> Result<Export> {
    let mut e = tc.export(&[ind], false)?;
    let rec = format!("{ind}.rec");
    let u = e.lparam("u");
    let nu = e.name("u");
    let mut lps = vec![json!(nu)];
    lps.extend(
        e.decl(&rec)["levelParams"]
            .as_array()
            .unwrap()
            .iter()
            .cloned(),
    );
    e.set(&rec, "levelParams", Value::Array(lps));
    let ty = e.decl_id(&rec, "type");
    let t = replace_sort0(&mut e, ty, u);
    e.set(&rec, "type", json!(t));
    let nrules = e.decl(&rec)["rules"].as_array().unwrap().len();
    for i in 0..nrules {
        let rhs = e.decl(&rec)["rules"][i]["rhs"].as_u64().unwrap();
        let r = replace_sort0(&mut e, rhs, u);
        e.decl(&rec).get_mut("rules").unwrap()[i]["rhs"] = json!(r);
    }
    Ok(e)
}

fn universe_cases(v: &mut Cases) {
    use Lv::{U, V, W, Z};
    univ(
        v,
        "univ-imax-succ",
        "accept",
        imax(U, succ(V)),
        max(U, succ(V)),
        "imax u (v+1) = max u (v+1)",
    );
    univ(
        v,
        "univ-max-imax",
        "reject",
        max(U, V),
        imax(U, V),
        "max u v ≠ imax u v when v = 0",
    );
    univ(v, "univ-imax-self", "accept", imax(U, U), U, "imax u u = u");
    univ(v, "univ-imax-zero", "accept", imax(U, Z), Z, "imax u 0 = 0");
    univ(
        v,
        "univ-imax-one",
        "reject",
        imax(succ(Z), U),
        succ(Z),
        "imax 1 u is 0 when u = 0",
    );
    univ(
        v,
        "univ-imax-nested-trap",
        "reject",
        imax(imax(U, V), W),
        imax(max(U, V), W),
        "differs at v = 0, w = 1, u = 2: looks like a harmless imax→max rewrite",
    );
    univ(
        v,
        "univ-imax-assoc",
        "either",
        imax(U, imax(V, W)),
        imax(max(U, V), W),
        "equal for every assignment (w = 0, then w > 0); a level normaliser need not prove it",
    );
    univ(
        v,
        "univ-max-comm",
        "accept",
        max(U, V),
        max(V, U),
        "max is commutative",
    );
    univ(v, "univ-max-zero", "accept", max(Z, U), U, "max 0 u = u");
    univ(
        v,
        "univ-succ-max",
        "accept",
        succ(max(U, V)),
        max(succ(U), succ(V)),
        "succ distributes over max",
    );
    univ(
        v,
        "univ-max-absorb",
        "accept",
        max(U, max(U, V)),
        max(V, U),
        "idempotence + commutativity",
    );
    univ(v, "univ-param-swap", "reject", U, V, "distinct parameters");
    univ(v, "univ-succ-param", "reject", succ(U), U, "u+1 ≠ u");
    univ(
        v,
        "univ-imax-succ-left",
        "reject",
        imax(succ(U), V),
        succ(max(U, V)),
        "imax (u+1) v is 0 when v = 0",
    );

    v.add(
        "lparam-undeclared",
        "universe.params",
        "reject",
        "K.lp uses u but declares no level params",
        |tc| {
            let mut e = tc.export(&["K.lp"], false)?;
            e.set("K.lp", "levelParams", json!([]));
            Ok(e)
        },
    );
    v.add(
        "lparam-duplicate",
        "universe.params",
        "reject",
        "K.lp declares level params [u, u]",
        |tc| {
            let mut e = tc.export(&["K.lp"], false)?;
            let lps = e.decl("K.lp")["levelParams"].as_array().unwrap().clone();
            e.set(
                "K.lp",
                "levelParams",
                Value::Array([lps.clone(), lps].concat()),
            );
            Ok(e)
        },
    );
    v.add(
        "lparam-const-too-many",
        "universe.params",
        "reject",
        "Eq.refl.{u, u} (one param expected)",
        |tc| lp_arity(tc, |us| [us, us].concat()),
    );
    v.add(
        "lparam-const-too-few",
        "universe.params",
        "reject",
        "Eq.refl with no universe argument",
        |tc| lp_arity(tc, |_| Vec::new()),
    );

    v.add(
        "elim-prop-two-ctors",
        "universe.elim",
        "reject",
        "P2 : Prop with two ctors, recursor claims a motive in Sort u",
        |tc| large_rec(tc, "K.P2"),
    );
    v.add(
        "elim-prop-data-field",
        "universe.elim",
        "reject",
        "Ex : Prop with a Nat field, recursor claims a motive in Sort u",
        |tc| large_rec(tc, "K.Ex"),
    );
    v.add(
        "elim-prop-use",
        "universe.elim",
        "reject",
        "P2.rec (motive into Prop) applied to a motive into Type",
        |tc| {
            let mut e = tc.export(&["K.P2", "Bool.true", "Bool.false"], false)?;
            let p = e.c("K.P2");
            let bt = e.c("Bool");
            let motive = e.lam("p", p, bt);
            let rec = e.c("K.P2.rec");
            let t = e.c("Bool.true");
            let f = e.c("Bool.false");
            let x = e.bvar(0);
            let body = e.app(rec, &[motive, t, f, x]);
            let ty = e.pi("p", p, bt);
            let val = e.lam("p", p, body);
            e.add_def("K.toBool", ty, val, &[], "safe");
            Ok(e)
        },
    );
    v.add(
        "elim-false-large",
        "universe.elim",
        "accept",
        "False eliminates into any universe (empty Prop)",
        |tc| as_is(tc, "False.elim"),
    );
}

// ---------------------------------------------------------------------------
// Quotients

const QUOT: [&str; 4] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];

fn quot_cases(v: &mut Cases) {
    v.add(
        "quot-lift-mk-q",
        "quot.reduce",
        "accept",
        "Quot.lift f h (Quot.mk r a) ≡ f a",
        |tc| as_is(tc, "K.q_lift_mk_q"),
    );
    v.add(
        "quot-lift-mk-extra-arg",
        "quot.reduce",
        "accept",
        "the reduction also fires with extra arguments after the quotient",
        |tc| as_is(tc, "K.q_lift_mk_fun_q"),
    );
    v.add(
        "quot-ind-mk",
        "quot.reduce",
        "accept",
        "Quot.ind h (Quot.mk r a) ≡ h a",
        |tc| as_is(tc, "K.q_ind_mk"),
    );
    v.add(
        "quot-lift-var",
        "quot.reduce",
        "reject",
        "Quot.lift f h q ≡ f a claimed for a variable q (no Quot.mk to reduce)",
        |tc| with_rfl(tc, "K.q_lift_var", &[]),
    );
    v.add(
        "quot-mk-rel-rfl",
        "quot.reduce",
        "reject",
        "Quot.mk r a ≡ Quot.mk r b for related a b: needs Quot.sound, not defeq",
        |tc| {
            let mut e = tc.export(&["K.q_mk_rel"], false)?;
            let ty = e.decl_id("K.q_mk_rel", "type");
            let v = e.rfl_proof(ty);
            e.set("K.q_mk_rel", "value", json!(v));
            Ok(e)
        },
    );
    v.add(
        "quot-lift-mk-wrong",
        "quot.reduce",
        "reject",
        "Quot.lift f h (Quot.mk r a) claimed ≡ f (a+1)",
        |tc| {
            let mut e = tc.export(&["K.q_lift_mk_q", "Nat.succ"], false)?;
            let d = "K.q_lift_mk_q";
            let ty = e.decl_id(d, "type");
            let (bs, body) = e.binders(ty, "forallE");
            let (f, args) = e.app_args(body);
            let (t, a, b) = (args[0], args[1], args[2]);
            let (ff, fargs) = e.app_args(b);
            assert_eq!(fargs.len(), 1);
            let s = e.c("Nat.succ");
            let sa = e.app(s, &[fargs[0]]);
            let b2 = e.app(ff, &[sa]);
            let body = e.app(f, &[t, a, b2]);
            let ty = e.close(&bs, body, "forallE");
            e.set(d, "type", json!(ty));
            let v = e.rfl_proof(ty);
            e.set(d, "value", json!(v));
            Ok(e)
        },
    );
    v.add(
        "quot-lift-no-respect",
        "quot.typing",
        "reject",
        "Quot.lift declared without the respect hypothesis (lifts any function)",
        |tc| {
            let mut e = tc.export(&["Quot.lift"], false)?;
            let ty = e.decl_id("Quot.lift", "type");
            let t = drop_binder(&mut e, ty, 4);
            e.set("Quot.lift", "type", json!(t));
            Ok(e)
        },
    );
    v.add(
        "quot-ind-large",
        "quot.typing",
        "reject",
        "Quot.ind's motive is Quot r → Sort u",
        |tc| {
            let mut e = tc.export(&["Quot.ind"], false)?;
            let ty = e.decl_id("Quot.ind", "type");
            let (mut bs, body) = e.binders(ty, "forallE");
            let (n, t, bi) = bs[2].clone();
            let u = e.lparam("u");
            let t = replace_sort0(&mut e, t, u);
            bs[2] = (n, t, bi);
            let ty = e.close(&bs, body, "forallE");
            e.set("Quot.ind", "type", json!(ty));
            Ok(e)
        },
    );
    v.add(
        "quot-mk-type",
        "quot.typing",
        "reject",
        "Quot.mk : {α} → (r) → α → α",
        |tc| {
            let mut e = tc.export(&["Quot.mk"], false)?;
            let ty = e.decl_id("Quot.mk", "type");
            let (bs, _) = e.binders(ty, "forallE");
            let b = e.bvar(2);
            let t = e.close(&bs, b, "forallE");
            e.set("Quot.mk", "type", json!(t));
            Ok(e)
        },
    );
    v.add(
        "quot-kind-swap",
        "quot.typing",
        "reject",
        "Quot.lift's record says kind \"ind\"",
        |tc| {
            let mut e = tc.export(&["Quot.lift"], false)?;
            e.set("Quot.lift", "kind", json!("ind"));
            Ok(e)
        },
    );
    v.add(
        "quot-no-eq",
        "quot.typing",
        "reject",
        "the quotient package without Eq declared",
        |tc| {
            let mut e = tc.export(&["Quot.lift"], false)?;
            assert!(e.remove_decl("Eq"));
            Ok(e)
        },
    );
}

// ---------------------------------------------------------------------------
// Proof irrelevance

fn proj_proof(tc: &mut Toolchain, thm: &str, ty_name: &str) -> Result<Export> {
    let mut e = tc.export(&[thm], false)?;
    let ty = e.decl_id(thm, "type");
    let (bs, _) = e.binders(ty, "forallE");
    let b = e.bvar(0);
    let p = e.proj(ty_name, 0, b);
    let v = e.close(&bs, p, "lam");
    e.set(thm, "value", json!(v));
    Ok(e)
}

fn irrel_cases(v: &mut Cases) {
    v.add(
        "pi-fun",
        "proof-irrel",
        "accept",
        "two proofs of ∀ n, p n are defeq",
        |tc| as_is(tc, "K.pi_fun"),
    );
    v.add(
        "pi-imax",
        "proof-irrel",
        "accept",
        "∀ a : α, β a with α : Sort u, β : α → Prop is a Prop (imax u 0 = 0)",
        |tc| as_is(tc, "K.pi_imax"),
    );
    v.add(
        "pi-beta",
        "proof-irrel",
        "accept",
        "the proposition is only Prop after beta",
        |tc| as_is(tc, "K.pi_beta"),
    );
    v.add(
        "pi-data",
        "proof-irrel",
        "reject",
        "functions P → Nat out of a proof are not proofs",
        |tc| with_rfl(tc, "K.pi_data", &[]),
    );
    v.add(
        "pi-sort",
        "proof-irrel",
        "reject",
        "elements of α : Sort u are not proofs (u may be > 0)",
        |tc| with_rfl(tc, "K.pi_sort", &[]),
    );
    v.add(
        "pi-bool",
        "proof-irrel",
        "reject",
        "Bool values are not proofs",
        |tc| with_rfl(tc, "K.pi_bool", &[]),
    );
    v.add(
        "pi-proj-exists",
        "proof-irrel",
        "reject",
        "projecting the witness (data) out of a proof of ∃",
        |tc| proj_proof(tc, "K.ex_wit", "Exists"),
    );
    v.add(
        "pi-proj-and",
        "proof-irrel",
        "accept",
        "projecting a proof out of a proof of ∧",
        |tc| proj_proof(tc, "K.and_left", "And"),
    );
}

// ---------------------------------------------------------------------------
// Malformed exports (base: theorem K.triv : True := True.intro)

fn fmt_raw(
    v: &mut Cases,
    id: &'static str,
    why: &'static str,
    f: impl Fn(&str, &mut Vec<Value>) -> String + 'static,
) {
    v.text(id, "export.format", "reject", why, move |tc| {
        let (m, mut r) = triv(tc)?;
        Ok(f(&m, &mut r))
    });
}

fn first_ie(r: &[Value], t: &Value) -> usize {
    r.iter().position(|x| x.get("ie") == Some(t)).unwrap()
}

fn triv_edit(v: &mut Cases, id: &'static str, why: &'static str, f: fn(&mut Export)) {
    v.add(id, "export.format", "reject", why, move |tc| {
        let mut e = tc.export(&["K.triv"], false)?;
        f(&mut e);
        Ok(e)
    });
}

fn format_cases(v: &mut Cases) {
    v.text(
        "fmt-ok",
        "export.format",
        "accept",
        "the unmodified base export (control)",
        |tc| {
            let (m, r) = triv(tc)?;
            Ok(join(&m, &r))
        },
    );
    v.text(
        "fmt-meta-only",
        "export.format",
        "accept",
        "an export with no declarations",
        |tc| {
            let (m, _) = triv(tc)?;
            Ok(join(&m, &[]))
        },
    );
    fmt_raw(
        v,
        "fmt-fwd-expr",
        "the theorem's type record comes after the theorem",
        |m, r| {
            let t = r[last_decl(r, "thm")]["thm"]["type"].clone();
            let rec = r.remove(first_ie(r, &t));
            r.push(rec);
            join(m, r)
        },
    );
    fmt_raw(
        v,
        "fmt-dup-expr-id",
        "an expression id bound twice to different terms",
        |m, r| {
            let i = last_decl(r, "thm");
            let t = r[i]["thm"]["type"].clone();
            r.insert(i, json!({"ie": t, "sort": 0}));
            join(m, r)
        },
    );
    fmt_raw(
        v,
        "fmt-dup-expr-same",
        "an expression id bound twice to the same term",
        |m, r| {
            let i = last_decl(r, "thm");
            let t = r[i]["thm"]["type"].clone();
            let rec = r[first_ie(r, &t)].clone();
            r.insert(i, rec);
            join(m, r)
        },
    );
    fmt_raw(v, "fmt-dup-name-id", "a name id bound twice", |m, r| {
        let j = r.iter().position(|x| x.get("in").is_some()).unwrap();
        let n = r[j]["in"].clone();
        r.insert(j + 1, json!({"in": n, "str": {"pre": 0, "str": "Other"}}));
        join(m, r)
    });
    fmt_raw(v, "fmt-dup-level-id", "a level id bound twice", |m, r| {
        let i = last_decl(r, "thm");
        r.insert(i, json!({"il": 1, "succ": 0}));
        r.insert(i, json!({"il": 1, "succ": 0}));
        join(m, r)
    });
    fmt_raw(v, "fmt-dup-decl", "the theorem declared twice", |m, r| {
        let d = r[last_decl(r, "thm")].clone();
        r.push(d);
        join(m, r)
    });
    let drop_field = |v: &mut Cases, id, why, kind: &'static str, field: &'static str| {
        fmt_raw(v, id, why, move |m, r| {
            let i = last_decl(r, kind);
            r[i][kind].as_object_mut().unwrap().remove(field);
            join(m, r)
        });
    };
    drop_field(
        v,
        "fmt-missing-value",
        "theorem without `value`",
        "thm",
        "value",
    );
    drop_field(
        v,
        "fmt-missing-type",
        "theorem without `type`",
        "thm",
        "type",
    );
    drop_field(
        v,
        "fmt-missing-levelparams",
        "theorem without `levelParams`",
        "thm",
        "levelParams",
    );
    drop_field(
        v,
        "fmt-missing-ctors",
        "inductive without `ctors`",
        "inductive",
        "ctors",
    );
    drop_field(
        v,
        "fmt-missing-recs",
        "inductive without `recs`",
        "inductive",
        "recs",
    );
    let rename_kind = |v: &mut Cases, id, why, old: &'static str, new: &'static str, decl: bool| {
        fmt_raw(v, id, why, move |m, r| {
            let i = if decl {
                last_decl(r, old)
            } else {
                r.iter().position(|x| x.get(old).is_some()).unwrap()
            };
            let mut obj = r[i].as_object().unwrap().clone();
            let val = obj.remove(old).unwrap();
            obj.insert(new.to_string(), val);
            r[i] = Value::Object(obj);
            join(m, r)
        });
    };
    rename_kind(
        v,
        "fmt-kind-unknown",
        "a declaration record of unknown kind \"theorem\"",
        "thm",
        "theorem",
        true,
    );
    rename_kind(
        v,
        "fmt-kind-thm-as-axiom",
        "theorem fields under the \"axiom\" kind",
        "thm",
        "axiom",
        true,
    );
    rename_kind(
        v,
        "fmt-kind-thm-as-def",
        "theorem fields under the \"def\" kind",
        "thm",
        "def",
        true,
    );
    rename_kind(
        v,
        "fmt-kind-expr-unknown",
        "an expression record of unknown kind \"pi\"",
        "forallE",
        "pi",
        false,
    );

    triv_edit(
        v,
        "fmt-undeclared-const",
        "the proof refers to an undeclared constant",
        |e| {
            let c = e.c("K.nope");
            e.set("K.triv", "value", json!(c));
        },
    );
    triv_edit(
        v,
        "fmt-thm-mismatch",
        "the theorem's value True does not have type True",
        |e| {
            let c = e.c("True");
            e.set("K.triv", "value", json!(c));
        },
    );
    triv_edit(
        v,
        "fmt-thm-not-prop",
        "theorem K.triv : Prop := True (a theorem's type must be a Prop)",
        |e| {
            let s = e.sort(0);
            e.set("K.triv", "type", json!(s));
            let c = e.c("True");
            e.set("K.triv", "value", json!(c));
        },
    );
    triv_edit(
        v,
        "fmt-loose-bvar",
        "the theorem's type is a loose bound variable",
        |e| {
            let b = e.bvar(0);
            e.set("K.triv", "type", json!(b));
        },
    );
    triv_edit(
        v,
        "fmt-const-wrong-arity",
        "True.intro applied to a universe argument",
        |e| {
            let c = e.konst("True.intro", &[0]);
            e.set("K.triv", "value", json!(c));
        },
    );

    fmt_raw(
        v,
        "fmt-bad-level-ref",
        "a constant whose universe list names a missing level id",
        |m, r| {
            let val = r[last_decl(r, "thm")]["thm"]["value"].clone();
            let j = first_ie(r, &val);
            r[j]["const"]["us"] = json!([999]);
            join(m, r)
        },
    );
    fmt_raw(
        v,
        "fmt-name-bad-prefix",
        "a name whose prefix id does not exist",
        |m, r| {
            let j = r.iter().position(|x| x.get("in").is_some()).unwrap();
            r[j]["str"]["pre"] = json!(999);
            join(m, r)
        },
    );
    fmt_raw(
        v,
        "fmt-no-meta",
        "the meta header line is missing",
        |_, r| r.iter().map(dumps).collect::<Vec<_>>().join("\n") + "\n",
    );
    fmt_raw(
        v,
        "fmt-bad-json",
        "the last line is truncated JSON",
        |m, r| {
            let t = join(m, r);
            let chars: Vec<char> = t.trim_end_matches('\n').chars().collect();
            chars[..chars.len() - 5].iter().collect::<String>() + "\n"
        },
    );
    v.add(
        "fmt-opaque-mismatch",
        "export.format",
        "reject",
        "an opaque whose value does not match its type",
        |tc| {
            let mut e = tc.export(&["K.triv"], false)?;
            let all = e.name("K.o");
            let n = e.name("K.o");
            let t = e.c("True");
            let val = e.c("True");
            e.add_decl(
                "opaque",
                json!({"all": [all], "isUnsafe": false, "levelParams": [],
                "name": n, "type": t, "value": val}),
            );
            Ok(e)
        },
    );
    v.add(
        "fmt-safe-uses-unsafe",
        "export.format",
        "reject",
        "a safe theorem proved by an unsafe axiom of False",
        |tc| {
            let mut e = tc.export(&["False"], false)?;
            let f = e.c("False");
            e.add_axiom("K.bad", f, &[], true);
            let f = e.c("False");
            let bad = e.c("K.bad");
            e.add_thm("K.oops", f, bad, &[]);
            Ok(e)
        },
    );
    v.add(
        "fmt-safe-uses-partial",
        "export.format",
        "reject",
        "a safe definition that unfolds to a partial one",
        |tc| {
            let mut e = tc.export(&["K.triv"], false)?;
            let t = e.c("True");
            let i = e.c("True.intro");
            e.add_def("K.p", t, i, &[], "partial");
            let p = e.c("K.p");
            e.add_def("K.q", t, p, &[], "safe");
            Ok(e)
        },
    );
}

// ---------------------------------------------------------------------------
// Evaluation of closed terms (src/check/eval/). Each claim is proved by
// `Eq.refl`, so only reduction decides it; the `-wrong` twins must fail.

fn eval(
    v: &mut Cases,
    id: &'static str,
    thm: &'static str,
    expected: &'static str,
    why: &'static str,
    consts: &'static [&'static str],
) {
    v.add(id, "eval", expected, why, move |tc| {
        with_rfl(tc, thm, consts)
    });
}

/// A case of lean/KCases434.lean, exported from Lean v4.34.0.
fn eval_old(
    v: &mut Cases,
    id: &'static str,
    thm: &'static str,
    expected: &'static str,
    why: &'static str,
) {
    v.add(id, "eval", expected, why, move |tc| {
        with_rfl(tc.old()?, thm, &[])
    });
}

fn eval_cases(v: &mut Cases) {
    eval(
        v,
        "eval-decide",
        "K.ev_decide",
        "accept",
        "decide on a fold over List.range",
        &[],
    );
    eval(
        v,
        "eval-decide-false",
        "K.ev_decide_false",
        "reject",
        "the same decide, false",
        &[],
    );
    eval(
        v,
        "eval-k-stuck",
        "K.ev_k_stuck",
        "reject",
        "Eq.rec over an axiom of 0 = 1: K does not apply (0 ≢ 1), so the cast is stuck",
        &[],
    );
    eval(
        v,
        "eval-k-ok",
        "K.ev_k_ok",
        "accept",
        "Eq.rec over an axiom of 2 + 2 = 4: K applies (2 + 2 ≡ 4) without reducing the axiom",
        &[],
    );
    eval(
        v,
        "eval-struct-eta",
        "K.ev_struct_eta",
        "accept",
        "Prod.rec on an opaque pair reduces by structure eta to its first projection",
        &[],
    );
    eval(
        v,
        "eval-struct-eta-wrong",
        "K.ev_struct_eta_wrong",
        "reject",
        "the same, claimed to be the second projection",
        &[],
    );
    eval(
        v,
        "eval-quot",
        "K.ev_quot_ok",
        "accept",
        "Quot.lift f h (Quot.mk r (ev_sum 4)) ≡ f 6 = 7",
        &QUOT,
    );
    eval(
        v,
        "eval-quot-wrong",
        "K.ev_quot_wrong",
        "reject",
        "the same, claimed 6",
        &QUOT,
    );
    eval(
        v,
        "eval-str-len",
        "K.ev_str_len",
        "accept",
        "String.length of a literal",
        &[],
    );
    eval(
        v,
        "eval-str-len-wrong",
        "K.ev_str_len_wrong",
        "reject",
        "the same, claimed 4",
        &[],
    );
    eval(
        v,
        "eval-deep",
        "K.ev_deep_ok",
        "accept",
        "a right fold over 20000 elements: evaluation nests 20000 deep",
        &[],
    );
    eval(
        v,
        "eval-deep-wrong",
        "K.ev_deep_wrong",
        "reject",
        "the same, off by one",
        &[],
    );
    eval(
        v,
        "eval-pap",
        "K.ev_pap",
        "accept",
        "Nat.add 1 is not in weak head normal form: it unfolds (then eta)",
        &[],
    );
    eval(
        v,
        "eval-pap-wrong",
        "K.ev_pap_wrong",
        "reject",
        "Nat.add 1 ≢ fun x => Nat.add 2 x",
        &[],
    );
    eval(
        v,
        "eval-rec-lit",
        "K.ev_rec_lit",
        "accept",
        "Nat.rec on the literal 1000 (literals become Nat.succ applications)",
        &[],
    );
    eval(
        v,
        "eval-rec-lit-wrong",
        "K.ev_rec_lit_wrong",
        "reject",
        "the same, off by one",
        &[],
    );
    eval(
        v,
        "eval-big",
        "K.ev_big",
        "accept",
        "literal arithmetic past 2^64 inside decide",
        &[],
    );
    eval(
        v,
        "eval-big-wrong",
        "K.ev_big_wrong",
        "reject",
        "the same, false",
        &[],
    );
    eval(
        v,
        "eval-cast-thm",
        "K.ev_cast_thm",
        "accept",
        "cast over a theorem applied to a variable: the erased proof is a K-like major premise",
        &[],
    );
    eval(
        v,
        "eval-cast-thm-wrong",
        "K.ev_cast_thm_wrong",
        "reject",
        "the same, off by one",
        &[],
    );
    eval(
        v,
        "eval-and-rec",
        "K.ev_and_ok",
        "accept",
        "And.rec on a constructed proof: the erased proof is a major premise",
        &[],
    );
    eval(
        v,
        "eval-and-rec-wrong",
        "K.ev_and_wrong",
        "reject",
        "the same, off by one",
        &[],
    );
    eval(
        v,
        "eval-sub",
        "K.ev_sub_ok",
        "accept",
        "a weak head normal form holding a proof (a Subtype value)",
        &[],
    );
    eval(
        v,
        "eval-sub-wrong",
        "K.ev_sub_wrong",
        "reject",
        "its value, claimed 3",
        &[],
    );
    eval(
        v,
        "eval-let",
        "K.ev_let_ok",
        "accept",
        "a let-bound value used twice",
        &[],
    );
    eval(
        v,
        "eval-let-wrong",
        "K.ev_let_wrong",
        "reject",
        "the same, off by one",
        &[],
    );
    eval(
        v,
        "eval-fn",
        "K.ev_fn_ok",
        "accept",
        "a fold that builds a function (closures of closures), then applied",
        &[],
    );
    eval(
        v,
        "eval-fn-wrong",
        "K.ev_fn_wrong",
        "reject",
        "the same, off by one",
        &[],
    );
    eval(
        v,
        "eval-arr-get",
        "K.ev_arr_get",
        "accept",
        "an array built by push, read by get! and getD (in and out of range)",
        &[],
    );
    eval(
        v,
        "eval-arr-get-wrong",
        "K.ev_arr_get_wrong",
        "reject",
        "the same, wrong sum",
        &[],
    );
    eval(
        v,
        "eval-arr-set",
        "K.ev_arr_set",
        "accept",
        "set! then the array as a list",
        &[],
    );
    eval(
        v,
        "eval-arr-set-wrong",
        "K.ev_arr_set_wrong",
        "reject",
        "the same, the old element",
        &[],
    );
    eval(
        v,
        "eval-arr-oob",
        "K.ev_arr_oob",
        "accept",
        "set! and get! out of range leave the array alone and give the default",
        &[],
    );
    eval(
        v,
        "eval-arr-oob-wrong",
        "K.ev_arr_oob_wrong",
        "reject",
        "the same, off by one",
        &[],
    );
    eval(
        v,
        "eval-arr-eq",
        "K.ev_arr_eq",
        "accept",
        "decidable equality of an array built by push and one made from a list",
        &[],
    );
    eval(
        v,
        "eval-arr-eq-wrong",
        "K.ev_arr_eq_wrong",
        "reject",
        "the same, different arrays",
        &[],
    );
    eval(
        v,
        "eval-arr-fn",
        "K.ev_arr_fn",
        "accept",
        "an array of functions, elements applied",
        &[],
    );
    eval(
        v,
        "eval-arr-fn-wrong",
        "K.ev_arr_fn_wrong",
        "reject",
        "the same, wrong sum",
        &[],
    );
    eval(
        v,
        "eval-select",
        "K.ev_select",
        "accept",
        "ite, dite and decide pick a branch: a function applied further, a value, a closed term",
        &[],
    );
    eval(
        v,
        "eval-select-wrong",
        "K.ev_select_wrong",
        "reject",
        "the same, off by one",
        &[],
    );
    eval(
        v,
        "eval-arr-vers",
        "K.ev_arr_vers",
        "accept",
        "old versions of an array read after set! and push on them",
        &[],
    );
    eval(
        v,
        "eval-arr-vers-wrong",
        "K.ev_arr_vers_wrong",
        "reject",
        "the same, off by one",
        &[],
    );
    eval(
        v,
        "eval-arr-hist",
        "K.ev_arr_hist_ok",
        "accept",
        "twenty versions of an array, each made from the last, all read",
        &[],
    );
    eval(
        v,
        "eval-arr-hist-wrong",
        "K.ev_arr_hist_wrong",
        "reject",
        "the same, off by one",
        &[],
    );
    eval(
        v,
        "eval-list",
        "K.ev_lists",
        "accept",
        "List.any, all, filter, getLast?, foldl, reverse, elem and eraseDups on numbers",
        &[],
    );
    eval(
        v,
        "eval-list-wrong",
        "K.ev_lists_wrong",
        "reject",
        "the same fold, off by one",
        &[],
    );
    eval(
        v,
        "eval-list-filter-lazy",
        "K.ev_filter_lazy",
        "accept",
        "the head of a filter, whose later tests would divide by zero",
        &[],
    );
    eval(
        v,
        "eval-list-filter-lazy-wrong",
        "K.ev_filter_lazy_wrong",
        "reject",
        "the same, the wrong head",
        &[],
    );
    eval(
        v,
        "eval-int",
        "K.ev_int",
        "accept",
        "Int +, -, *, neg, / and % (Euclidean and toward zero), ^, subNatNat, negOfNat, natAbs and toNat on every sign, zero and big values, hashed",
        &[],
    );
    eval(
        v,
        "eval-int-wrong",
        "K.ev_int_wrong",
        "reject",
        "the same hash, off by one",
        &[],
    );
    eval(
        v,
        "eval-list-lazy",
        "K.ev_lists2",
        "accept",
        "List.map, zipWith, append and length",
        &[],
    );
    eval(
        v,
        "eval-list-lazy-wrong",
        "K.ev_lists2_wrong",
        "reject",
        "the length, off by one",
        &[],
    );
    eval(
        v,
        "eval-methods",
        "K.ev_methods_ok",
        "accept",
        "+ through 20 instances built from a number, an instance argument and a computed field",
        &[],
    );
    eval(
        v,
        "eval-methods-wrong",
        "K.ev_methods_wrong",
        "reject",
        "the same sum, off by one",
        &[],
    );
    eval(
        v,
        "eval-cases",
        "K.ev_cases_ok",
        "accept",
        "matches through casesOn and sparse casesOn: wildcards, a literal, a structure, a function result",
        &[],
    );
    eval(
        v,
        "eval-cases-wrong",
        "K.ev_cases_wrong",
        "reject",
        "the same sum, off by one",
        &[],
    );

    eval_old(
        v,
        "eval434-deceq",
        "K34.ev_deceq",
        "accept",
        "DecidableEq on lists of (subtype, Bool) pairs, equal (v4.34.0)",
    );
    eval_old(
        v,
        "eval434-deceq-wrong",
        "K34.ev_deceq_wrong",
        "reject",
        "the same, lists of different lengths",
    );
    eval_old(
        v,
        "eval434-deceq-ne",
        "K34.ev_deceq_ne",
        "accept",
        "pairs that differ in the second component",
    );
    eval_old(
        v,
        "eval434-deceq-ne-wrong",
        "K34.ev_deceq_ne_wrong",
        "reject",
        "pairs that differ in the first component, claimed equal",
    );
    eval_old(
        v,
        "eval434-beq",
        "K34.ev_beq",
        "accept",
        "== on pairs (instBEqProd) in a filter",
    );
    eval_old(
        v,
        "eval434-beq-wrong",
        "K34.ev_beq_wrong",
        "reject",
        "the same, off by one",
    );
    eval_old(
        v,
        "eval434-nodup",
        "K34.ev_nodup",
        "accept",
        "decide Nodup of distinct pairs",
    );
    eval_old(
        v,
        "eval434-nodup-wrong",
        "K34.ev_nodup_wrong",
        "reject",
        "the same with a repeated pair",
    );
    eval_old(
        v,
        "eval434-dedup",
        "K34.ev_dedup",
        "accept",
        "eraseDups on pairs",
    );
    eval_old(
        v,
        "eval434-dedup-wrong",
        "K34.ev_dedup_wrong",
        "reject",
        "the same, off by one",
    );
    eval_old(
        v,
        "eval434-elem",
        "K34.ev_elem",
        "accept",
        "List.elem on pairs, found and not",
    );
    eval_old(
        v,
        "eval434-elem-wrong",
        "K34.ev_elem_wrong",
        "reject",
        "the one not found, claimed found",
    );
    eval_old(
        v,
        "eval434-cast",
        "K34.ev_cast_ok",
        "accept",
        "a cast over a DecidableEq proof: the erased proof is a K-like major premise",
    );
    eval_old(
        v,
        "eval434-cast-wrong",
        "K34.ev_cast_wrong",
        "reject",
        "the same, the other branch",
    );
    eval_old(
        v,
        "eval434-hold",
        "K34.ev_hold_ok",
        "accept",
        "a value holding a decision, compared with one built by hand",
    );
    eval_old(
        v,
        "eval434-hold-wrong",
        "K34.ev_hold_wrong",
        "reject",
        "the same, claimed none",
    );
    eval_old(
        v,
        "eval434-hold-match",
        "K34.ev_hold_n_ok",
        "accept",
        "a match on a value holding a decision",
    );
    eval_old(
        v,
        "eval434-hold-match-wrong",
        "K34.ev_hold_n_wrong",
        "reject",
        "the same, wrong sum",
    );
    eval_old(
        v,
        "eval434-axiom",
        "K34.ev_ax_eq",
        "reject",
        "elem of an axiom pair in a list of it: left to the definition, stuck as in Lean",
    );
    eval_old(
        v,
        "eval434-list",
        "K34.ev_lists",
        "accept",
        "List.any, all, filter, getLast?, foldl and reverse (v4.34.0)",
    );
    eval_old(
        v,
        "eval434-list-wrong",
        "K34.ev_lists_wrong",
        "reject",
        "the same fold, off by one",
    );
    eval_old(
        v,
        "eval434-filter-lazy",
        "K34.ev_filter_lazy",
        "accept",
        "the head of a filter, whose later tests would divide by zero",
    );
    eval_old(
        v,
        "eval434-filter-lazy-wrong",
        "K34.ev_filter_lazy_wrong",
        "reject",
        "the same, the wrong head",
    );
    eval_old(
        v,
        "eval434-dec-cast",
        "K34.ev_dec_cast",
        "accept",
        "a cast along a proof from Nat.decEq: evaluated again keeping proofs",
    );
    eval_old(
        v,
        "eval434-dec-cast-wrong",
        "K34.ev_dec_cast_wrong",
        "reject",
        "the same sum, off by one",
    );
    eval_old(
        v,
        "eval434-cases",
        "K34.ev_cases_ok",
        "accept",
        "matches through casesOn and sparse casesOn, as in eval-cases",
    );
    eval_old(
        v,
        "eval434-cases-wrong",
        "K34.ev_cases_wrong",
        "reject",
        "the same sum, off by one",
    );
}

// ---------------------------------------------------------------------------
// Disagreements with Lean found by the differential fuzzer (tests/fuzz,
// `cargo xtask difffuzz`). The ones nitrolean still gets wrong are listed in
// tests/kernel/open.tsv.

fn mdata(e: &mut Export, x: Id) -> Id {
    e.expr("mdata", json!({"data": {}, "expr": x}))
}

/// The binder `depth` Pis deep in a declaration's type, renamed or with
/// another binder info.
fn retouch_type(e: &mut Export, name: &str, depth: usize, field: &str, value: Value) {
    let mut chain = vec![e.decl_id(name, "type")];
    for _ in 0..depth {
        let b = e.exprs[chain.last().unwrap()].1["body"].as_u64().unwrap();
        chain.push(b);
    }
    let (k, mut p) = e.exprs[chain.last().unwrap()].clone();
    p[field] = value;
    let mut new = e.expr(&k, p);
    for x in chain.iter().rev().skip(1) {
        let (k, mut p) = e.exprs[x].clone();
        p["body"] = json!(new);
        new = e.expr(&k, p);
    }
    e.set(name, "type", json!(new));
}

fn fuzz_cases(v: &mut Cases) {
    v.text(
        "fuzz-quot-lift-direct",
        "quot",
        "accept",
        "a theorem stated with Quot.lift and Quot.mk, with the names the fuzzer's seed had: valid, \
         but leanchecker --from-export says unknown constant Quot.lift; with other names \
         (K.fz_quot_direct as exported) it accepts",
        |tc| {
            let mut text = as_is(tc, "K.fz_quot_direct")?.text();
            for (a, b) in [
                ("\"str\":\"lean\"", "\"str\":\"seeds\""),
                ("\"str\":\"KCases\"", "\"str\":\"FuzzSeeds\""),
                ("\"str\":\"K\"}", "\"str\":\"FZ\"}"),
                ("\"str\":\"fz_quot_direct\"", "\"str\":\"q_lift_id\""),
            ] {
                assert!(text.contains(a), "{a}");
                text = text.replace(a, b);
            }
            let re = regex::Regex::new(r#""num":\{"i":\d+,"pre":(\d+)\}"#).unwrap();
            Ok(re
                .replacen(&text, 1, r#""num":{"i":4092553897,"pre":$1}"#)
                .into_owned())
        },
    );
    v.add(
        "fuzz-str-deceq",
        "eval.string",
        "accept",
        "decide (\"abc\" = \"abc\") = true by decide: valid (Lean compiles it, and leanchecker \
         accepts the .olean), but leanchecker --from-export fails to reduce it",
        |tc| as_is(tc, "K.fz_str_deceq"),
    );
    v.add(
        "fuzz-mdata-ctor-type",
        "inductive.mdata",
        "reject",
        "Bool.true's type is mdata around Bool: Lean rejects (invalid return type)",
        |tc| {
            let mut e = tc.export(&["Bool.true"], false)?;
            let t = e.decl_id("Bool.true", "type");
            let m = mdata(&mut e, t);
            e.set("Bool.true", "type", json!(m));
            Ok(e)
        },
    );
    v.add(
        "fuzz-mdata-rec-rule",
        "inductive.mdata",
        "reject",
        "a rule of Bool.rec has its right-hand side under mdata: Lean rejects (invalid recursor)",
        |tc| {
            let mut e = tc.export(&["Bool.rec"], false)?;
            let rhs = e.decl("Bool.rec")["rules"][0]["rhs"].as_u64().unwrap();
            let m = mdata(&mut e, rhs);
            e.decl("Bool.rec")["rules"][0]["rhs"] = json!(m);
            Ok(e)
        },
    );
    v.add(
        "fuzz-mdata-quot-type",
        "quot",
        "reject",
        "the type of Quot.ind under mdata: Lean's quotient check rejects it (constant mismatch)",
        |tc| {
            let mut e = tc.export(&QUOT, false)?;
            let t = e.decl_id("Quot.ind", "type");
            let m = mdata(&mut e, t);
            e.set("Quot.ind", "type", json!(m));
            Ok(e)
        },
    );
    v.add(
        "fuzz-quot-binder-name",
        "quot",
        "accept",
        "the binder of the relation in Quot's type renamed: Lean accepts (binder names do not \
         matter)",
        |tc| {
            let mut e = tc.export(&QUOT, false)?;
            let n = e.name("fuzz_renamed");
            retouch_type(&mut e, "Quot", 1, "name", json!(n));
            Ok(e)
        },
    );
    v.add(
        "fuzz-quot-binder-info",
        "quot",
        "accept",
        "the first binder of Quot.mk's type made explicit: Lean accepts (binder info does not \
         matter to the kernel)",
        |tc| {
            let mut e = tc.export(&QUOT, false)?;
            retouch_type(&mut e, "Quot.mk", 0, "binderInfo", json!("default"));
            Ok(e)
        },
    );
    v.text(
        "fuzz-quot-type-alone",
        "quot",
        "accept",
        "the quot declaration of Quot without those of Quot.mk, Quot.lift and Quot.ind, and \
         without their names: Lean accepts (it adds the quotient package at Quot); with the \
         names Quot.mk, Quot.lift, Quot.ind still bound (and unused), nitrolean accepts too",
        |tc| {
            let mut e = tc.export(&QUOT, false)?;
            for c in ["Quot.mk", "Quot.lift", "Quot.ind"] {
                assert!(e.remove_decl(c), "{c}");
            }
            let gone: Vec<Id> = ["Quot.mk", "Quot.lift", "Quot.ind"]
                .iter()
                .map(|c| e.name_id(c).expect("bound"))
                .collect();
            let text = e.text();
            let recs: Vec<Value> = text
                .lines()
                .map(|l| serde_json::from_str(l).unwrap())
                .collect();
            let used: BTreeSet<Id> = recs
                .iter()
                .skip(1)
                .flat_map(|r| crate::kernel_cases::export::deps(r))
                .filter(|d| d.0 == "in")
                .map(|d| d.1)
                .collect();
            let kept: Vec<&str> = text
                .lines()
                .zip(&recs)
                .filter(|(_, r)| {
                    !r["in"]
                        .as_u64()
                        .is_some_and(|i| gone.contains(&i) && !used.contains(&i))
                })
                .map(|(l, _)| l)
                .collect();
            Ok(kept.join("\n") + "\n")
        },
    );
    v.add(
        "fuzz-quot-lift-wrong-type",
        "quot",
        "reject",
        "Quot.lift declared with a wrong type (its motive in Sort 0 instead of Sort v), and no \
         Quot.ind (control for fuzz-quot-type-alone: Lean's quotient post-check rejects it)",
        |tc| {
            let mut e = tc.export(&QUOT, false)?;
            assert!(e.remove_decl("Quot.ind"));
            let t = e.decl_id("Quot.lift", "type");
            let v = e.lparam("v");
            let mut zero = |_: &mut Export, l: Id| if l == v { 0 } else { l };
            let t2 = e.map_levels(t, &mut zero);
            assert_ne!(t, t2);
            e.set("Quot.lift", "type", json!(t2));
            Ok(e)
        },
    );
    v.add(
        "fuzz-ctor-unsafe-flag",
        "inductive.meta",
        "accept",
        "Bool.true's record says isUnsafe while Bool is safe: Lean takes the constructor from \
         the inductive type and ignores the flag",
        |tc| {
            let mut e = tc.export(&["Bool.true"], false)?;
            e.set("Bool.true", "isUnsafe", json!(true));
            Ok(e)
        },
    );
    v.add(
        "fuzz-rec-unsafe-flag",
        "inductive.meta",
        "accept",
        "Bool.rec's record says isUnsafe while Bool is safe: Lean takes the recursor from the \
         inductive type and ignores the flag",
        |tc| {
            let mut e = tc.export(&["Bool.rec"], false)?;
            e.set("Bool.rec", "isUnsafe", json!(true));
            Ok(e)
        },
    );
    v.add(
        "fuzz-type-isrec-flag",
        "inductive.meta",
        "accept",
        "Bool's type record says isRec: Lean computes the flag itself and ignores it",
        |tc| {
            let mut e = tc.export(&["Bool.rec"], false)?;
            ind_record(&mut e, "Bool")["types"][0]["isRec"] = json!(true);
            Ok(e)
        },
    );
    v.add(
        "fuzz-type-unsafe-flag",
        "inductive.meta",
        "reject",
        "Bool's type record says isUnsafe while its constructors and recursor say safe: Lean \
         rejects (No such constructor Bool.false)",
        |tc| {
            let mut e = tc.export(&["Bool.rec"], false)?;
            ind_record(&mut e, "Bool")["types"][0]["isUnsafe"] = json!(true);
            Ok(e)
        },
    );
    v.add(
        "fuzz-type-unsafe-flag-neg",
        "inductive.meta",
        "reject",
        "the same inconsistency on a negative inductive (Neg.mk : (Neg → Nat) → Neg): a safe \
         kernel must not accept it as declared",
        |tc| {
            let mut e = tc.export(&["K.Neg"], true)?;
            make_safe(&mut e, "K.Neg");
            ind_record(&mut e, "K.Neg")["types"][0]["isUnsafe"] = json!(true);
            Ok(e)
        },
    );
    v.add(
        "fuzz-hints-regular-u32",
        "decl.hints",
        "reject",
        "a definition with reducibility hint regular 2^32 + 1: the field is a UInt32 (Lean \
         v4.36.0 truncates it and accepts; nitrolean rejects it, as for numParams)",
        |tc| {
            let mut e = tc.export(&["K.fz_two"], false)?;
            e.set("K.fz_two", "hints", json!({"regular": U32 as u64 + 1}));
            Ok(e)
        },
    );
}
