//! Mutation operators. Each operator gets the seed, a fresh mutant for one
//! declaration and the generator, and returns whether it changed something.
//! Everything is deterministic given the generator.

use std::collections::HashMap;

use serde_json::{Value, json};

use super::export::{Decl, Mutant, Pos, Root, Seed, at_loc, decl_roots, positions, u};
use super::rng::Rng;

/// The constants nitrolean (and Lean) accelerate by name. A definition of one
/// of these that is not the standard one is a deliberate divergence
/// (corpus/divergences.md, `historical/010_HB15908.contra`).
pub const BUILTINS: &[&str] = &[
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.div",
    "Nat.mod",
    "Nat.gcd",
    "Nat.beq",
    "Nat.ble",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "Nat.pow",
    "Nat.log2",
    "Nat.succ",
    "Nat.zero",
    "Nat",
    "Nat.rec",
    "Nat.pred",
    "String",
    "String.mk",
    "String.ofList",
    "Char",
    "Char.ofNat",
    "List",
    "List.cons",
    "List.nil",
    "Array",
    "Array.mk",
    "Array.push",
    "Array.size",
    "Array.get",
    "Array.set",
    "Array.getD",
    "Array.get!",
    "Array.getInternal",
    "Array.set!",
    "Array.setIfInBounds",
    "Array.uget",
    "Array.uset",
    "Array.pop",
    "Array.mkEmpty",
    "Array.emptyWithCapacity",
    "Array.empty",
    "Array.toList",
    "Array.replicate",
    "Bool",
    "Bool.true",
    "Bool.false",
    "Eq",
    "Eq.refl",
    "Decidable.decide",
    "instDecidableEqNat",
    "Nat.decEq",
    "Nat.decLe",
    "Nat.decLt",
];

const NAT_SPECIAL: &[&str] = &[
    "0",
    "1",
    "2",
    "256",
    "65536",
    "4294967295",
    "4294967296",
    "9223372036854775808",
    "18446744073709551615",
    "18446744073709551616",
    "18446744073709551617",
    "340282366920938463463374607431768211456",
    "16777217",
];

type Op = fn(&Seed, &mut Mutant, &mut Rng, &Decl) -> bool;

pub const CATEGORIES: &[&str] = &[
    "subterm",
    "universe",
    "natlit",
    "inductive",
    "proj",
    "quot",
    "let",
    "hints",
    "eval",
    "equiv",
];

pub fn ops(category: &str) -> Vec<(&'static str, Op)> {
    match category {
        "subterm" => vec![
            ("swap_subterm", op_swap_subterm as Op),
            ("swap_const", op_swap_const),
            ("swap_args", op_swap_args),
            ("arity", op_arity),
            ("statement_swap", op_statement_swap),
            ("proof_swap", op_proof_swap),
        ],
        "universe" => vec![
            ("sort_level", op_sort_level as Op),
            ("const_levels", op_const_levels),
            ("decl_lparams", op_decl_lparams),
        ],
        "natlit" => vec![
            ("nat_lit", op_nat_lit as Op),
            ("str_lit", op_str_lit),
            ("nat_unfold", op_nat_unfold),
        ],
        "inductive" => vec![
            ("inductive_field", op_inductive_field as Op),
            ("inductive_term", op_inductive_term),
        ],
        "proj" => vec![
            ("proj", op_proj as Op),
            ("proj_insert", op_proj_insert),
            ("eta_struct", op_eta_struct),
        ],
        "quot" => vec![
            ("quot_decl", op_quot_decl as Op),
            ("quot_term", op_quot_term),
        ],
        "let" => vec![
            ("let", op_let as Op),
            ("let_intro", op_let_intro),
            ("bvar", op_bvar),
            ("binder", op_binder),
        ],
        "hints" => vec![("hints", op_hints as Op), ("decl_kind", op_decl_kind)],
        "eval" => vec![
            ("eval_statement", op_eval_statement as Op),
            ("eval_value", op_eval_value),
            ("eval_const", op_eval_const),
        ],
        "equiv" => vec![
            ("cosmetic", op_cosmetic as Op),
            ("nat_unfold", op_nat_unfold),
            ("let_intro", op_let_intro),
            ("hints", op_hints),
        ],
        _ => vec![],
    }
}

/// Which declaration kinds a category prefers.
fn want_kind(category: &str) -> Option<&'static [&'static str]> {
    match category {
        "inductive" => Some(&["inductive"]),
        "quot" => Some(&["quot", "thm", "def"]),
        "hints" => Some(&["def", "thm", "opaque"]),
        "eval" => Some(&["thm", "def"]),
        _ => None,
    }
}

/// Pick a declaration: the seed's own (names starting with `focus`) first,
/// otherwise mostly the last ones (a test's own declarations come last).
fn choose_decl(seed: &Seed, category: &str, rng: &mut Rng, focus: Option<&str>) -> Option<usize> {
    let want = want_kind(category);
    let cands: Vec<usize> = (0..seed.decls.len())
        .filter(|&i| want.is_none_or(|w| w.contains(&seed.decls[i].kind.as_str())))
        .collect();
    if cands.is_empty() {
        return None;
    }
    if let Some(f) = focus {
        let own: Vec<usize> = cands
            .iter()
            .copied()
            .filter(|&i| {
                seed.decl_names(&seed.decls[i])
                    .iter()
                    .any(|n| n.starts_with(f))
            })
            .collect();
        if !own.is_empty() && rng.chance(0.85) {
            return Some(*rng.pick(&own));
        }
    }
    if rng.chance(0.6) {
        let n = (cands.len() / 10).max(3).min(cands.len());
        return Some(*rng.pick(&cands[cands.len() - n..]));
    }
    Some(*rng.pick(&cands))
}

/// A mutant of `seed` in `category`, or None.
pub fn mutate<'s>(
    seed: &'s Seed,
    category: &str,
    rng: &mut Rng,
    focus: Option<&str>,
) -> Option<Mutant<'s>> {
    let ops = ops(category);
    for _ in 0..30 {
        let di = choose_decl(seed, category, rng, focus)?;
        let d = &seed.decls[di];
        let (name, op) = *rng.pick(&ops);
        let mut m = Mutant::new(seed, d.line);
        m.op = name.to_string();
        m.decl = seed.decl_names(d).first().cloned().unwrap_or_default();
        if op(seed, &mut m, rng, d) && !m.replace.is_empty() {
            if !m.truncate && rng.chance(0.3) {
                m.truncate = true;
            }
            return Some(m);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Helpers

fn pick_root(rng: &mut Rng, d: &Decl, want: Option<&[&str]>) -> Option<Root> {
    let mut roots = decl_roots(&d.kind, &d.payload);
    if let Some(w) = want {
        let f: Vec<Root> = roots
            .iter()
            .filter(|r| w.contains(&r.label))
            .cloned()
            .collect();
        if !f.is_empty() {
            roots = f;
        }
    }
    if roots.is_empty() {
        return None;
    }
    let weights: Vec<u32> = roots
        .iter()
        .map(|r| {
            if matches!(r.label, "value" | "rule") {
                3
            } else {
                1
            }
        })
        .collect();
    Some(roots[rng.weighted(&weights)].clone())
}

fn pick_pos(
    seed: &Seed,
    rng: &mut Rng,
    d: &Decl,
    pred: &dyn Fn(u64, u64) -> bool,
    want: Option<&[&str]>,
) -> Option<(Root, Pos)> {
    for _ in 0..4 {
        let root = pick_root(rng, d, want)?;
        let pos: Vec<Pos> = positions(seed, root.expr, 4000, Some(rng))
            .into_iter()
            .filter(|(_, e, dd)| pred(*e, *dd))
            .collect();
        if !pos.is_empty() {
            let i = rng.below(pos.len());
            return Some((root, pos.into_iter().nth(i).unwrap()));
        }
    }
    None
}

/// Pick a position satisfying `pred`, build its replacement with `make`, and rebuild.
fn replace_at(
    seed: &Seed,
    m: &mut Mutant,
    rng: &mut Rng,
    d: &Decl,
    pred: &dyn Fn(u64, u64) -> bool,
    make: &mut dyn FnMut(&mut Mutant, &mut Rng, u64, u64) -> Option<u64>,
    want: Option<&[&str]>,
) -> bool {
    let Some((root, (path, e, depth))) = pick_pos(seed, rng, d, pred, want) else {
        return false;
    };
    let Some(new) = make(m, rng, e, depth) else {
        return false;
    };
    if new == e {
        return false;
    }
    let r = m.rebuild(&path, new);
    m.set_root(&d.kind, &d.payload, &root, r);
    let info = at_loc(&d.payload, root.loc);
    m.note = format!(
        "{} of {}",
        root.label,
        info.get("name")
            .map(|n| seed.name_str(u(n)))
            .unwrap_or_else(|| "rule".into())
    );
    true
}

fn is_kind<'a>(seed: &'a Seed, k: &'a str) -> impl Fn(u64, u64) -> bool + 'a {
    move |e, _| seed.ekind(e) == k
}

fn all_positions(seed: &Seed, d: &Decl, limit: usize, rng: &mut Rng) -> Vec<Pos> {
    let mut pool = Vec::new();
    for r in decl_roots(&d.kind, &d.payload) {
        pool.extend(positions(seed, r.expr, limit, Some(rng)));
    }
    pool
}

fn lparams(d: &Decl) -> Vec<u64> {
    let x = if d.kind == "inductive" {
        &d.payload["types"][0]
    } else {
        &d.payload
    };
    x["levelParams"]
        .as_array()
        .map(|a| a.iter().map(u).collect())
        .unwrap_or_default()
}

fn nlparams(x: &Value) -> usize {
    x["levelParams"].as_array().map_or(0, |a| a.len())
}

// ---------------------------------------------------------------------------
// subterm

fn op_swap_subterm(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    let pool: Vec<u64> = all_positions(seed, d, 1500, rng)
        .into_iter()
        .map(|p| p.1)
        .collect();
    if pool.len() < 2 {
        return false;
    }
    replace_at(
        seed,
        m,
        rng,
        d,
        &|_, _| true,
        &mut |_, rng, e, depth| {
            let k = seed.ekind(e);
            let same: Vec<u64> = pool
                .iter()
                .copied()
                .filter(|&x| x != e && seed.lbr(x) <= depth)
                .collect();
            let pref: Vec<u64> = same
                .iter()
                .copied()
                .filter(|&x| seed.ekind(x) == k)
                .collect();
            let cand = if !pref.is_empty() && rng.chance(0.8) {
                pref
            } else {
                same
            };
            (!cand.is_empty()).then(|| *rng.pick(&cand))
        },
        None,
    )
}

fn op_swap_const(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    let line = m.line;
    let mut by_type: HashMap<(u64, usize), Vec<&String>> = HashMap::new();
    for (c, (l, _, x)) in &seed.consts {
        if *l < line && x.get("type").is_some() {
            by_type
                .entry((u(&x["type"]), nlparams(x)))
                .or_default()
                .push(c);
        }
    }
    for v in by_type.values_mut() {
        v.sort();
    }
    let mut names: Vec<&String> = seed
        .consts
        .keys()
        .filter(|c| seed.consts[*c].0 < line)
        .collect();
    names.sort();
    replace_at(
        seed,
        m,
        rng,
        d,
        &is_kind(seed, "const"),
        &mut |m, rng, e, _| {
            let p = &seed.expr(e).1;
            let nm = seed.name_str(u(&p["name"]));
            let nus = p["us"].as_array().map_or(0, |a| a.len());
            let mut cands: Vec<&String> = Vec::new();
            if let Some((_, _, x)) = seed.consts.get(&nm)
                && x.get("type").is_some()
            {
                cands = by_type
                    .get(&(u(&x["type"]), nus))
                    .into_iter()
                    .flatten()
                    .copied()
                    .filter(|c| **c != nm)
                    .collect();
            }
            if cands.is_empty() || rng.chance(0.2) {
                cands = names
                    .iter()
                    .copied()
                    .filter(|c| **c != nm && nlparams(&seed.consts[*c].2) == nus)
                    .collect();
            }
            if cands.is_empty() {
                return None;
            }
            let c = *rng.pick(&cands);
            let id = u(&seed.consts[c].2["name"]);
            Some(m.expr("const", json!({"name": id, "us": p["us"]})))
        },
        None,
    )
}

fn op_swap_args(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    let pred = |e: u64, _| seed.ekind(e) == "app" && seed.ekind(u(&seed.expr(e).1["fn"])) == "app";
    replace_at(
        seed,
        m,
        rng,
        d,
        &pred,
        &mut |m, _, e, _| {
            let p = &seed.expr(e).1;
            let q = &seed.expr(u(&p["fn"])).1;
            if q["arg"] == p["arg"] {
                return None;
            }
            let inner = m.expr("app", json!({"fn": q["fn"], "arg": p["arg"]}));
            Some(m.expr("app", json!({"fn": inner, "arg": q["arg"]})))
        },
        None,
    )
}

fn op_arity(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    replace_at(
        seed,
        m,
        rng,
        d,
        &is_kind(seed, "app"),
        &mut |m, rng, e, _| {
            let p = &seed.expr(e).1;
            if rng.chance(0.5) {
                Some(u(&p["fn"]))
            } else {
                Some(m.expr("app", json!({"fn": e, "arg": p["arg"]})))
            }
        },
        None,
    )
}

fn decl_like(k: &str) -> bool {
    matches!(k, "thm" | "def" | "axiom" | "opaque")
}

fn sorted_consts(seed: &Seed) -> Vec<(&String, &(usize, String, Value))> {
    let mut v: Vec<_> = seed.consts.iter().collect();
    v.sort_by(|a, b| a.0.cmp(b.0));
    v
}

fn op_statement_swap(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    if !decl_like(&d.kind) {
        return false;
    }
    let n = nlparams(&d.payload);
    let cands: Vec<u64> = sorted_consts(seed)
        .into_iter()
        .filter(|(_, (l, k, x))| {
            decl_like(k) && *l < m.line && nlparams(x) == n && x["type"] != d.payload["type"]
        })
        .map(|(_, (_, _, x))| u(&x["type"]))
        .collect();
    if cands.is_empty() {
        return false;
    }
    let t = *rng.pick(&cands);
    let root = Root {
        label: "type",
        loc: super::export::Loc::Top,
        field: "type",
        expr: 0,
    };
    m.set_root(&d.kind, &d.payload, &root, t);
    true
}

fn op_proof_swap(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    if !matches!(d.kind.as_str(), "thm" | "def") {
        return false;
    }
    let n = nlparams(&d.payload);
    let cands: Vec<u64> = sorted_consts(seed)
        .into_iter()
        .filter(|(_, (l, k, x))| {
            *l < m.line && nlparams(x) == n && (k == "thm") == (d.kind == "thm")
        })
        .map(|(_, (_, _, x))| u(&x["name"]))
        .collect();
    if cands.is_empty() {
        return false;
    }
    let c = *rng.pick(&cands);
    let us: Vec<u64> = lparams(d)
        .iter()
        .map(|&n| m.level("param", json!(n)))
        .collect();
    let e = m.expr("const", json!({"name": c, "us": us}));
    let root = Root {
        label: "value",
        loc: super::export::Loc::Top,
        field: "value",
        expr: 0,
    };
    m.set_root(&d.kind, &d.payload, &root, e);
    true
}

// ---------------------------------------------------------------------------
// universes

fn mut_level(seed: &Seed, m: &mut Mutant, rng: &mut Rng, l: u64, lps: &[u64]) -> u64 {
    let (k, p) = seed
        .levels
        .get(&l)
        .cloned()
        .unwrap_or(("zero".into(), Value::Null));
    match rng.below(8) {
        1 if k == "succ" => u(&p),
        2 => 0,
        3 if !lps.is_empty() => m.level("param", json!(*rng.pick(lps))),
        4 if k == "max" || k == "imax" => m.level(if k == "max" { "imax" } else { "max" }, p),
        5 if k == "max" || k == "imax" => {
            if rng.chance(0.3) {
                m.level(&k, json!([p[1], p[0]]))
            } else {
                u(&p[rng.below(2)])
            }
        }
        6 => {
            let other = if lps.is_empty() {
                m.level("succ", json!(0))
            } else {
                m.level("param", json!(*rng.pick(lps)))
            };
            let op = if rng.chance(0.5) { "max" } else { "imax" };
            let args = if rng.chance(0.5) {
                json!([l, other])
            } else {
                json!([other, l])
            };
            m.level(op, args)
        }
        7 => {
            let n = *rng.pick(&["u", "v", "w", "u_1", "fuzz_u"]);
            let id = m.name(n);
            m.level("param", json!(id))
        }
        _ => m.level("succ", json!(l)),
    }
}

fn op_sort_level(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    let lps = lparams(d);
    replace_at(
        seed,
        m,
        rng,
        d,
        &is_kind(seed, "sort"),
        &mut |m, rng, e, _| {
            let l = mut_level(seed, m, rng, u(&seed.expr(e).1), &lps);
            Some(m.expr("sort", json!(l)))
        },
        None,
    )
}

fn op_const_levels(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    let lps = lparams(d);
    replace_at(
        seed,
        m,
        rng,
        d,
        &is_kind(seed, "const"),
        &mut |m, rng, e, _| {
            let p = &seed.expr(e).1;
            let mut us: Vec<u64> = p["us"]
                .as_array()
                .map(|a| a.iter().map(u).collect())
                .unwrap_or_default();
            match rng.below(4) {
                0 if !us.is_empty() => {
                    let i = rng.below(us.len());
                    us.remove(i);
                }
                1 => {
                    let l = if us.is_empty() { 0 } else { *rng.pick(&us) };
                    let i = rng.below(us.len() + 1);
                    us.insert(i, l);
                }
                2 if us.len() >= 2 => {
                    let (i, j) = rng.two(us.len());
                    if us[i] == us[j] {
                        return None;
                    }
                    us.swap(i, j);
                }
                _ if !us.is_empty() => {
                    let i = rng.below(us.len());
                    us[i] = mut_level(seed, m, rng, us[i], &lps);
                }
                _ => return None,
            }
            Some(m.expr("const", json!({"name": p["name"], "us": us})))
        },
        None,
    )
}

fn op_decl_lparams(_seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    let mut p = d.payload.clone();
    let mut locs: Vec<super::export::Loc> = Vec::new();
    if d.kind == "inductive" {
        for g in ["types", "ctors", "recs"] {
            for i in 0..p[g].as_array().map_or(0, |a| a.len()) {
                locs.push(super::export::Loc::Part(g, i));
            }
        }
        if rng.chance(0.5) {
            locs = vec![*rng.pick(&locs)];
        }
    } else {
        locs.push(super::export::Loc::Top);
    }
    let c = rng.below(4);
    let fresh = m.name("fuzz_u");
    let mut changed = false;
    for loc in locs {
        let x = super::export::at_loc_mut(&mut p, loc);
        let Some(lp) = x.get_mut("levelParams").and_then(|v| v.as_array_mut()) else {
            continue;
        };
        match c {
            0 if !lp.is_empty() => {
                if rng.chance(0.5) {
                    lp.remove(0);
                } else {
                    lp.pop();
                }
                changed = true;
            }
            1 if !lp.is_empty() => {
                let f = lp[0].clone();
                lp.push(f);
                changed = true;
            }
            2 if lp.len() >= 2 => {
                lp.swap(0, 1);
                changed = true;
            }
            3 => {
                if rng.chance(0.5) {
                    lp.insert(0, json!(fresh));
                } else {
                    lp.push(json!(fresh));
                }
                changed = true;
            }
            _ => {}
        }
    }
    if changed {
        m.set_decl(&d.kind, p);
    }
    changed
}

// ---------------------------------------------------------------------------
// literals (decimal strings, so that big values need no big-integer crate)

fn dec_add(a: &str, b: &str) -> String {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    let mut out = Vec::new();
    let (mut i, mut j, mut carry) = (a.len(), b.len(), 0u8);
    while i > 0 || j > 0 || carry > 0 {
        let x = if i > 0 {
            i -= 1;
            a[i] - b'0'
        } else {
            0
        };
        let y = if j > 0 {
            j -= 1;
            b[j] - b'0'
        } else {
            0
        };
        let s = x + y + carry;
        out.push(b'0' + s % 10);
        carry = s / 10;
    }
    out.reverse();
    trim(String::from_utf8(out).unwrap())
}

/// a - 1 for a > 0.
fn dec_pred(a: &str) -> String {
    let mut v: Vec<u8> = a.bytes().collect();
    let mut i = v.len();
    while i > 0 {
        i -= 1;
        if v[i] == b'0' {
            v[i] = b'9';
        } else {
            v[i] -= 1;
            break;
        }
    }
    trim(String::from_utf8(v).unwrap())
}

fn dec_half(a: &str) -> String {
    let mut out = String::new();
    let mut r = 0u8;
    for b in a.bytes() {
        let x = r * 10 + (b - b'0');
        out.push((b'0' + x / 2) as char);
        r = x % 2;
    }
    trim(out)
}

fn trim(s: String) -> String {
    let t = s.trim_start_matches('0');
    if t.is_empty() {
        "0".into()
    } else {
        t.to_string()
    }
}

fn perturb_nat(rng: &mut Rng, n: &str) -> String {
    let zero = n == "0";
    match rng.below(7) {
        0 => dec_add(n, "1"),
        1 => {
            if zero {
                "1".into()
            } else {
                dec_pred(n)
            }
        }
        2 => {
            if zero {
                "1".into()
            } else {
                dec_add(n, n)
            }
        }
        3 => dec_half(n),
        4 => rng.pick(NAT_SPECIAL).to_string(),
        5 => {
            // flip a low bit, when the value fits in 64 bits
            match n.parse::<u64>() {
                Ok(v) => (v ^ (1u64 << rng.below((64 - v.leading_zeros() as usize + 2).min(63))))
                    .to_string(),
                Err(_) => dec_add(n, "1"),
            }
        }
        _ => {
            if zero {
                "18446744073709551616".into()
            } else {
                dec_add(n, rng.pick(&["4294967296", "18446744073709551616"]))
            }
        }
    }
}

fn op_nat_lit_in(
    seed: &Seed,
    m: &mut Mutant,
    rng: &mut Rng,
    d: &Decl,
    want: Option<&[&str]>,
) -> bool {
    replace_at(
        seed,
        m,
        rng,
        d,
        &is_kind(seed, "natVal"),
        &mut |m, rng, e, _| {
            let n = seed.expr(e).1.as_str().unwrap_or("0").to_string();
            let v = perturb_nat(rng, &n);
            (v != n).then(|| m.expr("natVal", json!(v)))
        },
        want,
    )
}

fn op_nat_lit(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    op_nat_lit_in(seed, m, rng, d, None)
}

fn op_str_lit(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    replace_at(
        seed,
        m,
        rng,
        d,
        &is_kind(seed, "strVal"),
        &mut |m, rng, e, _| {
            let s: Vec<char> = seed.expr(e).1.as_str().unwrap_or("").chars().collect();
            let mut t = s.clone();
            match rng.below(4) {
                0 => t.push(*rng.pick(&['a', 'é', '\u{1F600}', '\0'])),
                1 if !s.is_empty() => {
                    let i = rng.below(s.len());
                    t.remove(i);
                }
                2 if !s.is_empty() => {
                    let i = rng.below(s.len());
                    t[i] = char::from_u32(t[i] as u32 + 1).unwrap_or('a');
                }
                _ => {
                    if s.len() > 1 {
                        t.reverse();
                    } else {
                        t.extend(s.iter());
                    }
                }
            }
            (t != s).then(|| m.expr("strVal", json!(t.into_iter().collect::<String>())))
        },
        None,
    )
}

/// Equivalent: a literal `n` written as `Nat.succ (n-1)`, `0` as `Nat.zero` (accept).
fn op_nat_unfold(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    if !seed.const_before("Nat.succ", m.line) {
        return false;
    }
    m.expect = "accept";
    replace_at(
        seed,
        m,
        rng,
        d,
        &is_kind(seed, "natVal"),
        &mut |m, _, e, _| {
            let n = seed.expr(e).1.as_str().unwrap_or("0").to_string();
            if n == "0" {
                let z = m.name("Nat.zero");
                return Some(m.expr("const", json!({"name": z, "us": []})));
            }
            let s = m.name("Nat.succ");
            let f = m.expr("const", json!({"name": s, "us": []}));
            let a = m.expr("natVal", json!(dec_pred(&n)));
            Some(m.expr("app", json!({"fn": f, "arg": a})))
        },
        None,
    )
}

// ---------------------------------------------------------------------------
// inductive declarations

fn op_inductive_field(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    use super::export::Loc;
    if d.kind != "inductive" {
        return false;
    }
    let mut p = d.payload.clone();
    let mut opts: Vec<(Loc, &str)> = Vec::new();
    let count = |g: &str| p[g].as_array().map_or(0, |a| a.len());
    for i in 0..count("types") {
        for f in [
            "numParams",
            "numIndices",
            "isRec",
            "isReflexive",
            "numNested",
            "isUnsafe",
            "ctors",
            "all",
        ] {
            opts.push((Loc::Part("types", i), f));
        }
    }
    for i in 0..count("ctors") {
        for f in ["numParams", "numFields", "cidx", "isUnsafe", "induct"] {
            opts.push((Loc::Part("ctors", i), f));
        }
    }
    for r in 0..count("recs") {
        for f in [
            "numParams",
            "numIndices",
            "numMotives",
            "numMinors",
            "k",
            "isUnsafe",
            "rules",
            "all",
        ] {
            opts.push((Loc::Part("recs", r), f));
        }
        for i in 0..p["recs"][r]["rules"].as_array().map_or(0, |a| a.len()) {
            for f in ["nfields", "ctor", "rhs"] {
                opts.push((Loc::Rule(r, i), f));
            }
        }
    }
    let (loc, f) = *rng.pick(&opts);
    let ctor_names: Vec<Value> = ["ctors", "types"]
        .iter()
        .flat_map(|g| p[*g].as_array().cloned().unwrap_or_default())
        .map(|x| x["name"].clone())
        .collect();
    let rhss: Vec<Value> = p["recs"]
        .as_array()
        .into_iter()
        .flatten()
        .flat_map(|r| r["rules"].as_array().cloned().unwrap_or_default())
        .map(|r| r["rhs"].clone())
        .collect();
    let x = super::export::at_loc_mut(&mut p, loc);
    let v = x[f].clone();
    let new = if let Some(b) = v.as_bool() {
        json!(!b)
    } else if f == "ctor" || f == "induct" || f == "rhs" {
        let pool = if f == "rhs" { &rhss } else { &ctor_names };
        let alts: Vec<&Value> = pool.iter().filter(|y| **y != v).collect();
        if alts.is_empty() {
            return false;
        }
        (*rng.pick(&alts)).clone()
    } else if let Some(n) = v.as_u64() {
        let deltas: [i128; 5] = [1, -1, 1, 1 << 32, (1 << 32) + 1];
        let dlt = if rng.chance(0.95) {
            *rng.pick(&deltas)
        } else {
            *rng.pick(&[1i128 << 31, 1i128 << 63])
        };
        let mut nv = n as i128 + dlt;
        if nv < 0 {
            nv = n as i128 + 1;
        }
        json!(nv as u64)
    } else if let Some(a) = v.as_array() {
        let mut a = a.clone();
        if a.len() >= 2 && rng.chance(0.6) {
            let (i, j) = rng.two(a.len());
            a.swap(i, j);
        } else if !a.is_empty() && rng.chance(0.5) {
            let i = rng.below(a.len());
            a.remove(i);
        } else if !a.is_empty() {
            let f0 = a[0].clone();
            a.push(f0);
        } else {
            return false;
        }
        json!(a)
    } else {
        return false;
    };
    let nm = x
        .get("name")
        .or_else(|| x.get("ctor"))
        .map(|n| seed.name_str(u(n)))
        .unwrap_or_default();
    x[f] = new;
    m.set_decl(&d.kind, p);
    m.note = format!("{nm}.{f}");
    true
}

fn mentions(seed: &Seed, e: u64, names: &[u64]) -> bool {
    positions(seed, e, 300, None)
        .iter()
        .any(|(_, x, _)| seed.ekind(*x) == "const" && names.contains(&u(&seed.expr(*x).1["name"])))
}

fn op_inductive_term(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    if d.kind != "inductive" {
        return false;
    }
    let roots = decl_roots(&d.kind, &d.payload);
    let root = rng.pick(&roots).clone();
    let sub = rng.below(5);
    let pos = positions(seed, root.expr, 4000, Some(rng));
    let names: Vec<u64> = d.payload["types"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|x| u(&x["name"]))
        .collect();
    let of = |k: &str| -> Vec<&Pos> { pos.iter().filter(|p| seed.ekind(p.1) == k).collect() };
    let (path, new) = match sub {
        0 => {
            // positivity: a binder type T becomes T -> T (T in a negative position)
            let mut cands = of("forallE");
            let rich: Vec<&Pos> = cands
                .iter()
                .copied()
                .filter(|p| mentions(seed, u(&seed.expr(p.1).1["type"]), &names))
                .collect();
            if !rich.is_empty() && rng.chance(0.8) {
                cands = rich;
            }
            if cands.is_empty() {
                return false;
            }
            let (path, e, _) = (*rng.pick(&cands)).clone();
            let p = seed.expr(e).1.clone();
            let t = u(&p["type"]);
            let lt = m.lift(t, 1, 0);
            let neg = m.expr(
                "forallE",
                json!({"binderInfo": "default", "name": p["name"], "type": t, "body": lt}),
            );
            let tt = if rng.chance(0.7) {
                neg
            } else {
                m.expr(
                    "forallE",
                    json!({"binderInfo": "default", "name": p["name"], "type": neg, "body": lt}),
                )
            };
            let mut q = p;
            q["type"] = json!(tt);
            m.note = format!("negative occurrence in {}", root.label);
            (path, m.expr("forallE", q))
        }
        1 => {
            let sorts = of("sort");
            if sorts.is_empty() {
                return false;
            }
            let (path, e, _) = (*rng.pick(&sorts)).clone();
            let l = mut_level(seed, m, rng, u(&seed.expr(e).1), &lparams(d));
            m.note = format!("sort in {}", root.label);
            (path, m.expr("sort", json!(l)))
        }
        2 => {
            let bv = of("bvar");
            if bv.is_empty() {
                return false;
            }
            let (path, e, depth) = (*rng.pick(&bv)).clone();
            let i = u(&seed.expr(e).1);
            let mut j = if depth > 0 {
                match rng.below(3) {
                    0 => i + 1,
                    1 => i.wrapping_sub(1),
                    _ => rng.below(depth as usize) as u64,
                }
            } else {
                i + 1
            };
            if j == i || j == u64::MAX {
                j = i + 1;
            }
            m.note = format!("bvar in {}", root.label);
            (path, m.expr("bvar", json!(j)))
        }
        3 => {
            let cs = of("const");
            let block: Vec<u64> = ["types", "ctors"]
                .iter()
                .flat_map(|g| d.payload[*g].as_array().cloned().unwrap_or_default())
                .map(|x| u(&x["name"]))
                .collect();
            if cs.is_empty() || block.len() < 2 {
                return false;
            }
            let (path, e, _) = (*rng.pick(&cs)).clone();
            let p = &seed.expr(e).1;
            let alts: Vec<u64> = block
                .iter()
                .copied()
                .filter(|&n| n != u(&p["name"]))
                .collect();
            m.note = format!("const in {}", root.label);
            (
                path,
                m.expr("const", json!({"name": *rng.pick(&alts), "us": p["us"]})),
            )
        }
        _ => {
            let fa = of("forallE");
            if fa.len() < 2 {
                return false;
            }
            let (i, j) = rng.two(fa.len());
            let (path, e, depth) = fa[i].clone();
            let t2 = u(&seed.expr(fa[j].1).1["type"]);
            if seed.lbr(t2) > depth || t2 == u(&seed.expr(e).1["type"]) {
                return false;
            }
            let mut q = seed.expr(e).1.clone();
            q["type"] = json!(t2);
            m.note = format!("binder type in {}", root.label);
            (path, m.expr("forallE", q))
        }
    };
    let r = m.rebuild(&path, new);
    m.set_root(&d.kind, &d.payload, &root, r);
    true
}

// ---------------------------------------------------------------------------
// projections, structure eta

fn structures(seed: &Seed, line: usize) -> Vec<u64> {
    let mut v: Vec<(&String, u64)> = seed
        .consts
        .iter()
        .filter(|(_, (l, k, x))| k == "inductive" && x.get("numIndices").is_some() && *l < line)
        .map(|(c, (_, _, x))| (c, u(&x["name"])))
        .collect();
    v.sort();
    v.into_iter().map(|x| x.1).collect()
}

fn op_proj(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    let structs = structures(seed, m.line + 1);
    replace_at(
        seed,
        m,
        rng,
        d,
        &is_kind(seed, "proj"),
        &mut |m, rng, e, _| {
            let mut p = seed.expr(e).1.clone();
            let idx = u(&p["idx"]);
            match rng.below(4) {
                0 => p["idx"] = json!(idx + 1),
                1 => {
                    if idx == 0 {
                        return None;
                    }
                    p["idx"] = json!(idx - 1);
                }
                2 if !structs.is_empty() => p["typeName"] = json!(*rng.pick(&structs)),
                _ => p["idx"] = json!(*rng.pick(&[idx + 2, 1 << 32, (1 << 32) + idx])),
            }
            Some(m.expr("proj", p))
        },
        None,
    )
}

fn op_proj_insert(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    let structs = structures(seed, m.line);
    if structs.is_empty() {
        return false;
    }
    replace_at(
        seed,
        m,
        rng,
        d,
        &|_, _| true,
        &mut |m, rng, e, _| {
            let (k, p) = seed.expr(e);
            if k == "proj" && rng.chance(0.5) {
                return Some(u(&p["struct"]));
            }
            let s = *rng.pick(&structs);
            Some(m.expr(
                "proj",
                json!({"typeName": s, "idx": rng.below(3), "struct": e}),
            ))
        },
        None,
    )
}

/// `x.i` becomes `(S.mk x.0 ... x.n).i` for a structure without parameters
/// (structure eta: accept), or the same with two fields swapped.
fn op_eta_struct(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    let Some((root, (path, e, _))) = pick_pos(seed, rng, d, &is_kind(seed, "proj"), None) else {
        return false;
    };
    let p = seed.expr(e).1.clone();
    let sname = seed.name_str(u(&p["typeName"]));
    let Some((_, k, si)) = seed.consts.get(&sname) else {
        return false;
    };
    let ctors = si["ctors"].as_array().cloned().unwrap_or_default();
    if k != "inductive" || ctors.len() != 1 || u(&si["numParams"]) != 0 || nlparams(si) != 0 {
        return false;
    }
    let ctor = u(&ctors[0]);
    let Some((_, _, ci)) = seed.consts.get(&seed.name_str(ctor)) else {
        return false;
    };
    let nf = u(&ci["numFields"]) as usize;
    if nf < 1 {
        return false;
    }
    let mut fields: Vec<u64> = (0..nf)
        .map(|i| {
            m.expr(
                "proj",
                json!({"typeName": p["typeName"], "idx": i, "struct": p["struct"]}),
            )
        })
        .collect();
    if nf >= 2 && rng.chance(0.5) {
        let (i, j) = rng.two(nf);
        fields.swap(i, j);
        m.note = format!("eta with fields {i} and {j} swapped");
    } else {
        m.expect = "accept";
        m.note = "eta".into();
    }
    let mut t = m.expr("const", json!({"name": ctor, "us": []}));
    for f in fields {
        t = m.expr("app", json!({"fn": t, "arg": f}));
    }
    let new = m.expr(
        "proj",
        json!({"typeName": p["typeName"], "idx": p["idx"], "struct": t}),
    );
    let r = m.rebuild(&path, new);
    m.set_root(&d.kind, &d.payload, &root, r);
    true
}

// ---------------------------------------------------------------------------
// quotients

const QUOT: [&str; 4] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];

fn op_quot_decl(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    if d.kind != "quot" {
        return false;
    }
    let mut p = d.payload.clone();
    match rng.below(4) {
        0 => {
            let kinds: Vec<&str> = ["type", "ctor", "lift", "ind"]
                .into_iter()
                .filter(|k| p["kind"] != json!(k))
                .collect();
            p["kind"] = json!(*rng.pick(&kinds));
        }
        1 => {
            let fresh = m.name("fuzz_u");
            let lp = p["levelParams"].as_array_mut().unwrap();
            if !lp.is_empty() && rng.chance(0.5) {
                lp.pop();
            } else {
                lp.push(json!(fresh));
            }
        }
        2 => {
            let others: Vec<Value> = sorted_consts(seed)
                .into_iter()
                .filter(|(_, (_, k, x))| k == "quot" && x["type"] != p["type"])
                .map(|(_, (_, _, x))| x["type"].clone())
                .collect();
            if others.is_empty() {
                return false;
            }
            p["type"] = rng.pick(&others).clone();
        }
        _ => return op_sort_level(seed, m, rng, d),
    }
    m.set_decl(&d.kind, p);
    true
}

fn op_quot_term(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    let qn: Vec<u64> = QUOT
        .iter()
        .filter_map(|q| seed.name_ids.get(*q).copied())
        .collect();
    if qn.is_empty() {
        return false;
    }
    let is_q = |e: u64| seed.ekind(e) == "const" && qn.contains(&u(&seed.expr(e).1["name"]));
    if rng.chance(0.5) {
        return replace_at(
            seed,
            m,
            rng,
            d,
            &|e, _| is_q(e),
            &mut |m, rng, e, _| {
                let p = &seed.expr(e).1;
                let alts: Vec<u64> = qn.iter().copied().filter(|&x| x != u(&p["name"])).collect();
                (!alts.is_empty())
                    .then(|| m.expr("const", json!({"name": *rng.pick(&alts), "us": p["us"]})))
            },
            None,
        );
    }
    let headed = |e: u64, _| {
        if seed.ekind(e) != "app" {
            return false;
        }
        let mut h = e;
        while seed.ekind(h) == "app" {
            h = u(&seed.expr(h).1["fn"]);
        }
        is_q(h)
    };
    let pool: Vec<u64> = all_positions(seed, d, 1500, rng)
        .into_iter()
        .map(|p| p.1)
        .collect();
    replace_at(
        seed,
        m,
        rng,
        d,
        &headed,
        &mut |m, rng, e, depth| {
            let p = &seed.expr(e).1;
            let cands: Vec<u64> = pool
                .iter()
                .copied()
                .filter(|&x| x != u(&p["arg"]) && seed.lbr(x) <= depth)
                .collect();
            (!cands.is_empty())
                .then(|| m.expr("app", json!({"fn": p["fn"], "arg": *rng.pick(&cands)})))
        },
        None,
    )
}

// ---------------------------------------------------------------------------
// let-bindings, binders, de Bruijn indices

fn op_let(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    let has_let = decl_roots(&d.kind, &d.payload).iter().any(|r| {
        positions(seed, r.expr, 2000, None)
            .iter()
            .any(|p| seed.ekind(p.1) == "letE")
    });
    if !has_let {
        return op_let_intro(seed, m, rng, d);
    }
    replace_at(
        seed,
        m,
        rng,
        d,
        &is_kind(seed, "letE"),
        &mut |m, rng, e, depth| {
            let mut p = seed.expr(e).1.clone();
            match rng.below(5) {
                0 => {
                    if seed.lbr(u(&p["value"])) > depth {
                        return None;
                    }
                    let (t, v) = (p["type"].clone(), p["value"].clone());
                    p["type"] = v;
                    p["value"] = t;
                }
                1 => p["nondep"] = json!(!p["nondep"].as_bool().unwrap_or(false)),
                2 => {
                    let b = m.lift(u(&p["body"]), 1, 1);
                    p["body"] = json!(b);
                }
                3 => {
                    let b = u(&p["body"]);
                    return (seed.lbr(b) <= depth).then_some(b);
                }
                _ => {
                    let q = positions(seed, u(&p["value"]), 200, Some(rng));
                    let alts: Vec<u64> = q
                        .iter()
                        .filter(|(_, x, dd)| {
                            *dd == 0 && *x != u(&p["value"]) && seed.lbr(*x) <= depth
                        })
                        .map(|x| x.1)
                        .collect();
                    if alts.is_empty() {
                        return None;
                    }
                    p["value"] = json!(*rng.pick(&alts));
                }
            }
            Some(m.expr("letE", p))
        },
        None,
    )
}

/// `n` becomes `let x : Nat := n; x` (accept), or `let x : Nat := n+1; x`.
fn op_let_intro(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    let Some(nat) = seed.name_before("Nat", m.line) else {
        return false;
    };
    let mut good = false;
    let ok = replace_at(
        seed,
        m,
        rng,
        d,
        &is_kind(seed, "natVal"),
        &mut |m, rng, e, _| {
            let t = m.expr("const", json!({"name": nat, "us": []}));
            good = rng.chance(0.5);
            let val = if good {
                e
            } else {
                let n = seed.expr(e).1.as_str().unwrap_or("0").to_string();
                m.expr("natVal", json!(dec_add(&n, "1")))
            };
            let x = m.name("fuzz_x");
            let b = m.expr("bvar", json!(0));
            Some(m.expr(
                "letE",
                json!({"name": x, "type": t, "value": val, "body": b, "nondep": false}),
            ))
        },
        None,
    );
    if ok && good {
        m.expect = "accept";
    }
    ok
}

fn op_bvar(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    replace_at(
        seed,
        m,
        rng,
        d,
        &is_kind(seed, "bvar"),
        &mut |m, rng, e, depth| {
            let i = u(&seed.expr(e).1);
            let j = match rng.below(4) {
                0 => Some(i + 1),
                1 => i.checked_sub(1),
                2 if depth > 0 => Some(rng.below(depth as usize) as u64),
                _ => Some(depth + *rng.pick(&[0, 1, 1 << 32])),
            }?;
            (j != i).then(|| m.expr("bvar", json!(j)))
        },
        None,
    )
}

fn op_binder(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    let pool = all_positions(seed, d, 1500, rng);
    replace_at(
        seed,
        m,
        rng,
        d,
        &|e, _| matches!(seed.ekind(e), "lam" | "forallE"),
        &mut |m, rng, e, depth| {
            let (k, p) = seed.expr(e).clone();
            if rng.chance(0.4) {
                return Some(m.expr(if k == "lam" { "forallE" } else { "lam" }, p));
            }
            let cands: Vec<Value> = pool
                .iter()
                .filter(|(_, x, _)| matches!(seed.ekind(*x), "lam" | "forallE"))
                .map(|(_, x, _)| seed.expr(*x).1["type"].clone())
                .filter(|t| seed.lbr(u(t)) <= depth && *t != p["type"])
                .collect();
            if cands.is_empty() {
                return None;
            }
            let mut q = p;
            q["type"] = rng.pick(&cands).clone();
            Some(m.expr(&k, q))
        },
        None,
    )
}

/// Equivalent: a binder name or binder info changed, or an mdata node inserted (accept).
fn op_cosmetic(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    m.expect = "accept";
    replace_at(
        seed,
        m,
        rng,
        d,
        &|_, _| true,
        &mut |m, rng, e, _| {
            let (k, p) = seed.expr(e).clone();
            let binder = matches!(k.as_str(), "lam" | "forallE");
            match rng.below(3) {
                0 if binder || k == "letE" => {
                    let mut q = p;
                    q["name"] = json!(m.name("fuzz_renamed"));
                    Some(m.expr(&k, q))
                }
                1 if binder => {
                    let bis: Vec<&str> = ["default", "implicit", "strictImplicit", "instImplicit"]
                        .into_iter()
                        .filter(|b| p["binderInfo"] != json!(b))
                        .collect();
                    let mut q = p;
                    q["binderInfo"] = json!(*rng.pick(&bis));
                    Some(m.expr(&k, q))
                }
                _ => Some(m.expr("mdata", json!({"data": {}, "expr": e}))),
            }
        },
        None,
    )
}

// ---------------------------------------------------------------------------
// definitional heights, reducibility hints, declaration kinds

fn op_hints(_seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    if d.kind != "def" {
        return false;
    }
    let mut p = d.payload.clone();
    let h = p["hints"].clone();
    p["hints"] = match rng.below(5) {
        0 => json!("abbrev"),
        1 => json!("opaque"),
        2 if h.get("regular").is_some() => {
            let r = u(&h["regular"]) as i64 + *rng.pick(&[-1i64, 1, -100, 1000]);
            json!({"regular": r.max(0)})
        }
        3 => json!({"regular": *rng.pick(&[0u64, 1, (1 << 32) - 1])}),
        _ => json!({"regular": (1u64 << 32) + 1}),
    };
    if p["hints"] == h {
        return false;
    }
    m.expect = "accept";
    m.set_decl(&d.kind, p);
    true
}

fn keep_fields(p: &Value, fields: &[&str]) -> Value {
    let mut o = serde_json::Map::new();
    for f in fields {
        if let Some(v) = p.get(*f) {
            o.insert(f.to_string(), v.clone());
        }
    }
    Value::Object(o)
}

fn op_decl_kind(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    if matches!(d.kind.as_str(), "inductive" | "quot") {
        return false;
    }
    let base = ["name", "levelParams", "type", "value", "all"];
    let mut p = d.payload.clone();
    let k = d.kind.as_str();
    let new_kind = match rng.below(6) {
        0 if k == "def" || k == "opaque" => {
            p = keep_fields(&p, &base);
            "thm"
        }
        1 if k == "thm" => {
            p["hints"] = json!({"regular": 1});
            p["safety"] = json!("safe");
            "def"
        }
        2 if k == "def" || k == "thm" => {
            p = keep_fields(&p, &base);
            p["isUnsafe"] = json!(false);
            "opaque"
        }
        3 if k == "def" => {
            let s: Vec<&str> = ["safe", "unsafe", "partial"]
                .into_iter()
                .filter(|s| p["safety"] != json!(s))
                .collect();
            p["safety"] = json!(*rng.pick(&s));
            "def"
        }
        4 if p.get("all").is_some() => {
            let names: Vec<(&String, u64)> = sorted_consts(seed)
                .into_iter()
                .map(|(c, (_, _, x))| (c, u(&x["name"])))
                .collect();
            if rng.chance(0.5) && !names.is_empty() {
                let extra = rng.pick(&names).1;
                p["all"].as_array_mut().unwrap().push(json!(extra));
            } else {
                p["all"] = json!([]);
            }
            k
        }
        5 if k == "thm" || k == "def" => {
            // an axiom is always fine to the kernel when nothing after it reduces it
            p = keep_fields(&p, &["name", "levelParams", "type"]);
            p["isUnsafe"] = json!(false);
            m.truncate = true;
            m.expect = "accept";
            "axiom"
        }
        _ => return false,
    };
    if new_kind == k && p == d.payload {
        return false;
    }
    m.note = format!("{k} -> {new_kind}");
    m.set_decl(new_kind, p);
    true
}

// ---------------------------------------------------------------------------
// kernel computation

const SWAP_GROUPS: &[&[&str]] = &[
    &[
        "Nat.add",
        "Nat.sub",
        "Nat.mul",
        "Nat.div",
        "Nat.mod",
        "Nat.gcd",
        "Nat.land",
        "Nat.lor",
        "Nat.xor",
        "Nat.shiftLeft",
        "Nat.shiftRight",
        "Nat.pow",
    ],
    &["Nat.beq", "Nat.ble"],
    &["Bool.true", "Bool.false"],
    &["Nat.succ", "Nat.pred", "Nat.log2"],
    &["instHAdd", "instHSub", "instHMul", "instHDiv", "instHMod"],
    &[
        "HAdd.hAdd",
        "HSub.hSub",
        "HMul.hMul",
        "HDiv.hDiv",
        "HMod.hMod",
    ],
    &[
        "instAddNat",
        "instSubNat",
        "instMulNat",
        "Nat.instDiv",
        "Nat.instMod",
    ],
    &["Array.push", "Array.pop"],
    &["Array.size", "Array.toList"],
    &["List.cons", "List.nil"],
    &["And.intro", "Or.inl", "Or.inr"],
    &["Decidable.isTrue", "Decidable.isFalse"],
    &["True", "False"],
    &["Eq.refl", "rfl"],
    &["List.foldl", "List.foldr"],
    &["Array.foldl", "Array.foldr"],
    &["instDecidableEqNat", "Nat.decEq"],
    &["Nat.decLe", "Nat.decLt"],
    &["Nat.lt", "Nat.le"],
    &["LT.lt", "LE.le"],
    &["instLTNat", "instLENat"],
];

fn op_eval_const(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    let mut group_of: HashMap<u64, Vec<u64>> = HashMap::new();
    for g in SWAP_GROUPS {
        let ids: Vec<u64> = g
            .iter()
            .filter_map(|n| seed.name_before(n, m.line))
            .collect();
        for &i in &ids {
            group_of.insert(i, ids.iter().copied().filter(|&j| j != i).collect());
        }
    }
    let pred = |e: u64, _| {
        seed.ekind(e) == "const"
            && group_of
                .get(&u(&seed.expr(e).1["name"]))
                .is_some_and(|g| !g.is_empty())
    };
    replace_at(
        seed,
        m,
        rng,
        d,
        &pred,
        &mut |m, rng, e, _| {
            let p = &seed.expr(e).1;
            let alts = &group_of[&u(&p["name"])];
            Some(m.expr("const", json!({"name": *rng.pick(alts), "us": p["us"]})))
        },
        None,
    )
}

/// A number in a computation theorem's statement changed; its proof stays `rfl`/`decide`.
fn op_eval_statement(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    if d.kind != "thm" {
        return false;
    }
    if rng.chance(0.7) {
        return op_nat_lit_in(seed, m, rng, d, Some(&["type"]));
    }
    op_eval_const(seed, m, rng, d)
}

/// A number or an operation changed in a definition a computation runs through.
fn op_eval_value(seed: &Seed, m: &mut Mutant, rng: &mut Rng, d: &Decl) -> bool {
    if !matches!(d.kind.as_str(), "def" | "thm") {
        return false;
    }
    if rng.chance(0.6) {
        return op_nat_lit_in(seed, m, rng, d, Some(&["value"]));
    }
    op_eval_const(seed, m, rng, d)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decimal_helpers() {
        assert_eq!(dec_add("18446744073709551615", "1"), "18446744073709551616");
        assert_eq!(dec_pred("1000"), "999");
        assert_eq!(dec_pred("1"), "0");
        assert_eq!(dec_half("18446744073709551616"), "9223372036854775808");
        assert_eq!(dec_half("1"), "0");
    }
}
