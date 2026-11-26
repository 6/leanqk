//! The kernel's built-in extensions: `Nat` and `String` literals, `Nat`
//! arithmetic on literals (GMP-accelerated in Lean, `num-bigint` here),
//! quotients and `eagerReduce`.
//!
//! Deliberate divergence from Lean: Lean's kernel recognizes these by name
//! alone, so an environment with its own `Nat.add` gets Lean's arithmetic
//! for it. Here each one is enabled only if the environment's declarations
//! are structurally the expected ones (see `fingerprint.rs`): literals
//! need the prelude's `Nat` (or `String`, `Char`, `List`) with their
//! expected types, and each arithmetic operation needs its prelude
//! definition, compared with the one of a known Lean version (v4.36.0,
//! v4.34.0 or v4.30.0) across everything it depends on. Otherwise the operation is
//! just its definition, and a literal of a type that is not the expected
//! one is rejected.

use crate::env::{Decl, DeclKind, Env};
use crate::expr::{ExprId, ExprNode};
use crate::level::{LevelId, LevelNode};
use crate::name::NameId;

use super::fingerprint;
use super::store::IdMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NatOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Gcd,
    Beq,
    Ble,
    Land,
    Lor,
    Xor,
    ShiftLeft,
    ShiftRight,
    Pow,
}

/// Whether the checkers compute `Nat` operations on literals below 2^64
/// without `BigUint` (`NatOp::small`).
pub const SMALL_NAT: bool = true;

/// The result of `NatOp::small`.
pub enum SmallNat {
    Nat(u64),
    Bool(bool),
}

impl NatOp {
    /// The operation on two numbers below 2^64, when its result is one too
    /// (or a `Bool`). It is what the `BigUint` path gives; `None` leaves
    /// the operation to that path (a result past 2^64, `Nat.pow` and
    /// `Nat.shiftLeft` beyond it), which also decides the kernel's limits,
    /// none of which a result below 2^64 reaches.
    pub fn small(self, x: u64, y: u64) -> Option<SmallNat> {
        use SmallNat::{Bool, Nat};
        Some(match self {
            NatOp::Add => Nat(x.checked_add(y)?),
            NatOp::Sub => Nat(x.saturating_sub(y)),
            NatOp::Mul => Nat(x.checked_mul(y)?),
            NatOp::Div => Nat(x.checked_div(y).unwrap_or(0)),
            NatOp::Mod => Nat(if y == 0 { x } else { x % y }),
            NatOp::Gcd => {
                let (mut a, mut b) = (x, y);
                while b != 0 {
                    (a, b) = (b, a % b);
                }
                Nat(a)
            }
            NatOp::Beq => Bool(x == y),
            NatOp::Ble => Bool(x <= y),
            NatOp::Land => Nat(x & y),
            NatOp::Lor => Nat(x | y),
            NatOp::Xor => Nat(x ^ y),
            NatOp::ShiftLeft => {
                if x == 0 {
                    Nat(0)
                } else if y < 64 && (x << y) >> y == x {
                    Nat(x << y)
                } else {
                    return None;
                }
            }
            NatOp::ShiftRight => Nat(if y < 64 { x >> y } else { 0 }),
            NatOp::Pow => Nat(x.checked_pow(u32::try_from(y).ok()?)?),
        })
    }
}

pub const NAT_OPS: [(&str, NatOp); 14] = [
    ("Nat.add", NatOp::Add),
    ("Nat.sub", NatOp::Sub),
    ("Nat.mul", NatOp::Mul),
    ("Nat.div", NatOp::Div),
    ("Nat.mod", NatOp::Mod),
    ("Nat.gcd", NatOp::Gcd),
    ("Nat.beq", NatOp::Beq),
    ("Nat.ble", NatOp::Ble),
    ("Nat.land", NatOp::Land),
    ("Nat.lor", NatOp::Lor),
    ("Nat.xor", NatOp::Xor),
    ("Nat.shiftLeft", NatOp::ShiftLeft),
    ("Nat.shiftRight", NatOp::ShiftRight),
    ("Nat.pow", NatOp::Pow),
];

/// `Array` operations the closed-term evaluator (`eval/`) runs on vectors.
/// They are not kernel rules: each is enabled only if its definition (and
/// everything it depends on) is a known prelude's, so running it on a
/// vector gives what unfolding the definition gives.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ArrayOp {
    /// `Array.size a = a.toList.length`
    Size,
    /// `Array.getInternal a i h = a.toList.get ⟨i, h⟩`
    Get,
    /// `Array.set xs i v h = ⟨xs.toList.set i v⟩`
    Set,
    /// `Array.push a v = ⟨a.toList.concat v⟩`
    Push,
}

pub const ARRAY_OPS: [(&str, ArrayOp); 4] = [
    ("Array.size", ArrayOp::Size),
    ("Array.getInternal", ArrayOp::Get),
    ("Array.set", ArrayOp::Set),
    ("Array.push", ArrayOp::Push),
];

/// `List` operations the evaluator runs as loops over list values, without
/// the structural recursion (`List.brecOn`, `List.rec`) their definitions
/// compile to. Enabled like `ARRAY_OPS`, on definitions that are a known
/// prelude's; every known version computes the same function.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ListOp {
    /// `List.any l p`: `p` on the elements until one is `true`
    Any,
    /// `List.all l p`: `p` on the elements until one is `false`
    All,
    /// `List.filter p l`: up to the first element kept; the rest stays lazy
    Filter,
    /// `List.reverseAux l r`: `l` reversed onto `r`
    ReverseAux,
    /// `List.foldl f a l`: `f (… (f a x₀) …) xₙ₋₁`, built lazily, then forced
    Foldl,
    /// `List.getLast l h`: the last element
    GetLast,
    /// `List.elem a l` (with a `BEq` instance): `a == x` on the elements
    /// until one is `true`
    Elem,
    /// `List.eraseDupsBy.loop r l acc`: the elements `x` of `l` with no
    /// `r x y` among those kept before, pushed onto `acc`, then reversed
    EraseDupsLoop,
    /// `List.map f l`: the first cell, `f x :: map f t`, lazily
    Map,
    /// `List.zipWith f l₁ l₂`: the first cell, lazily
    ZipWith,
    /// `List.append l₁ l₂`: the first cell, lazily
    Append,
    /// `List.length l`
    Length,
}

pub const LIST_OPS: [(&str, ListOp); 12] = [
    ("List.any", ListOp::Any),
    ("List.all", ListOp::All),
    ("List.filter", ListOp::Filter),
    ("List.reverseAux", ListOp::ReverseAux),
    ("List.foldl", ListOp::Foldl),
    ("List.getLast", ListOp::GetLast),
    ("List.elem", ListOp::Elem),
    ("List.eraseDupsBy.loop", ListOp::EraseDupsLoop),
    ("List.map", ListOp::Map),
    ("List.zipWith", ListOp::ZipWith),
    ("List.append", ListOp::Append),
    ("List.length", ListOp::Length),
];

/// `DecidableEq` instances of the core library that the evaluator decides
/// on values: it runs the comparison and builds `isTrue`/`isFalse` without
/// the matches and the proof terms of the definition (the proof is left
/// erased, see `docs/kernel-compute.md`). They are enabled only for the
/// versions in `DEC_EQ_VERSIONS`, in which `Decidable` is the inductive type
/// with `isTrue` and `isFalse` (from v4.36.0 it is a structure with a
/// `Bool` field, and these instances are already cheap).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DecEqOp {
    /// `Nat.decEq n m`, on literals
    Nat,
    /// `Bool.decEq a b`
    Bool,
    /// `instDecidableEqProd dα dβ x y`: the first components, then the second
    Prod,
    /// `Subtype.instDecidableEq dα x y`: the values
    Subtype,
}

pub const DEC_EQ_OPS: [(&str, DecEqOp); 4] = [
    ("Nat.decEq", DecEqOp::Nat),
    ("Bool.decEq", DecEqOp::Bool),
    ("instDecidableEqProd", DecEqOp::Prod),
    ("Subtype.instDecidableEq", DecEqOp::Subtype),
];

/// `Int` operations the evaluator runs on values `Int.ofNat n` and
/// `Int.negSucc n` with literal `n`, by the case analysis of their
/// definitions with the kernel's `Nat` operations. The definitions are the
/// same in every known version. Enabled like `LIST_OPS`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IntOp {
    Add,
    Sub,
    Mul,
    Neg,
    /// Euclidean division and remainder (`/` and `%` on `Int`)
    Ediv,
    Emod,
    /// Division and remainder rounding toward zero
    Tdiv,
    Tmod,
    Pow,
    SubNatNat,
    NegOfNat,
    NatAbs,
    ToNat,
}

pub const INT_OPS: [(&str, IntOp); 13] = [
    ("Int.add", IntOp::Add),
    ("Int.sub", IntOp::Sub),
    ("Int.mul", IntOp::Mul),
    ("Int.neg", IntOp::Neg),
    ("Int.ediv", IntOp::Ediv),
    ("Int.emod", IntOp::Emod),
    ("Int.tdiv", IntOp::Tdiv),
    ("Int.tmod", IntOp::Tmod),
    ("Int.pow", IntOp::Pow),
    ("Int.subNatNat", IntOp::SubNatNat),
    ("Int.negOfNat", IntOp::NegOfNat),
    ("Int.natAbs", IntOp::NatAbs),
    ("Int.toNat", IntOp::ToNat),
];

/// `instBEqProd`, whose `==` the evaluator runs on pairs: `(a₁, b₁) ==
/// (a₂, b₂)` is `a₁ == a₂ && b₁ == b₂`. Enabled like `LIST_OPS`.
pub const BEQ_PROD: &str = "instBEqProd";

pub const DEC_EQ_VERSIONS: [&str; 2] = ["v4.34.0", "v4.30.0"];

/// The inductive types and constructors the `List` and `DecidableEq`
/// operations look at. They are in the cones the fingerprints cover.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FastNames {
    pub list: NameId,
    pub list_nil: NameId,
    pub list_cons: NameId,
    pub prod: Option<NameId>,
    pub subtype: Option<NameId>,
    pub decidable: Option<NameId>,
    pub beq: Option<NameId>,
    pub int: Option<NameId>,
    pub int_of_nat: Option<NameId>,
    pub int_neg_succ: Option<NameId>,
    pub is_true: Option<NameId>,
    pub is_false: Option<NameId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StrExt {
    pub string: NameId,
    pub of_list: NameId,
    pub char: NameId,
    pub char_of_nat: NameId,
    pub list_cons: NameId,
    pub list_nil: NameId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct QuotNames {
    pub quot: NameId,
    pub mk: NameId,
    pub lift: NameId,
    pub ind: NameId,
}

#[derive(Default, Debug, PartialEq, Eq)]
pub struct Ext {
    pub nat: Option<NameId>,
    pub nat_zero: Option<NameId>,
    pub nat_succ: Option<NameId>,
    pub bool_true: Option<NameId>,
    pub bool_false: Option<NameId>,
    pub ops: IdMap<NameId, NatOp>,
    pub nat_ops_complete: bool,
    pub array_ops: IdMap<NameId, ArrayOp>,
    pub list_ops: IdMap<NameId, ListOp>,
    pub dec_eq_ops: IdMap<NameId, DecEqOp>,
    pub fast: Option<FastNames>,
    pub beq_prod: Option<NameId>,
    pub int_ops: IdMap<NameId, IntOp>,
    pub strings: Option<StrExt>,
    pub eager_reduce: Option<NameId>,
    pub quot: Option<QuotNames>,
    pub eq: Option<NameId>,
    /// Why an extension is off, for `--stats`.
    pub notes: Vec<String>,
}

impl Ext {
    pub fn string(&self) -> Option<&StrExt> {
        self.strings.as_ref()
    }

    #[inline]
    pub fn nat_op(&self, n: NameId) -> Option<NatOp> {
        if self.ops.is_empty() {
            return None;
        }
        self.ops.get(&n).copied()
    }

    pub fn new(env: &Env) -> Ext {
        Self::with_decls(env, &env.decls)
    }

    pub(super) fn with_decls(env: &Env, decls: &[Decl]) -> Ext {
        let mut x = Ext {
            eager_reduce: env.names.find_dotted("eagerReduce"),
            eq: env.names.find_dotted("Eq"),
            ..Ext::default()
        };
        let q = |s| env.names.find_dotted(s);
        if let (Some(quot), Some(mk), Some(lift), Some(ind)) =
            (q("Quot"), q("Quot.mk"), q("Quot.lift"), q("Quot.ind"))
        {
            x.quot = Some(QuotNames {
                quot,
                mk,
                lift,
                ind,
            });
        }
        let shapes = Shapes { env, decls };
        let Some((nat, zero, succ)) = shapes.nat() else {
            x.notes.push(
                "no `Nat` literals: `Nat` is absent or not the expected inductive type".into(),
            );
            return x;
        };
        x.nat = Some(nat);
        x.nat_zero = Some(zero);
        x.nat_succ = Some(succ);
        let bool_ok = shapes.bool_type();
        if let Some((f, t)) = bool_ok {
            x.bool_false = Some(f);
            x.bool_true = Some(t);
        }
        let fp = fingerprint::Checker::with_decls(env, decls);
        let mut recognized_ops = 0;
        for (name, op) in NAT_OPS {
            let Some(n) = env.names.find_dotted(name) else {
                continue;
            };
            let pred = matches!(op, NatOp::Beq | NatOp::Ble);
            if pred && bool_ok.is_none() {
                x.notes.push(format!(
                    "no built-in `{name}`: `Bool` is not the expected inductive type"
                ));
                continue;
            }
            match fp.matches(n) {
                Ok(_) => {
                    x.ops.insert(n, op);
                    recognized_ops += 1;
                }
                Err(why) => x.notes.push(format!("no built-in `{name}`: {why}")),
            }
        }
        x.nat_ops_complete = recognized_ops == NAT_OPS.len();
        for (name, op) in ARRAY_OPS {
            let Some(n) = env.names.find_dotted(name) else {
                continue;
            };
            match fp.matches(n) {
                Ok(_) => {
                    x.array_ops.insert(n, op);
                }
                Err(why) => x
                    .notes
                    .push(format!("no fast `{name}` in the evaluator: {why}")),
            }
        }
        let f = |s| env.names.find_dotted(s);
        if let (Some(list), Some(list_nil), Some(list_cons)) =
            (f("List"), f("List.nil"), f("List.cons"))
        {
            x.fast = Some(FastNames {
                list,
                list_nil,
                list_cons,
                prod: f("Prod"),
                subtype: f("Subtype"),
                decidable: f("Decidable"),
                beq: f("BEq"),
                int: f("Int"),
                int_of_nat: f("Int.ofNat"),
                int_neg_succ: f("Int.negSucc"),
                is_true: f("Decidable.isTrue"),
                is_false: f("Decidable.isFalse"),
            });
            for (name, op) in LIST_OPS {
                let Some(n) = f(name) else {
                    continue;
                };
                match fp.matches(n) {
                    Ok(_) => {
                        x.list_ops.insert(n, op);
                    }
                    Err(why) => x
                        .notes
                        .push(format!("no fast `{name}` in the evaluator: {why}")),
                }
            }
            for (name, op) in INT_OPS {
                let Some(n) = f(name) else {
                    continue;
                };
                match fp.matches(n) {
                    Ok(_) => {
                        x.int_ops.insert(n, op);
                    }
                    Err(why) => x
                        .notes
                        .push(format!("no fast `{name}` in the evaluator: {why}")),
                }
            }
            if let Some(n) = f(BEQ_PROD) {
                match fp.matches(n) {
                    Ok(_) => x.beq_prod = Some(n),
                    Err(why) => x
                        .notes
                        .push(format!("no fast `{BEQ_PROD}` in the evaluator: {why}")),
                }
            }
            let want = fingerprint::version_mask(&DEC_EQ_VERSIONS);
            for (name, op) in DEC_EQ_OPS {
                let Some(n) = f(name) else {
                    continue;
                };
                match fp.matches(n) {
                    Ok(m) if m & want != 0 && bool_ok.is_some() => {
                        x.dec_eq_ops.insert(n, op);
                    }
                    Ok(_) => x.notes.push(format!(
                        "no fast `{name}` in the evaluator: only for {}",
                        DEC_EQ_VERSIONS.join(", ")
                    )),
                    Err(why) => x
                        .notes
                        .push(format!("no fast `{name}` in the evaluator: {why}")),
                }
            }
        }
        match shapes.strings(nat) {
            Some(s) => x.strings = Some(s),
            None => x.notes.push(
                "no `String` literals: `String`, `String.ofList`, `Char.ofNat` or `List` is absent or not as expected".into(),
            ),
        }
        x
    }
}

/// Structural checks on declaration types, by name.
struct Shapes<'a> {
    env: &'a Env,
    decls: &'a [Decl],
}

impl Shapes<'_> {
    fn find(&self, n: NameId) -> Option<&Decl> {
        self.env.by_name.get(&n).map(|i| &self.decls[i as usize])
    }

    fn decl(&self, s: &str) -> Option<(NameId, &Decl)> {
        let n = self.env.names.find_dotted(s)?;
        Some((n, self.find(n)?))
    }

    fn is_const(&self, e: ExprId, n: NameId, nlevels: usize) -> bool {
        matches!(self.env.exprs.get(e), ExprNode::Const(m, ls) if m == n && self.env.levels.list(ls).len() == nlevels)
    }

    fn is_sort(&self, e: ExprId, succs: u32) -> bool {
        let ExprNode::Sort(mut l) = self.env.exprs.get(e) else {
            return false;
        };
        for _ in 0..succs {
            match self.env.levels.get(l) {
                LevelNode::Succ(a) => l = a,
                _ => return false,
            }
        }
        l == LevelId::ZERO
    }

    /// `e` is `a → b` (non-dependent).
    fn arrow(&self, e: ExprId) -> Option<(ExprId, ExprId)> {
        match self.env.exprs.get(e) {
            ExprNode::Pi(_, _, a, b) if self.env.exprs.data(b).loose_bvar_range() == 0 => {
                Some((a, b))
            }
            _ => None,
        }
    }

    /// An inductive type `n : Type` with no parameters or indices and the
    /// constructors `ctors`, each of a type accepted by `ok`.
    fn simple_inductive(&self, name: &str, ctors: &[&str]) -> Option<(NameId, Vec<NameId>)> {
        let (n, d) = self.decl(name)?;
        let DeclKind::Inductive {
            num_params: 0,
            num_indices: 0,
            ctors: cs,
            is_unsafe: false,
            ..
        } = d.kind
        else {
            return None;
        };
        if !d.level_params.is_empty() || !self.is_sort(d.ty, 1) {
            return None;
        }
        let cs = self.env.name_list(cs);
        if cs.len() != ctors.len() {
            return None;
        }
        let mut out = Vec::new();
        for (&c, want) in cs.iter().zip(ctors) {
            if self.env.names.find_dotted(want) != Some(c) {
                return None;
            }
            out.push(c);
        }
        Some((n, out))
    }

    fn nat(&self) -> Option<(NameId, NameId, NameId)> {
        let (nat, cs) = self.simple_inductive("Nat", &["Nat.zero", "Nat.succ"])?;
        let zero = self.find(cs[0])?;
        let succ = self.find(cs[1])?;
        if !self.is_const(zero.ty, nat, 0) {
            return None;
        }
        let (a, b) = self.arrow(succ.ty)?;
        if !self.is_const(a, nat, 0) || !self.is_const(b, nat, 0) {
            return None;
        }
        Some((nat, cs[0], cs[1]))
    }

    fn bool_type(&self) -> Option<(NameId, NameId)> {
        let (b, cs) = self.simple_inductive("Bool", &["Bool.false", "Bool.true"])?;
        for &c in &cs {
            if !self.is_const(self.find(c)?.ty, b, 0) {
                return None;
            }
        }
        Some((cs[0], cs[1]))
    }

    fn strings(&self, nat: NameId) -> Option<StrExt> {
        // `List.{u} (α : Type u) : Type u` with `nil` and `cons`.
        let (list, ld) = self.decl("List")?;
        let DeclKind::Inductive {
            num_params: 1,
            num_indices: 0,
            ctors,
            is_unsafe: false,
            ..
        } = ld.kind
        else {
            return None;
        };
        let cs = self.env.name_list(ctors);
        let nil = self.env.names.find_dotted("List.nil")?;
        let cons = self.env.names.find_dotted("List.cons")?;
        if cs != [nil, cons] || ld.level_params.len() != 1 {
            return None;
        }
        // `Char : Type`, `Char.ofNat : Nat → Char`, `String : Type`,
        // `String.ofList : List Char → String`.
        let (ch, chd) = self.decl("Char")?;
        if !chd.level_params.is_empty() || !self.is_sort(chd.ty, 1) {
            return None;
        }
        let (of_nat, ond) = self.decl("Char.ofNat")?;
        let (a, b) = self.arrow(ond.ty)?;
        if !ond.level_params.is_empty() || !self.is_const(a, nat, 0) || !self.is_const(b, ch, 0) {
            return None;
        }
        let (string, sd) = self.decl("String")?;
        if !sd.level_params.is_empty() || !self.is_sort(sd.ty, 1) {
            return None;
        }
        let (of_list, old) = self.decl("String.ofList")?;
        let (a, b) = self.arrow(old.ty)?;
        if !old.level_params.is_empty() || !self.is_const(b, string, 0) {
            return None;
        }
        // `a` is `List.{0} Char`.
        let ExprNode::App(f, x) = self.env.exprs.get(a) else {
            return None;
        };
        let ExprNode::Const(l, ls) = self.env.exprs.get(f) else {
            return None;
        };
        if l != list || self.env.levels.list(ls) != [LevelId::ZERO] || !self.is_const(x, ch, 0) {
            return None;
        }
        // The constructors of `List` were checked with the inductive block.
        Some(StrExt {
            string,
            of_list,
            char: ch,
            char_of_nat: of_nat,
            list_cons: cons,
            list_nil: nil,
        })
    }
}

#[cfg(test)]
mod small_nat_tests {
    use super::{NatOp, SmallNat};
    use num_bigint::BigUint;

    /// What the checkers' `BigUint` paths compute, without the size limits
    /// (no result below 2^64 reaches them).
    fn big(op: NatOp, x: u64, y: u64) -> Option<SmallNat> {
        let (a, b) = (BigUint::from(x), BigUint::from(y));
        let z = BigUint::ZERO;
        let r = match op {
            NatOp::Add => a + b,
            NatOp::Sub => {
                if a >= b {
                    a - b
                } else {
                    z
                }
            }
            NatOp::Mul => a * b,
            NatOp::Div => {
                if b == z {
                    z
                } else {
                    a / b
                }
            }
            NatOp::Mod => {
                if b == z {
                    a
                } else {
                    a % b
                }
            }
            NatOp::Gcd => {
                let (mut a, mut b) = (a, b);
                while b != BigUint::ZERO {
                    let r = &a % &b;
                    a = b;
                    b = r;
                }
                a
            }
            NatOp::Beq => return Some(SmallNat::Bool(a == b)),
            NatOp::Ble => return Some(SmallNat::Bool(a <= b)),
            NatOp::Land => a & b,
            NatOp::Lor => a | b,
            NatOp::Xor => a ^ b,
            // Past 2^128: not small, and too large to compute here.
            NatOp::Pow if x > 1 && y > 128 => return None,
            NatOp::Pow => a.pow(u32::try_from(y).ok()?),
            NatOp::ShiftLeft => {
                if x == 0 {
                    z
                } else if y > 128 {
                    return None;
                } else {
                    a << u32::try_from(y).ok()?
                }
            }
            NatOp::ShiftRight => match u64::try_from(&b) {
                Ok(k) if k < a.bits() => a >> k,
                _ => z,
            },
        };
        u64::try_from(&r).ok().map(SmallNat::Nat)
    }

    #[test]
    fn small_agrees_with_big() {
        let ops = [
            NatOp::Add,
            NatOp::Sub,
            NatOp::Mul,
            NatOp::Div,
            NatOp::Mod,
            NatOp::Gcd,
            NatOp::Beq,
            NatOp::Ble,
            NatOp::Land,
            NatOp::Lor,
            NatOp::Xor,
            NatOp::ShiftLeft,
            NatOp::ShiftRight,
            NatOp::Pow,
        ];
        let xs = [
            0,
            1,
            2,
            3,
            7,
            63,
            64,
            65,
            1000,
            u32::MAX as u64,
            u32::MAX as u64 + 1,
            u64::MAX / 3,
            u64::MAX - 1,
            u64::MAX,
        ];
        for op in ops {
            for &x in &xs {
                for &y in &xs {
                    let s = op.small(x, y);
                    let b = big(op, x, y);
                    let same = match (&s, &b) {
                        (Some(SmallNat::Nat(p)), Some(SmallNat::Nat(q))) => p == q,
                        (Some(SmallNat::Bool(p)), Some(SmallNat::Bool(q))) => p == q,
                        // `None`: the `BigUint` path decides.
                        (None, _) => true,
                        _ => false,
                    };
                    assert!(same, "{op:?} {x} {y}");
                    // Only a result past 2^64 (or an operation too large to
                    // compute here) is left to the `BigUint` path.
                    if s.is_none() {
                        assert!(b.is_none(), "{op:?} {x} {y} left to BigUint");
                    }
                }
            }
        }
    }
}
