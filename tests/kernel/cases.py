"""Kernel test cases.  Each case builds one export (a string) from a toolchain `tc`.

Expected verdicts:
  accept  a correct kernel must accept the export
  reject  a correct kernel must reject it
  either  the claims are true but need a resource the kernel may refuse
          (a Nat size limit); accepting and rejecting cleanly are both fine,
          crashing or hanging is not
"""

import json

from exportlib import dumps, empty_export

CASES = []
U32 = 2 ** 32
P64 = 2 ** 64


class Case:
    def __init__(self, id, rule, expected, why, fn):
        self.id, self.rule, self.expected, self.why, self.fn = id, rule, expected, why, fn

    def build(self, tc):
        out = self.fn(tc)
        return out if isinstance(out, str) else out.text()


def case(id, rule, expected, why):
    assert expected in ("accept", "reject", "either")

    def deco(fn):
        CASES.append(Case(id, rule, expected, why, fn))
        return fn
    return deco


def agrees(expected, lean):
    return expected == "either" or expected == lean


# ---------------------------------------------------------------------------
# helpers

def consts_of(t, acc):
    if isinstance(t, tuple):
        acc.add(t[0])
        for a in t[1:]:
            consts_of(a, acc)
    elif isinstance(t, str):
        acc.add(t)
    return acc


def term(e, t):
    """ints are Nat literals, strings are constants, tuples are applications."""
    if isinstance(t, bool):
        raise TypeError(t)
    if isinstance(t, int):
        return e.nat(t)
    if isinstance(t, str):
        return e.const(t)
    return e.app(e.const(t[0]), *[term(e, a) for a in t[1:]])


def eq(e, T, a, b):
    return e.app(e.const("Eq", [e.lsucc(0)]), T, a, b)


def refl(e, T, a):
    return e.app(e.const("Eq.refl", [e.lsucc(0)]), T, a)


def claim(tc, lhs, rhs, ty="Nat", tweak=None):
    """theorem K.claim : @Eq ty lhs rhs := @Eq.refl ty lhs"""
    cs = consts_of(lhs, set()) | consts_of(rhs, set()) | {"Eq.refl", ty}
    e = tc.export(sorted(cs))
    if tweak:
        tweak(e)
    T = e.const(ty)
    L, R = term(e, lhs), term(e, rhs)
    e.add_thm("K.claim", eq(e, T, L, R), refl(e, T, L))
    return e


def nat_case(id, rule, expected, lhs, rhs, why, ty="Nat"):
    case(id, rule, expected, why)(lambda tc: claim(tc, lhs, rhs, ty))


def drop_sorry(e):
    try:
        e.remove_decl("sorryAx")
    except KeyError:
        pass


def with_rfl(tc, thm, consts=()):
    """Export `thm` and replace its proof by `Eq.refl` (making the statement
    hold only if both sides are definitionally equal)."""
    e = tc.export([thm] + list(consts))
    d = e.decl(thm)
    d["value"] = e.rfl_proof(d["type"])
    drop_sorry(e)
    return e


def as_is(tc, thm, consts=()):
    e = tc.export([thm] + list(consts))
    return e


def ind_record(e, name):
    return e.recs[e.decl_index(name)]["inductive"]


def make_safe(e, name):
    ind = ind_record(e, name)
    for part in ("types", "ctors", "recs"):
        for x in ind[part]:
            x["isUnsafe"] = False


def lower(e, x, cut):
    """Remove de Bruijn index `cut` (at depth 0) from `x`, shifting the ones above it."""
    def fe(i, k, p, d):
        if k == "bvar":
            if p == cut + d:
                raise ValueError("removed binder is still used")
            if p > cut + d:
                return e.bvar(p - 1)
            return i
        return None
    return e.rebuild(x, fe=fe)


def drop_binder(e, ty, k):
    bs, body = e.binders(ty)
    out = bs[:k]
    for j in range(k + 1, len(bs)):
        n, t, bi = bs[j]
        out.append((n, lower(e, t, j - k - 1), bi))
    body = lower(e, body, len(bs) - k - 1)
    return e.close(out, body, kind="forallE")


def replace_sort0(e, x, lvl):
    return e.rebuild(x, fe=lambda i, k, p, d: e.sort(lvl) if k == "sort" and p == 0 else None)


def records(text):
    lines = text.rstrip("\n").split("\n")
    return lines[0], [json.loads(ln) for ln in lines[1:]]


def join(meta, recs):
    return "\n".join([meta] + [r if isinstance(r, str) else dumps(r) for r in recs]) + "\n"


def last_decl(recs, kind="thm"):
    for i in range(len(recs) - 1, -1, -1):
        if kind in recs[i]:
            return i
    raise KeyError(kind)


def triv(tc):
    """Base for malformed-export cases: `theorem K.triv : True := True.intro`."""
    return records(tc.export(["K.triv"]).text())


# ---------------------------------------------------------------------------
# Nat literal extension: wrong answers must be rejected, edge answers accepted

N = "Nat"
B = "Bool"
nat_case("nat-add-wrap64", "nat.add", "reject", ("Nat.add", P64 - 1, 1), 0,
         "2^64-1 + 1 claimed 0: a kernel using machine words wraps around")
nat_case("nat-add-carry64", "nat.add", "accept", ("Nat.add", P64 - 1, 1), P64,
         "carry past 2^64 must give 2^64")
nat_case("nat-add-zero-ctor", "nat.add", "accept", ("Nat.add", "Nat.zero", 0), 0,
         "Nat.zero counts as the literal 0 for the extension")
nat_case("nat-sub-wrap", "nat.sub", "reject", ("Nat.sub", 0, 1), P64 - 1,
         "0 - 1 claimed 2^64-1: Nat subtraction truncates, it does not wrap")
nat_case("nat-sub-trunc", "nat.sub", "accept", ("Nat.sub", 3, 5), 0,
         "truncated subtraction gives 0")
nat_case("nat-sub-big", "nat.sub", "accept", ("Nat.sub", P64, P64 - 1), 1,
         "borrow across the 2^64 boundary")
nat_case("nat-sub-succ-arg", "nat.sub", "accept", ("Nat.sub", ("Nat.succ", 5), 3), 3,
         "Nat.succ of a literal is reduced to a literal before the extension fires")
nat_case("nat-mul-wrap64", "nat.mul", "reject", ("Nat.mul", U32, U32), 0,
         "2^32 * 2^32 claimed 0 (64-bit overflow)")
nat_case("nat-mul-big", "nat.mul", "accept", ("Nat.mul", P64, P64), 2 ** 128,
         "2^64 * 2^64 = 2^128")
nat_case("nat-div-zero", "nat.div", "accept", ("Nat.div", 7, 0), 0, "x / 0 = 0")
nat_case("nat-div-zero-wrong", "nat.div", "reject", ("Nat.div", 7, 0), 7,
         "x / 0 claimed x")
nat_case("nat-div-big-wrong", "nat.div", "reject", ("Nat.div", 2 ** 128, P64), P64 + 1,
         "2^128 / 2^64 claimed 2^64+1")
nat_case("nat-div-big", "nat.div", "accept", ("Nat.div", 2 ** 128 - 1, P64), P64 - 1,
         "floor division of big literals")
nat_case("nat-mod-zero", "nat.mod", "accept", ("Nat.mod", 7, 0), 7, "x % 0 = x")
nat_case("nat-mod-zero-wrong", "nat.mod", "reject", ("Nat.mod", 7, 0), 0,
         "x % 0 claimed 0")
nat_case("nat-mod-big-wrong", "nat.mod", "reject", ("Nat.mod", P64 + 5, P64), 0,
         "(2^64+5) % 2^64 claimed 0 (low-word truncation)")
nat_case("nat-gcd-zero", "nat.gcd", "accept", ("Nat.gcd", 0, 0), 0, "gcd 0 0 = 0")
nat_case("nat-gcd-zero-wrong", "nat.gcd", "reject", ("Nat.gcd", 0, 0), 1,
         "gcd 0 0 claimed 1")
nat_case("nat-gcd-big", "nat.gcd", "accept", ("Nat.gcd", P64, 2 ** 96 * 3), P64,
         "gcd of big literals")
nat_case("nat-gcd-big-wrong", "nat.gcd", "reject", ("Nat.gcd", P64, 2 ** 96 * 3), 3 * P64,
         "gcd of big literals claimed too large")
nat_case("nat-beq-trunc", "nat.beq", "reject", ("Nat.beq", P64, 0), "Bool.true",
         "beq 2^64 0 claimed true (comparing only the low 64 bits)", ty=B)
nat_case("nat-beq-big", "nat.beq", "accept", ("Nat.beq", P64 + 1, P64 + 1), "Bool.true",
         "beq of equal big literals", ty=B)
nat_case("nat-beq-false-wrong", "nat.beq", "reject", ("Nat.beq", 1, 2), "Bool.true",
         "beq 1 2 claimed true", ty=B)
nat_case("nat-ble-trunc", "nat.ble", "reject", ("Nat.ble", P64, 1), "Bool.true",
         "ble 2^64 1 claimed true", ty=B)
nat_case("nat-ble-big", "nat.ble", "accept", ("Nat.ble", P64, P64 + 1), "Bool.true",
         "ble of big literals", ty=B)
nat_case("nat-ble-eq", "nat.ble", "accept", ("Nat.ble", 0, 0), "Bool.true",
         "ble 0 0 = true", ty=B)
nat_case("nat-land-wrong", "nat.land", "reject", ("Nat.land", P64 + 1, 1), 0,
         "land (2^64+1) 1 claimed 0")
nat_case("nat-land-big", "nat.land", "accept", ("Nat.land", P64 + 1, P64 + 3), P64 + 1,
         "land above 2^64")
nat_case("nat-lor-wrong", "nat.lor", "reject", ("Nat.lor", 1, 2), 4, "lor 1 2 claimed 4")
nat_case("nat-lor-big", "nat.lor", "accept", ("Nat.lor", P64, 1), P64 + 1, "lor above 2^64")
nat_case("nat-xor-wrong", "nat.xor", "reject", ("Nat.xor", 5, 5), 10, "xor 5 5 claimed 10")
nat_case("nat-xor-big", "nat.xor", "accept", ("Nat.xor", P64 + 7, P64), 7,
         "xor cancels the high bit")
nat_case("nat-shl-wrap", "nat.shiftLeft", "reject", ("Nat.shiftLeft", 1, 64), 0,
         "1 <<< 64 claimed 0 (64-bit shift)")
nat_case("nat-shl-big", "nat.shiftLeft", "accept", ("Nat.shiftLeft", 1, 64), P64, "1 <<< 64 = 2^64")
nat_case("nat-shr-wrong", "nat.shiftRight", "reject", ("Nat.shiftRight", P64, 64), 0,
         "2^64 >>> 64 claimed 0")
nat_case("nat-shr-big", "nat.shiftRight", "accept", ("Nat.shiftRight", P64, 64), 1,
         "2^64 >>> 64 = 1")
nat_case("nat-shr-huge-shift", "nat.shiftRight", "accept", ("Nat.shiftRight", 1, P64), 0,
         "a shift amount of 2^64 bits is still fine for >>>")
nat_case("nat-pow-wrap", "nat.pow", "reject", ("Nat.pow", 2, 64), 0, "2^64 claimed 0")
nat_case("nat-pow-big", "nat.pow", "accept", ("Nat.pow", 2, 64), P64, "2^64")
nat_case("nat-pow-zero-zero", "nat.pow", "accept", ("Nat.pow", 0, 0), 1, "0^0 = 1")
nat_case("nat-pow-zero-zero-wrong", "nat.pow", "reject", ("Nat.pow", 0, 0), 0, "0^0 claimed 0")
nat_case("nat-pow-2-24", "nat.pow", "accept", ("Nat.mod", ("Nat.pow", 2, 2 ** 24), 7), 2,
         "2^(2^24) (a 2 MB literal) mod 7 = 2; the exponent is at Lean's limit")
nat_case("nat-pow-2-24-wrong", "nat.pow", "reject", ("Nat.mod", ("Nat.pow", 2, 2 ** 24), 7), 4,
         "2^(2^24) mod 7 claimed 4")
nat_case("nat-pow-2-24-plus1", "nat.size-limit", "either",
         ("Nat.mod", ("Nat.pow", 2, 2 ** 24 + 1), 7), 4,
         "true claim just past Lean's Nat.pow limit; Lean refuses, a kernel may compute it")
nat_case("nat-pow-2-24-plus1-wrong", "nat.size-limit", "reject",
         ("Nat.mod", ("Nat.pow", 2, 2 ** 24 + 1), 7), 2,
         "false claim just past the Nat.pow limit: refusing or computing both reject")
nat_case("nat-pow-exp-u32", "nat.size-limit", "either", ("Nat.pow", 1, U32), 1,
         "1^(2^32) = 1; Lean refuses exponents that do not fit in 32 bits")
nat_case("nat-pow-exp-u32-wrong", "nat.size-limit", "reject", ("Nat.pow", 1, U32), 0,
         "1^(2^32) claimed 0")
nat_case("nat-pow-result-limit-wrong", "nat.size-limit", "reject",
         ("Nat.ble", ("Nat.pow", 2, 2 ** 31), 0), "Bool.true",
         "2^(2^31) (256 MB) claimed <= 0; must not be accepted whatever the size policy", ty=B)
nat_case("nat-shl-limit", "nat.size-limit", "either",
         ("Nat.shiftRight", ("Nat.shiftLeft", 1, 2 ** 31), 2 ** 31), 1,
         "(1 <<< 2^31) >>> 2^31 = 1 builds a 256 MB literal; Lean refuses it")
nat_case("nat-shl-limit-wrong", "nat.size-limit", "reject",
         ("Nat.shiftRight", ("Nat.shiftLeft", 1, 2 ** 31), 2 ** 31), 0,
         "the same claimed 0")
nat_case("nat-shl-zero-u32", "nat.size-limit", "either", ("Nat.shiftLeft", 0, U32), 0,
         "0 <<< 2^32 = 0: the shift amount does not fit in 32 bits, the result is tiny")
nat_case("nat-log2-small", "nat.log2", "accept", ("Nat.log2", 8), 3,
         "Nat.log2 is not a kernel extension: it must be unfolded")
nat_case("nat-log2-wrong", "nat.log2", "reject", ("Nat.log2", 8), 4, "log2 8 claimed 4")
nat_case("nat-log2-zero", "nat.log2", "accept", ("Nat.log2", 0), 0, "log2 0 = 0")
nat_case("nat-succ-big", "nat.lit", "accept", ("Nat.succ", P64 - 1), P64,
         "Nat.succ of a literal at the 2^64 boundary")
nat_case("nat-succ-wrong", "nat.lit", "reject", ("Nat.succ", ("Nat.succ", 0)), 3,
         "succ (succ 0) claimed 3")
nat_case("nat-zero-lit", "nat.lit", "accept", "Nat.zero", 0, "Nat.zero is defeq to literal 0")
nat_case("nat-big-lit-neq", "nat.lit", "reject", P64, 0,
         "2^64 claimed equal to 0 (a literal truncated to 64 bits)")


@case("nat-lit-negative", "nat.lit", "reject", "natVal \"-1\" is not a natural number")
def _(tc):
    e = claim(tc, 0, 0)
    t = e.text().replace('"natVal":"0"', '"natVal":"-1"')
    return t


# ---------------------------------------------------------------------------
# String literals

STR_CONSTS = ["String.ofList", "Char.ofNat", "List.cons", "List.nil", "Eq.refl"]


def str_claim(tc, s, cps=None, other=None):
    e = tc.export(STR_CONSTS)
    T = e.const("String")
    ch = e.const("Char")
    lst = e.app(e.const("List.nil", [0]), ch)
    for c in reversed(cps or []):
        lst = e.app(e.const("List.cons", [0]), ch, e.app(e.const("Char.ofNat"), e.nat(c)), lst)
    rhs = e.str_(other) if other is not None else e.app(e.const("String.ofList"), lst)
    lhs = e.str_(s)
    e.add_thm("K.claim", eq(e, T, lhs, rhs), refl(e, T, lhs))
    return e


def str_case(id, expected, s, cps, why, other=None):
    case(id, "string.lit", expected, why)(lambda tc: str_claim(tc, s, cps, other))


str_case("str-empty", "accept", "", [], "\"\" unfolds to String.ofList []")
str_case("str-ab", "accept", "ab", [97, 98], "\"ab\" unfolds to String.ofList ['a','b']")
str_case("str-ab-swapped", "reject", "ab", [98, 97], "\"ab\" claimed to be ['b','a']")
str_case("str-ab-short", "reject", "ab", [97], "\"ab\" claimed to be ['a']")
str_case("str-2byte", "accept", "é", [233], "a 2-byte UTF-8 char is one Char (U+00E9)")
str_case("str-2byte-as-bytes", "reject", "é", [0xC3, 0xA9],
         "a 2-byte char claimed to be its UTF-8 bytes")
str_case("str-4byte", "accept", "\U0001F600", [0x1F600], "a 4-byte char is one Char")
str_case("str-4byte-as-utf16", "reject", "\U0001F600", [0xD83D, 0xDE00],
         "a 4-byte char claimed to be its UTF-16 surrogate pair")
str_case("str-nul", "accept", "a\x00b", [97, 0, 98], "an embedded NUL is an ordinary char")
str_case("str-nul-truncated", "reject", "a\x00b", [97],
         "\"a\\0b\" claimed to be \"a\" (C-string truncation)")
str_case("str-lit-neq", "reject", "a", None, "two different literals are not defeq", other="b")
str_case("str-invalid-char", "accept", "\x00", [0xD800],
         "Char.ofNat of a surrogate is '\\0', so String.ofList [Char.ofNat 0xD800] is \"\\0\"")


# ---------------------------------------------------------------------------
# Positivity (built as `unsafe` in Lean so the recursors exist, then made safe)

def positivity(id, typ, why):
    @case(id, "inductive.positivity", "reject", why)
    def _(tc):
        e = tc.export([typ], unsafe=True)
        make_safe(e, typ)
        return e


positivity("pos-direct", "K.Neg", "Neg.mk : (Neg → Nat) → Neg (control)")
positivity("pos-nonstrict", "K.NonStrict", "((T → Nat) → Nat) → T is positive but not strictly")
positivity("pos-nested-list", "K.NegNested", "negative occurrence inside a nested List argument")
positivity("pos-nested-wrap", "K.NegWrap",
           "nested through Wrap, whose parameter is used negatively in Wrap's field")
positivity("pos-mutual", "K.NegA", "negative occurrence of the other type of a mutual block")
positivity("pos-mutual-nested", "K.NegNA",
           "mutual block, nested through List, negative in the other type")


@case("pos-nested-ok", "inductive.positivity", "accept", "List (Nat → T) → T is fine")
def _(tc):
    return as_is(tc, "K.PosNested")


@case("pos-mutual-nested-ok", "inductive.positivity", "accept",
      "mutual + nested, strictly positive")
def _(tc):
    return as_is(tc, "K.PosA")


# ---------------------------------------------------------------------------
# Mutual blocks

@case("mutual-param-type", "inductive.mutual", "reject",
      "MB's parameter is (α : Prop) while MA's is (α : Type)")
def _(tc):
    e = tc.export(["K.MA"])
    d = e.decl("K.MB")
    bs, body = e.binders(d["type"])
    n, t, bi = bs[0]
    d["type"] = e.close([(n, e.sort(0), bi)], body, kind="forallE")
    return e


@case("mutual-levelparam-name", "inductive.mutual", "reject",
      "MV is declared over universe v, MU over u")
def _(tc):
    e = tc.export(["K.MU"])
    d = e.decl("K.MV")
    u, v = e.lparam("u"), e.lparam("v")
    d["levelParams"] = [e.name("v")]
    d["type"] = e.map_levels(d["type"], lambda l: rename_level(e, l, u, v))
    return e


def rename_level(e, l, u, v):
    k, p = e.levels[l]
    if l == u:
        return v
    if k == "succ":
        return e.lsucc(rename_level(e, json.loads(p), u, v))
    if k in ("max", "imax"):
        a, b = json.loads(p)
        f = e.lmax if k == "max" else e.limax
        return f(rename_level(e, a, u, v), rename_level(e, b, u, v))
    return l


@case("mutual-levelparam-extra", "inductive.mutual", "reject",
      "MV lists level params [u, v], MU lists [u]")
def _(tc):
    e = tc.export(["K.MU"])
    d = e.decl("K.MV")
    d["levelParams"] = d["levelParams"] + [e.name("v")]
    return e


@case("mutual-result-universe", "inductive.mutual", "reject",
      "MA : Type → Type but MB : Type → Type 1")
def _(tc):
    e = tc.export(["K.MA"])
    d = e.decl("K.MB")
    bs, body = e.binders(d["type"])
    d["type"] = e.close(bs, e.sort(e.lnum(2)), kind="forallE")
    return e


@case("mutual-numparams", "inductive.mutual", "reject",
      "MB's record says numParams 0, MA's says 1")
def _(tc):
    e = tc.export(["K.MA"])
    e.decl("K.MB")["numParams"] = 0
    return e


@case("mutual-all", "inductive.mutual", "reject", "MB's `all` omits MA")
def _(tc):
    e = tc.export(["K.MA"])
    e.decl("K.MB")["all"] = [e.name("K.MB")]
    return e


# ---------------------------------------------------------------------------
# Structure eta and unit-like eta

@case("eta-unit", "eta.unit", "accept", "any two values of a fieldless structure are defeq")
def _(tc):
    return as_is(tc, "K.U.uniq")


@case("eta-unit-param", "eta.unit", "accept", "unit-like eta with a parameter")
def _(tc):
    return as_is(tc, "K.UP.uniq")


@case("eta-unit-indexed", "eta.unit", "reject",
      "W : Nat → Type has one fieldless ctor but an index: not unit-like")
def _(tc):
    return with_rfl(tc, "K.W.uniq")


@case("eta-struct", "eta.struct", "accept", "p = (p.1, p.2) by eta for Prod")
def _(tc):
    return as_is(tc, "K.prod_eta")


@case("eta-struct-S", "eta.struct", "accept", "s = ⟨s.x, s.y⟩ by eta")
def _(tc):
    return as_is(tc, "K.S.eta")


@case("eta-recursive", "eta.struct", "reject",
      "R has one ctor but is recursive: x = R.mk (R.get x) is not defeq")
def _(tc):
    return with_rfl(tc, "K.R.eta")


@case("eta-recursive-isrec-lie", "eta.struct", "reject",
      "as eta-recursive, with R's record claiming isRec false")
def _(tc):
    e = with_rfl(tc, "K.R.eta")
    e.decl("K.R")["isRec"] = False
    return e


@case("eta-indexed", "eta.struct", "reject",
      "V : Nat → Type has one ctor but an index: no eta")
def _(tc):
    return with_rfl(tc, "K.V.eta")


@case("proj-recursive", "eta.proj", "accept",
      "projection out of the recursive one-ctor type R: allowed (only eta is restricted)")
def _(tc):
    e = tc.export(["K.R.get"])
    d = e.decl("K.R.get")
    d["value"] = e.lam("x", e.const("K.R"), e.proj("K.R", 0, e.bvar(0)))
    return e


@case("proj-indexed", "eta.proj", "accept",
      "projection out of the indexed one-ctor type V: allowed (only eta is restricted)")
def _(tc):
    e = tc.export(["K.V.get"])
    d = e.decl("K.V.get")
    bs, _ = e.binders(d["type"])
    d["value"] = e.close(bs, e.proj("K.V", 0, e.bvar(0)))
    return e


def proj_def(tc, idx, ret):
    e = tc.export(["K.S.eta"])
    S = e.const("K.S")
    e.add_def("K.p", e.pi("s", S, e.const(ret)), e.lam("s", S, e.proj("K.S", idx, e.bvar(0))))
    return e


@case("proj-ok", "eta.proj", "accept", "proj S 0 : Nat (control)")
def _(tc):
    return proj_def(tc, 0, "Nat")


@case("proj-out-of-range", "eta.proj", "reject", "proj S 2, S has two fields")
def _(tc):
    return proj_def(tc, 2, "Nat")


@case("proj-wrong-type", "eta.proj", "reject", "proj S 1 is a Bool, claimed Nat")
def _(tc):
    return proj_def(tc, 1, "Nat")


# ---------------------------------------------------------------------------
# Constructor and recursor records that the kernel must recompute, not trust

@case("ctor-meta-cidx", "inductive.meta", "reject", "Bool.true claims cidx 0")
def _(tc):
    e = tc.export(["Bool.true"])
    e.decl("Bool.true")["cidx"] = 0
    return e


@case("ctor-meta-numfields", "inductive.meta", "reject", "True.intro claims one field")
def _(tc):
    e = tc.export(["True.intro"])
    e.decl("True.intro")["numFields"] = 1
    return e


@case("rec-rule-swap", "inductive.rec", "reject", "Bool.rec's two rule right-hand sides swapped")
def _(tc):
    e = tc.export(["Bool.rec"])
    r = e.decl("Bool.rec")["rules"]
    r[0]["rhs"], r[1]["rhs"] = r[1]["rhs"], r[0]["rhs"]
    return e


@case("rec-k-lie", "inductive.rec", "reject", "Bool.rec claims K-like reduction (k = true)")
def _(tc):
    e = tc.export(["Bool.rec"])
    e.decl("Bool.rec")["k"] = True
    return e


@case("rec-k-missing", "inductive.rec", "reject", "Eq.rec claims k = false (it is K-like)")
def _(tc):
    e = tc.export(["Eq.rec"])
    e.decl("Eq.rec")["k"] = False
    return e


# ---------------------------------------------------------------------------
# Universe levels: `def K.f : Sort a → Sort b := fun x => x` needs a ≡ b

def univ(id, expected, a, b, why):
    @case(id, "universe.level", expected, why)
    def _(tc):
        e = empty_export(tc.export(["K.triv"]).meta)
        u, v, w = e.lparam("u"), e.lparam("v"), e.lparam("w")
        env = {"u": u, "v": v, "w": w, "max": e.lmax, "imax": e.limax, "succ": e.lsucc, "z": 0}
        A, Bl = eval(a, {}, env), eval(b, {}, env)
        ty = e.pi("x", e.sort(A), e.sort(Bl))
        e.add_def("K.f", ty, e.lam("x", e.sort(A), e.bvar(0)), lps=["u", "v", "w"])
        return e


univ("univ-imax-succ", "accept", "imax(u, succ(v))", "max(u, succ(v))",
     "imax u (v+1) = max u (v+1)")
univ("univ-max-imax", "reject", "max(u, v)", "imax(u, v)", "max u v ≠ imax u v when v = 0")
univ("univ-imax-self", "accept", "imax(u, u)", "u", "imax u u = u")
univ("univ-imax-zero", "accept", "imax(u, z)", "z", "imax u 0 = 0")
univ("univ-imax-one", "reject", "imax(succ(z), u)", "succ(z)", "imax 1 u is 0 when u = 0")
univ("univ-imax-nested-trap", "reject", "imax(imax(u, v), w)", "imax(max(u, v), w)",
     "differs at v = 0, w = 1, u = 2: looks like a harmless imax→max rewrite")
univ("univ-imax-assoc", "either", "imax(u, imax(v, w))", "imax(max(u, v), w)",
     "equal for every assignment (w = 0, then w > 0); a level normaliser need not prove it")
univ("univ-max-comm", "accept", "max(u, v)", "max(v, u)", "max is commutative")
univ("univ-max-zero", "accept", "max(z, u)", "u", "max 0 u = u")
univ("univ-succ-max", "accept", "succ(max(u, v))", "max(succ(u), succ(v))",
     "succ distributes over max")
univ("univ-max-absorb", "accept", "max(u, max(u, v))", "max(v, u)", "idempotence + commutativity")
univ("univ-param-swap", "reject", "u", "v", "distinct parameters")
univ("univ-succ-param", "reject", "succ(u)", "u", "u+1 ≠ u")
univ("univ-imax-succ-left", "reject", "imax(succ(u), v)", "succ(max(u, v))",
     "imax (u+1) v is 0 when v = 0")


@case("lparam-undeclared", "universe.params", "reject", "K.lp uses u but declares no level params")
def _(tc):
    e = tc.export(["K.lp"])
    e.decl("K.lp")["levelParams"] = []
    return e


@case("lparam-duplicate", "universe.params", "reject", "K.lp declares level params [u, u]")
def _(tc):
    e = tc.export(["K.lp"])
    d = e.decl("K.lp")
    d["levelParams"] = d["levelParams"] * 2
    return e


def const_arity(e, name, f):
    n = e.name(name)
    hit = []

    def fe(i, k, p, d):
        if k == "const" and p["name"] == n:
            hit.append(i)
            return e._e("const", {"name": n, "us": f(p["us"])})
        return None
    return fe, hit


def lp_arity(tc, f):
    e = tc.export(["K.lp", "Eq.refl"])
    d = e.decl("K.lp")
    fe, hit = const_arity(e, "Eq.refl", f)
    d["value"] = e.rebuild(e.rfl_proof(d["type"]), fe=fe)
    assert hit
    return e


@case("lparam-const-too-many", "universe.params", "reject", "Eq.refl.{u, u} (one param expected)")
def _(tc):
    return lp_arity(tc, lambda us: us * 2)


@case("lparam-const-too-few", "universe.params", "reject", "Eq.refl with no universe argument")
def _(tc):
    return lp_arity(tc, lambda us: [])


# Large elimination from Prop

def large_rec(tc, ind):
    e = tc.export([ind])
    r = e.decl(ind + ".rec")
    u = e.lparam("u")
    r["levelParams"] = [e.name("u")] + r["levelParams"]
    r["type"] = replace_sort0(e, r["type"], u)
    for rule in r["rules"]:
        rule["rhs"] = replace_sort0(e, rule["rhs"], u)
    return e


@case("elim-prop-two-ctors", "universe.elim", "reject",
      "P2 : Prop with two ctors, recursor claims a motive in Sort u")
def _(tc):
    return large_rec(tc, "K.P2")


@case("elim-prop-data-field", "universe.elim", "reject",
      "Ex : Prop with a Nat field, recursor claims a motive in Sort u")
def _(tc):
    return large_rec(tc, "K.Ex")


@case("elim-prop-use", "universe.elim", "reject",
      "P2.rec (motive into Prop) applied to a motive into Type")
def _(tc):
    e = tc.export(["K.P2", "Bool.true", "Bool.false"])
    P, Bt = e.const("K.P2"), e.const("Bool")
    motive = e.lam("p", P, Bt)
    body = e.app(e.const("K.P2.rec"), motive, e.const("Bool.true"), e.const("Bool.false"), e.bvar(0))
    e.add_def("K.toBool", e.pi("p", P, Bt), e.lam("p", P, body))
    return e


@case("elim-false-large", "universe.elim", "accept",
      "False eliminates into any universe (empty Prop)")
def _(tc):
    e = tc.export(["False.elim"])
    return e


# ---------------------------------------------------------------------------
# Quotients

@case("quot-lift-mk-q", "quot.reduce", "accept", "Quot.lift f h (Quot.mk r a) ≡ f a")
def _(tc):
    return as_is(tc, "K.q_lift_mk_q")


@case("quot-lift-mk-extra-arg", "quot.reduce", "accept",
      "the reduction also fires with extra arguments after the quotient")
def _(tc):
    return as_is(tc, "K.q_lift_mk_fun_q")


@case("quot-ind-mk", "quot.reduce", "accept", "Quot.ind h (Quot.mk r a) ≡ h a")
def _(tc):
    return as_is(tc, "K.q_ind_mk")


@case("quot-lift-var", "quot.reduce", "reject",
      "Quot.lift f h q ≡ f a claimed for a variable q (no Quot.mk to reduce)")
def _(tc):
    return with_rfl(tc, "K.q_lift_var")


@case("quot-mk-rel-rfl", "quot.reduce", "reject",
      "Quot.mk r a ≡ Quot.mk r b for related a b: needs Quot.sound, not defeq")
def _(tc):
    e = tc.export(["K.q_mk_rel"])
    d = e.decl("K.q_mk_rel")
    bs, body = e.binders(d["type"])
    # the type is ∀ {r} a b (h : r a b), Quot.mk r a = Quot.mk r b
    d["value"] = e.rfl_proof(d["type"])
    return e


@case("quot-lift-mk-wrong", "quot.reduce", "reject",
      "Quot.lift f h (Quot.mk r a) claimed ≡ f (a+1)")
def _(tc):
    e = tc.export(["K.q_lift_mk_q", "Nat.succ"])
    d = e.decl("K.q_lift_mk_q")
    bs, body = e.binders(d["type"])
    f, (T, a, b) = e.app_args(body)
    F, (A,) = e.app_args(b)
    b2 = e.app(F, e.app(e.const("Nat.succ"), A))
    d["type"] = e.close(bs, e.app(f, T, a, b2), kind="forallE")
    d["value"] = e.rfl_proof(d["type"])
    return e


@case("quot-lift-no-respect", "quot.typing", "reject",
      "Quot.lift declared without the respect hypothesis (lifts any function)")
def _(tc):
    e = tc.export(["Quot.lift"])
    d = e.decl("Quot.lift")
    d["type"] = drop_binder(e, d["type"], 4)
    return e


@case("quot-ind-large", "quot.typing", "reject", "Quot.ind's motive is Quot r → Sort u")
def _(tc):
    e = tc.export(["Quot.ind"])
    d = e.decl("Quot.ind")
    bs, body = e.binders(d["type"])
    n, t, bi = bs[2]
    bs[2] = (n, replace_sort0(e, t, e.lparam("u")), bi)
    d["type"] = e.close(bs, body, kind="forallE")
    return e


@case("quot-mk-type", "quot.typing", "reject", "Quot.mk : {α} → (r) → α → α")
def _(tc):
    e = tc.export(["Quot.mk"])
    d = e.decl("Quot.mk")
    bs, body = e.binders(d["type"])
    d["type"] = e.close(bs, e.bvar(2), kind="forallE")
    return e


@case("quot-kind-swap", "quot.typing", "reject", "Quot.lift's record says kind \"ind\"")
def _(tc):
    e = tc.export(["Quot.lift"])
    e.decl("Quot.lift")["kind"] = "ind"
    return e


@case("quot-no-eq", "quot.typing", "reject", "the quotient package without Eq declared")
def _(tc):
    e = tc.export(["Quot.lift"])
    e.remove_decl("Eq")
    return e


# ---------------------------------------------------------------------------
# Proof irrelevance

@case("pi-fun", "proof-irrel", "accept", "two proofs of ∀ n, p n are defeq")
def _(tc):
    return as_is(tc, "K.pi_fun")


@case("pi-imax", "proof-irrel", "accept",
      "∀ a : α, β a with α : Sort u, β : α → Prop is a Prop (imax u 0 = 0)")
def _(tc):
    return as_is(tc, "K.pi_imax")


@case("pi-beta", "proof-irrel", "accept", "the proposition is only Prop after beta")
def _(tc):
    return as_is(tc, "K.pi_beta")


@case("pi-data", "proof-irrel", "reject", "functions P → Nat out of a proof are not proofs")
def _(tc):
    return with_rfl(tc, "K.pi_data")


@case("pi-sort", "proof-irrel", "reject", "elements of α : Sort u are not proofs (u may be > 0)")
def _(tc):
    return with_rfl(tc, "K.pi_sort")


@case("pi-bool", "proof-irrel", "reject", "Bool values are not proofs")
def _(tc):
    return with_rfl(tc, "K.pi_bool")


@case("pi-proj-exists", "proof-irrel", "reject",
      "projecting the witness (data) out of a proof of ∃")
def _(tc):
    e = tc.export(["K.ex_wit"])
    d = e.decl("K.ex_wit")
    bs, _ = e.binders(d["type"])
    d["value"] = e.close(bs, e.proj("Exists", 0, e.bvar(0)))
    return e


@case("pi-proj-and", "proof-irrel", "accept", "projecting a proof out of a proof of ∧")
def _(tc):
    e = tc.export(["K.and_left"])
    d = e.decl("K.and_left")
    bs, _ = e.binders(d["type"])
    d["value"] = e.close(bs, e.proj("And", 0, e.bvar(0)))
    return e


# ---------------------------------------------------------------------------
# Malformed exports (base: theorem K.triv : True := True.intro)

def fmt(id, why, expected="reject"):
    return case(id, "export.format", expected, why)


@fmt("fmt-ok", "the unmodified base export (control)", expected="accept")
def _(tc):
    m, r = triv(tc)
    return join(m, r)


@fmt("fmt-meta-only", "an export with no declarations", expected="accept")
def _(tc):
    m, r = triv(tc)
    return join(m, [])


@fmt("fmt-fwd-expr", "the theorem's type record comes after the theorem")
def _(tc):
    m, r = triv(tc)
    i = last_decl(r)
    t = r[i]["thm"]["type"]
    j = next(k for k, x in enumerate(r) if x.get("ie") == t)
    rec = r.pop(j)
    r.append(rec)
    return join(m, r)


@fmt("fmt-dup-expr-id", "an expression id bound twice to different terms")
def _(tc):
    m, r = triv(tc)
    i = last_decl(r)
    t = r[i]["thm"]["type"]
    r.insert(i, {"ie": t, "sort": 0})
    return join(m, r)


@fmt("fmt-dup-expr-same", "an expression id bound twice to the same term")
def _(tc):
    m, r = triv(tc)
    i = last_decl(r)
    t = r[i]["thm"]["type"]
    rec = next(x for x in r if x.get("ie") == t)
    r.insert(i, dict(rec))
    return join(m, r)


@fmt("fmt-dup-name-id", "a name id bound twice")
def _(tc):
    m, r = triv(tc)
    rec = next(x for x in r if "in" in x)
    r.insert(r.index(rec) + 1, {"in": rec["in"], "str": {"pre": 0, "str": "Other"}})
    return join(m, r)


@fmt("fmt-dup-level-id", "a level id bound twice")
def _(tc):
    m, r = triv(tc)
    i = last_decl(r)
    r.insert(i, {"il": 1, "succ": 0})
    r.insert(i, {"il": 1, "succ": 0})
    return join(m, r)


@fmt("fmt-dup-decl", "the theorem declared twice")
def _(tc):
    m, r = triv(tc)
    r.append(r[last_decl(r)])
    return join(m, r)


def drop_field(kind, field):
    def f(tc):
        m, r = triv(tc)
        i = last_decl(r, kind)
        del r[i][kind][field]
        return join(m, r)
    return f


fmt("fmt-missing-value", "theorem without `value`")(drop_field("thm", "value"))
fmt("fmt-missing-type", "theorem without `type`")(drop_field("thm", "type"))
fmt("fmt-missing-levelparams", "theorem without `levelParams`")(drop_field("thm", "levelParams"))
fmt("fmt-missing-ctors", "inductive without `ctors`")(drop_field("inductive", "ctors"))
fmt("fmt-missing-recs", "inductive without `recs`")(drop_field("inductive", "recs"))


def rename_kind(old, new, which="decl"):
    def f(tc):
        m, r = triv(tc)
        if which == "decl":
            i = last_decl(r, old)
        else:
            i = next(k for k, x in enumerate(r) if old in x)
        r[i] = {(new if k == old else k): v for k, v in r[i].items()}
        return join(m, r)
    return f


fmt("fmt-kind-unknown", "a declaration record of unknown kind \"theorem\"")(rename_kind("thm", "theorem"))
fmt("fmt-kind-thm-as-axiom", "theorem fields under the \"axiom\" kind")(rename_kind("thm", "axiom"))
fmt("fmt-kind-thm-as-def", "theorem fields under the \"def\" kind")(rename_kind("thm", "def"))
fmt("fmt-kind-expr-unknown", "an expression record of unknown kind \"pi\"")(
    rename_kind("forallE", "pi", which="expr"))


def triv_edit(f):
    def g(tc):
        e = tc.export(["K.triv"])
        f(e, e.decl("K.triv"))
        return e
    return g


fmt("fmt-undeclared-const", "the proof refers to an undeclared constant")(
    triv_edit(lambda e, d: d.__setitem__("value", e.const("K.nope"))))
fmt("fmt-thm-mismatch", "the theorem's value True does not have type True")(
    triv_edit(lambda e, d: d.__setitem__("value", e.const("True"))))
fmt("fmt-thm-not-prop", "theorem K.triv : Prop := True (a theorem's type must be a Prop)")(
    triv_edit(lambda e, d: (d.__setitem__("type", e.sort(0)), d.__setitem__("value", e.const("True")))))
fmt("fmt-loose-bvar", "the theorem's type is a loose bound variable")(
    triv_edit(lambda e, d: d.__setitem__("type", e.bvar(0))))
fmt("fmt-const-wrong-arity", "True.intro applied to a universe argument")(
    triv_edit(lambda e, d: d.__setitem__("value", e.const("True.intro", [0]))))


@fmt("fmt-bad-level-ref", "a constant whose universe list names a missing level id")
def _(tc):
    m, r = triv(tc)
    i = last_decl(r)
    v = r[i]["thm"]["value"]
    rec = next(x for x in r if x.get("ie") == v)
    rec["const"]["us"] = [999]
    return join(m, r)


@fmt("fmt-name-bad-prefix", "a name whose prefix id does not exist")
def _(tc):
    m, r = triv(tc)
    rec = next(x for x in r if "in" in x)
    rec["str"]["pre"] = 999
    return join(m, r)


@fmt("fmt-no-meta", "the meta header line is missing")
def _(tc):
    m, r = triv(tc)
    return "\n".join(dumps(x) for x in r) + "\n"


@fmt("fmt-bad-json", "the last line is truncated JSON")
def _(tc):
    m, r = triv(tc)
    t = join(m, r).rstrip("\n")
    return t[:-5] + "\n"


@fmt("fmt-opaque-mismatch", "an opaque whose value does not match its type")
def _(tc):
    e = tc.export(["K.triv"])
    e.add_decl("opaque", {"all": [e.name("K.o")], "isUnsafe": False, "levelParams": [],
                          "name": e.name("K.o"), "type": e.const("True"), "value": e.const("True")})
    return e


@fmt("fmt-safe-uses-unsafe", "a safe theorem proved by an unsafe axiom of False")
def _(tc):
    e = tc.export(["False"])
    e.add_axiom("K.bad", e.const("False"), unsafe=True)
    e.add_thm("K.oops", e.const("False"), e.const("K.bad"))
    return e


@fmt("fmt-safe-uses-partial", "a safe definition that unfolds to a partial one")
def _(tc):
    e = tc.export(["K.triv"])
    T = e.const("True")
    e.add_def("K.p", T, e.const("True.intro"), safety="partial")
    e.add_def("K.q", T, e.const("K.p"))
    return e


# ---------------------------------------------------------------------------
# Evaluation of closed terms (src/check/eval/). Each claim is proved by
# `Eq.refl`, so only reduction decides it; the `-wrong` twins must fail.

def eval_case(id, thm, expected, why, consts=()):
    case(id, "eval", expected, why)(lambda tc: with_rfl(tc, thm, consts))


QUOT = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"]


eval_case("eval-decide", "K.ev_decide", "accept", "decide on a fold over List.range")
eval_case("eval-decide-false", "K.ev_decide_false", "reject", "the same decide, false")
eval_case("eval-k-stuck", "K.ev_k_stuck", "reject",
          "Eq.rec over an axiom of 0 = 1: K does not apply (0 ≢ 1), so the cast is stuck")
eval_case("eval-k-ok", "K.ev_k_ok", "accept",
          "Eq.rec over an axiom of 2 + 2 = 4: K applies (2 + 2 ≡ 4) without reducing the axiom")
eval_case("eval-struct-eta", "K.ev_struct_eta", "accept",
          "Prod.rec on an opaque pair reduces by structure eta to its first projection")
eval_case("eval-struct-eta-wrong", "K.ev_struct_eta_wrong", "reject",
          "the same, claimed to be the second projection")
eval_case("eval-quot", "K.ev_quot_ok", "accept", "Quot.lift f h (Quot.mk r (ev_sum 4)) ≡ f 6 = 7", QUOT)
eval_case("eval-quot-wrong", "K.ev_quot_wrong", "reject", "the same, claimed 6", QUOT)
eval_case("eval-str-len", "K.ev_str_len", "accept", "String.length of a literal")
eval_case("eval-str-len-wrong", "K.ev_str_len_wrong", "reject", "the same, claimed 4")
eval_case("eval-deep", "K.ev_deep_ok", "accept",
          "a right fold over 20000 elements: evaluation nests 20000 deep")
eval_case("eval-deep-wrong", "K.ev_deep_wrong", "reject", "the same, off by one")
eval_case("eval-pap", "K.ev_pap", "accept",
          "Nat.add 1 is not in weak head normal form: it unfolds (then eta)")
eval_case("eval-pap-wrong", "K.ev_pap_wrong", "reject", "Nat.add 1 ≢ fun x => Nat.add 2 x")
eval_case("eval-rec-lit", "K.ev_rec_lit", "accept",
          "Nat.rec on the literal 1000 (literals become Nat.succ applications)")
eval_case("eval-rec-lit-wrong", "K.ev_rec_lit_wrong", "reject", "the same, off by one")
eval_case("eval-big", "K.ev_big", "accept", "literal arithmetic past 2^64 inside decide")
eval_case("eval-big-wrong", "K.ev_big_wrong", "reject", "the same, false")
eval_case("eval-let", "K.ev_let_ok", "accept", "a let-bound value used twice")
eval_case("eval-let-wrong", "K.ev_let_wrong", "reject", "the same, off by one")
eval_case("eval-fn", "K.ev_fn_ok", "accept",
          "a fold that builds a function (closures of closures), then applied")
eval_case("eval-fn-wrong", "K.ev_fn_wrong", "reject", "the same, off by one")
