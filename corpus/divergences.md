# Divergences from Lean v4.36.0

nitrolean is meant to give the same verdict as the kernel of Lean v4.36.0
(`leanchecker --from-export`, recorded in `expected-lean-v4.36.0.tsv`) on every
test of the corpus. This file lists the exceptions. `scripts/lean-verdicts.sh`
reads the table below to write `expected-nitrolean.tsv`; `scripts/selfcheck.sh`
checks that every row names a test of the corpus on which Lean's verdict really
differs.

| test | nitrolean | Lean v4.36.0 | reason |
|---|---|---|---|
| `historical/010_HB15908.contra` | reject | accept | Proof of `False` through a redefined trusted built-in. The export defines `Nat.add a b := 0`, proves `Nat.add 2 2 = 0` by unfolding it, and gets `4 = 0` because the kernel's native literal arithmetic reduces `Nat.add 2 2` to `4` by the constant's name, without checking its definition. Upstream closed leanprover/lean4#15908 as not a kernel bug, since the kernel assumes the standard prelude. nitrolean is meant to accelerate a built-in only if it has its standard definition, and so rejects (lean4lean does too). |
| `historical/009_HB16279.boxNat` | reject | accept | Bug fixed after v4.36.0: an inductive whose `numParams` is `2^32 + 1` while its type has one binder. Lean v4.36.0 truncates the count to 32 bits and accepts; leanprover/lean4#16279 (merged 2026-11-05, after v4.36.0) stopped the truncation. No proof of `False` is derived in this export, but the declaration is malformed (more parameters than its type has binders), and accepting it would mean emulating the truncation, which is what the forged proofs of `False` of leanprover/lean4#12746 and #16730 build on. |
| `arena/corner-cases/eta-struct-major-no-whnf` | accept | timeout | Lean gives no verdict: its kernel reduces the recursor's major premise to weak head normal form before trying structure eta, and that premise (built from Coquand's paradox) has none, so it does not terminate. The declaration is well typed (the Arena declares `either`; both reduction orders give the same result when they terminate), and nitrolean, trying structure eta first as leanprover/lean4#15351 proposes, is meant to accept it. |
| `arena/corner-cases/eta-struct-major-and` | accept | reject | Lean v4.36.0 never eta-expands a structure in `Prop`, so it cannot reduce `And.rec f x` for a variable `x` and rejects `And.rec f ⟨x.1, x.2⟩ = And.rec f x`. The equation is sound: `And` is a subsingleton that eliminates into any universe, so by proof irrelevance `x` and `⟨x.1, x.2⟩` are the same proof. nitrolean eta-expands the major premise of a large-eliminating structure recursor, `Prop` included and before reducing it, as leanprover/lean4#15371 (merged after v4.36.0) does, and accepts it. |
| `arena/corner-cases/eta-struct-major-and-no-whnf` | accept | timeout | As above, with the structure eta under a conjunction. |

## Not divergences

These tests have an upstream verdict that differs from Lean's, but nitrolean
follows Lean on them, as they do not prove `False`:

- `lean4lean/001_L4LMutB`: a mutual block of two `partial` definitions with
  different universe parameters. lean4lean rejects it; the check
  (leanprover/lean4#14608) is not in what v4.36.0's `leanchecker
  --from-export` runs, and `partial` definitions carry no logical content.

Tests that Lean's `leanchecker` refuses before they reach the kernel (the
duplicate declarations of the Arena's tutorial, `arena/tutorial/13x_dup_*`)
count as rejected, which is also what the Arena expects.
