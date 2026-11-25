# The `.olean` format of Lean v4.36.0

This is what `src/olean/` reads. Line numbers are in the `leanprover/lean4`
sources at tag `v4.36.0` (commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`).
Everything is little-endian with 64-bit pointers, the layout of the platforms
Lean ships for (x86-64 and AArch64, Linux and macOS).

An `.olean` file is a memory image of one Lean value, a `ModuleData`, laid out
by the compactor (`src/runtime/compact.cpp`) so that Lean can `mmap` it and use
the objects in place. nitrolean reads the same bytes but never uses them as Lean
objects: it decodes the kernel's part (constants, expressions, levels, names)
into its own arenas, checking every pointer on the way.

## Files of a module

A module `A.B` built by Lake has `A/B.olean` in a build directory such as
`.lake/build/lib/lean`. If the module uses the module system (`ModuleData.isModule`;
all of Init, Std, Lean and Mathlib at v4.36.0 do), it is written in three parts
(`writeModule`, `src/Lean/Environment.lean:2243`):

| file | level (`OLeanLevel`, `Environment.lean:1876`) | constants |
|---|---|---|
| `A/B.olean` | `exported` | the exported ones, sorted by name |
| `A/B.olean.server` | `server` | (language-server data) |
| `A/B.olean.private` | `private` | all kernel constants of the module |

The three are written by one compactor (`saveModuleDataParts`,
`Environment.lean:2119`), so they share one address space: objects of a later
part may point into earlier parts (`readModuleDataPartsOfMod`,
`Environment.lean:2443`, reads `.server` with the main part as a dependency
region, and `.private` with both). nitrolean takes the constants from the
`.private` part, the level `importModules` uses by default and the one
`leanexport` exports. A module without the module system has only the
`.olean`. The `.ir`, `.ir.sig` and `.ilean` files hold compiler and editor data
and are not read.

## Header

`struct olean_header`, `src/library/module.cpp:106-144`, 88 bytes, no padding:

| offset | size | field |
|---|---|---|
| 0 | 5 | `"olean"` |
| 5 | 1 | header version: 2, or 3 when the file holds closures (`CompactedRegion.save (allowClosures := true)`) |
| 6 | 1 | flags; bit 0: big numbers use GMP's layout (set in the Linux and macOS releases) |
| 7 | 33 | Lean version, NUL-padded, e.g. `4.36.0` |
| 40 | 40 | build githash, NUL-padded |
| 80 | 8 | `base_addr`: the address the whole file (header included) is meant to be mapped at |

Version 2: the compacted data starts at offset 88 and runs to the end of the
file. Version 3 (`module.cpp:133-140`, written at `module.cpp:337-393`, read at
`module.cpp:582-600`): an 8-byte data size at 88, the data at 96, then a table
of closure offsets and library names used to relocate function pointers.
Kernel data never contains closures; nitrolean reads version 3 files but no
closure object.

`base_addr` is derived from the hash of the module name (`module.cpp:281-294`);
for the later parts it is the first part's base plus the part's offset in the
compactor's buffer (`module.cpp:322-329`), so the parts' ranges never overlap.

nitrolean accepts only files whose version string is `4.36.0`: other releases may
change the layouts below.

## Pointers and the object graph

Every field that holds a Lean value is a 64-bit word:

* odd: a boxed scalar, the value shifted left by one (`lean_box`). Small `Nat`s,
  enumerations, and constructors without fields (`Name.anonymous`,
  `List.nil`, `Option.none`, `ReducibilityHints.opaque`) are boxed scalars.
* even: a pointer, the logical address of an object: `base_addr` plus the
  object's offset in the file (`object_compactor::save`, `compact.cpp:182-188`;
  dependency regions, `compact.cpp:202-232`).

The first word of the data is the root slot, the address of the `ModuleData`
object (`object_compactor::operator()`, `compact.cpp:461-469`;
`region_reader::read`, `compact.cpp:615-662`).

The compactor writes objects depth-first, children before the object holding
them (`insert_constructor`, `compact.cpp:297-310`: it computes the children's
offsets, then allocates the parent), and shares structurally equal objects
(`save_max_sharing`, `compact.cpp:190-200`: a node equal to an earlier one is
dropped and replaced by the earlier one). So every pointer points to a lower
address than the object holding it, including pointers into earlier parts.
nitrolean requires this: a pointer that does not point strictly below its holder
is an error. That makes the graph acyclic by construction, so no input can
make a walk loop. Objects are 8-byte aligned (`alloc`, `compact.cpp:163-180`).

## Objects

Each object starts with an 8-byte header, `lean_object`
(`src/include/lean/lean.h:174-179`):

| offset | size | field |
|---|---|---|
| 0 | 4 | `m_rc`: 0 in compacted objects (`lean_set_non_heap_header`, `lean.h:821-829`) |
| 4 | 2 | `m_cs_sz`: byte size of a small object; 1 for arrays and strings |
| 6 | 1 | `m_other`: number of pointer fields of a constructor |
| 7 | 1 | `m_tag`: constructor index (0-243), or a kind (`lean.h:113-125`) |

Kinds used by kernel data:

* **Constructor** (tag ≤ 243, `lean_ctor_object`, `lean.h:213-216`): `m_other`
  pointer fields, then the scalar fields. Lean orders a constructor's fields as
  pointer fields first in declaration order, then `USize` fields, then other
  scalars by decreasing size, in declaration order within a size. The object's
  size is `m_cs_sz` (`lean_object_byte_size`, `src/runtime/object.cpp:214-235`).
* **Array** (246, `lean_array_object`, `lean.h:219-224`): `m_size` at 8,
  `m_capacity` at 16, then `m_size` pointers (`insert_array`,
  `compact.cpp:312-328`).
* **String** (249, `lean_string_object`, `lean.h:234-240`): `m_size` (bytes
  including the terminating NUL) at 8, `m_capacity` at 16, `m_length` (code
  points) at 24, then the UTF-8 bytes and a NUL (`insert_string`,
  `compact.cpp:279-291`).
* **Big natural number** (250, `mpz_object`, `src/runtime/object.h:21-26`,
  `insert_mpz`, `compact.cpp:390-418`). With GMP (header flag bit 0):
  `_mp_alloc` (i32) at 8, `_mp_size` (i32, negative for negative numbers) at
  12, `_mp_d` at 16, a logical pointer to the limbs, which follow at 24 (64-bit
  limbs, least significant first). Without GMP (`src/runtime/mpz.h:31-33`): a
  sign byte at 8, the digit count at 16, the digit pointer at 24, then 32-bit
  digits from 32. `Nat`s below 2^63 are boxed scalars instead.

nitrolean checks that every object it reads lies wholly inside one part's data,
that its header is a compacted header of an expected kind, and that a
constructor has the tag, field count and size its type requires.

## The kernel's types

Field layouts follow from the rule above. "data" is a field computed by Lean
(`@[computed_field]`) and stored in the object after the declared fields.

`ModuleData` (`src/Lean/Environment.lean:109-127`): tag 0, pointer fields
`imports : Array Import`, `constNames : Array Name`,
`constants : Array ConstantInfo`, `extraConstNames : Array Name`,
`entries : Array (Name × Array EnvExtensionEntry)`; scalar `isModule : Bool`
at byte 0. `Import` (`src/Lean/Setup.lean:25-33`): `module : Name`; bytes
`importAll`, `isExported`, `isMeta`.

`Name` (`src/Init/Prelude.lean:4874-4900`): `anonymous` is the scalar 0;
`str pre s` is tag 1 with fields `pre`, `s : String`; `num pre i` is tag 2
with `pre`, `i : Nat`; both carry the cached `hash : UInt64` (line 4895) at
scalar byte 0.

`Level` (`src/Lean/Level.lean:90-106`), each with `data : UInt64` (hash,
depth, flags) at scalar byte 0: `zero` tag 0 with no pointer fields (nitrolean
also accepts the boxed scalar 0, as the C++ kernel does at
`src/kernel/level.h:47`), `succ` 1 `[l]`, `max` 2 `[l, r]`, `imax` 3 `[l, r]`,
`param` 4 `[name]`, `mvar` 5 `[id]`.

`Expr` (`src/Lean/Expr.lean:298-470`), each with `data : Expr.Data`, a
`UInt64` (`Expr.lean:118-132`: 32-bit hash, 8-bit approximate depth, four
flags, 20-bit loose bound variable range), at scalar byte 0:

| tag | constructor | pointer fields | other scalars |
|---|---|---|---|
| 0 | `bvar` | `idx : Nat` | |
| 1 | `fvar` | `FVarId` | |
| 2 | `mvar` | `MVarId` | |
| 3 | `sort` | `Level` | |
| 4 | `const` | `Name`, `List Level` | |
| 5 | `app` | `fn`, `arg` | |
| 6 | `lam` | `binderName`, `binderType`, `body` | `binderInfo : UInt8` at 8 |
| 7 | `forallE` | as `lam` | as `lam` |
| 8 | `letE` | `declName`, `type`, `value`, `body` | `nondep : Bool` at 8 (`src/kernel/expr.h:256`) |
| 9 | `lit` | `Literal` | |
| 10 | `mdata` | `MData`, `expr` | |
| 11 | `proj` | `typeName : Name`, `idx : Nat`, `struct` | |

`BinderInfo` (`Expr.lean:71-80`): 0 default, 1 implicit, 2 strict implicit, 3
instance implicit. `Literal` (`Expr.lean:18-22`): `natVal` tag 0 `[Nat]`,
`strVal` tag 1 `[String]`. `List`: `nil` is the scalar 0, `cons` tag 1
`[head, tail]`.

`ConstantInfo` (`src/Lean/Declaration.lean:406-415`): tags 0-7 (`axiomInfo`,
`defnInfo`, `thmInfo`, `opaqueInfo`, `quotInfo`, `inductInfo`, `ctorInfo`,
`recInfo`), each with one field, the `*Val` structure, whose first field is
its `ConstantVal` (`Declaration.lean:91-94`: `name`, `levelParams : List Name`,
`type`):

| `*Val` | pointer fields after `toConstantVal` | scalars |
|---|---|---|
| `AxiomVal` (97) | | `isUnsafe` |
| `DefinitionVal` (108) | `value`, `hints`, `all` | `safety` (0 unsafe, 1 safe, 2 partial, line 104) |
| `TheoremVal` (130) | `value`, `all` | |
| `OpaqueVal` (139) | `value`, `all` | `isUnsafe` |
| `QuotVal` (396) | | `kind` (0 type, 1 ctor, 2 lift, 3 ind) |
| `InductiveVal` (239) | `numParams`, `numIndices`, `all`, `ctors`, `numNested` | `isRec`, `isUnsafe`, `isReflexive` |
| `ConstructorVal` (306) | `induct`, `cidx`, `numParams`, `numFields` | `isUnsafe` |
| `RecursorVal` (335) | `all`, `numParams`, `numIndices`, `numMotives`, `numMinors`, `rules` | `k`, `isUnsafe` |

`ReducibilityHints` (`Declaration.lean:46-49`): `opaque` is the scalar 0,
`abbrev` the scalar 1, `regular h` tag 2 with `h : UInt32` at scalar byte 0.
`RecursorRule` (`Declaration.lean:326-332`): `ctor`, `nfields : Nat`, `rhs`.

## What nitrolean does with it

* **Cached data is ignored.** The name hashes, `Level.data` and `Expr.data`
  are never read. The arenas recompute what the checker relies on (loose bound
  variable range, level-parameter and free-variable flags) from the structure
  when a node is interned, and hash with their own function.
* `mdata` is kernel-transparent: it maps to its inner expression, as in the
  NDJSON reader. `fvar`, `mvar` and level `mvar` are errors: no declaration
  may contain them.
* **Import closure.** The imports of each module's main part are resolved in
  the search path (the project's build directory, its packages', `LEAN_PATH`
  and the toolchain's `lib/lean`); modules are loaded once each, after their
  imports, in the order of Lean's `importModulesCore` (depth-first, imports in
  order). An import cycle is an error.
* **Order.** A module's `constants` are in hash-map order (`mkModuleData`,
  `Environment.lean:2201-2230`). nitrolean groups them like `leanexport` (an
  inductive family with its constructors and recursors; the quotient
  constants) and sorts each module's groups depth-first by the constants
  their terms mention, so that every declaration comes after the ones it uses.
* **Duplicates.** A constant declared by two modules is an error, except where
  `importModules` merges them (`subsumesInfo`, `Environment.lean:2633-2665`,
  applied at 2699-2710): theorems (or a theorem and an axiom, or two
  propositional axioms) with the same type and universe parameters, as made by
  realized constants such as `congr_simp` and `eq_def` lemmas. Lean keeps the
  later theorem; nitrolean keeps the first one under the name, which earlier
  declarations may use, and also checks every later copy whose proof differs.

## Untrusted input

Every file is treated as hostile. Each pointer is checked to be aligned, to
lie inside the data of one of the module's parts with room for its object, and
to point below its holder; each object's header and size are checked against
its expected type; scalars and enumerations are range-checked; strings must be
NUL-terminated UTF-8; counts must fit the arenas' 32-bit ids. All walks are
iterative. Malformed input is reported with the file and exits with status 2;
it never panics. The memory map is the only `unsafe` code in nitrolean
(`src/olean/file.rs`): Lean writes `.olean` files under a temporary name and
renames them into place, so a mapped file does not change; if another program
truncates it anyway, reads past the new end fault instead of returning wrong
bytes.
