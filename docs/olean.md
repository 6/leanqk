# From `.olean` files to the checker

This note covers what the `.olean` reader (`src/olean/`) gives the checker
(`src/check/`), and how it gets there fast. The file format itself is
described in [olean-format.md](olean-format.md).

## The interface

The checker only sees an `Env` (`src/env.rs`). It is shared read-only by
all checking threads through `&Env`, and it never changes during checking.

- `decls: Vec<Decl>` in file order. `blocks: Vec<Block>` lists the
  scheduling units in dependency order: one declaration, or one inductive
  group. `block_decls(&Block)` gives a block's declarations.
- `find(NameId) -> Option<&Decl>`, and `by_name` for a declaration's
  index.
- `names`, `levels` and `exprs` are hash-consed arenas with dense `u32`
  ids. Id equality is structural equality. `exprs.node(id)` and
  `exprs.data(id)` (loose bound variable range, level parameters, free
  variables) are O(1) array reads. The env also holds let binders, big
  literals, `name_list` and `rec_rules`.
- A `Decl` has its name, its level parameters, `ty: ExprId` and its kind.
  Definitions, theorems and opaques carry `value: ExprId`.

### Lazy theorem values

Types, definitions, opaques and recursor rules are built at load time.
Theorem values are not. When reading `.olean` files with lazy proofs on
(the default for `check --olean`; `NITROLEAN_LAZY_PROOFS=0` turns it off),
a theorem's `value` is a placeholder:

- `env::is_lazy(e)` is true for a placeholder. Never pass one to
  `node` or `data`.
- `Env::value_into(&Decl, &mut dyn TermSink) -> Result<Option<ExprId>, String>`
  decodes the value from its file into the caller's `TermSink`. A value
  that is not lazy comes back as is. Nothing is cached, so the shared
  arena stays unchanged. An error means the file is malformed.
- `TermSink` takes names, levels, level lists and expression nodes,
  children first. A sink should look each node up in the shared arena
  first, so that ids stay canonical. Strings are already in the shared
  pool (`StrPool::intern_late` adds the ones first met in a lazy value).
- Subterms of a value that were already built at load time arrive whole,
  as ids of the shared arena, through `shared_name` and `shared_expr`. By
  default these return the id unchanged, which is right for any sink
  above the same environment, such as the checker's `Store`.

The checker's `Store` implements `TermSink`. `Tc::value(&Decl)` builds the
value once per declaration being checked, and returns it from a cache
afterwards; the cache is dropped with the store on `reset`. Its callers are:

- checking a declaration's value;
- unfolding a definition or theorem;
- the evaluator's constant unfolding.

A theorem's proof therefore lives only in the store of the thread that
checks it, and is freed with that store.

Equal copies of a theorem in several modules are merged at load time only
when their values were read. With lazy proofs, later copies are kept and
checked as well.

## How loading works

1. **Imports.** Module headers are read in parallel, and the import
   closure is resolved as headers arrive.
2. **Files.** Each module's parts (`.olean`, `.olean.server`,
   `.olean.private`) are memory-mapped, and objects are read in place.
3. **Decoding.** Each module is decoded on its own thread into a tape of
   module-local nodes. The memo is a dense array indexed by object
   address, which is cheap because Lean's compactor shares equal objects
   within a module. With lazy proofs, a scan of the theorem values, in
   address order, finds which constants of the same module they mention.
   That information is needed for the block order.
4. **Interning.** Tapes are hash-consed into the shared arenas: names
   depth by depth and expressions height by height, in batches. The
   tables are lock-free open-addressing tables (`intern::IdTable`), with
   per-thread id blocks and grouped probes.
5. **Assembly.** Declarations are ordered into blocks, equal copies are
   merged, and the arenas are handed to the `Env` without a copy.

A lazy value is decoded only down to the subterms that were built at
load time. Proofs share most of their types and instances with their
statements, and in Lean's compacted files equal objects are one object.
So the scan in step 3 records which loaded objects the lazy values point
to, and keeps them per module in a small map from the object's position
in the module (its memo slot) to its shared id (`decode::Pre`). On the Lean package this map has 0.75M entries
across all modules, and cuts the nodes decoded for proofs by 40%.

The files of modules with lazy values stay mapped. Their pages are
released after loading, and again every 1024 decoded values, so they do
not add up in memory as checking reads every proof.

`NITROLEAN_OLEAN_PROFILE=1` prints decode and intern times and node counts.

## Exports

The NDJSON export reader (`src/reader.rs`) gives the checker the same
interface, lazy theorem values included (`reader::Options::lazy_proofs`,
the default for `check`; `src/reader/lazy.rs`):

- Leaves (`bvar`, `sort`, `const`, literals) are added to the arena at
  once. Other expression records stay pending until the next declaration
  line. There, the terms the declaration needs at once (types, definition
  values, recursor rules) are added from the pending records, and the
  rest (a theorem's proof, mostly) moves to a compact store of words with
  references either to arena ids or to other stored records. A later
  declaration that needs a stored term adds it then.
- A regular file is parsed on several threads (`--threads`): each parses
  chunks of whole lines, and their batches are applied in file order on
  one thread.
- An export lists each term once, so expressions are added without
  hash-consing and indexed at the end, on all threads. If two are equal
  after all (an export that repeats a term), the file is read again with
  hash-consing.

`NITROLEAN_READ_PROFILE=1` prints the time of the read and of the index.
