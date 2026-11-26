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

- An export numbers its expressions densely from 0, children first. The
  reader keeps a record of 8 bytes per expression id, in a table indexed
  by that id: a leaf (`bvar`, `sort`, `const`, literals) is added to the
  arena at once and its record holds its arena id; a compound record holds
  its children's export ids (an application's in the record, the others'
  in a side table), so it costs one push. At a declaration line, the
  terms the declaration needs at once (types, definition values, recursor
  rules) are added to the arena from the table, and their records then
  hold arena ids. The rest (a theorem's proof, mostly) stays in the table;
  a later declaration that needs one of its terms adds it then. If the ids
  are not dense, the reader adds every record to the arena and goes on
  without lazy proofs.
- A theorem's value is built from the table into the checker's store
  (`Env::value_into`) the way the reader adds recent records: its own
  records, from its declaration's first line on, in two passes (one down
  marks the ones the value needs, one up builds them in order, with a
  dense memo). Records of earlier declarations that it uses are in the
  arena already: at the end of the read, the reader adds every record
  that a later declaration's records use (on Mathlib, 7.8M records that
  values would otherwise build again 17M times), so each record left in
  the table belongs to one declaration's value. The value's own nodes go
  to the store with `TermSink::expr_owned`: the store appends them with
  no Env lookup and no table insert, so an equal term built later gets a
  second id, which costs a cache hit at most.
- Lines are read by a byte scanner for the fixed shapes lean4export
  writes (`src/reader/scan.rs`), with no allocation per line. It looks at
  a window of 288 bytes from the line's start; each token checks its
  offset once, so a line longer than the window, or any shape it does not
  know, goes to the general JSON parser. Keys and fixed text are compared
  8 or 16 bytes at a time against a table of words (`Keys`), and numbers
  are read 8 digits at a time.
- Runs of application and binder lines (nine lines in ten) are read in
  one loop (`src/reader/run.rs`) straight into the table: it matches
  their fixed text and reads their numbers, and stops at any line it does
  not take, which the scanner then reads. A constant line (the commonest
  of those) does not end the run: the loop hands it to the scanner and
  goes on. Otherwise the loop makes no calls, so that its state stays in
  registers: records go to a batch of 512, copied into the table after
  it; a line's own id is compared as text with the expected one's, which
  is counted up in a word (and a ninth digit); numbers are read 8 digits
  at a time, a ninth only where the text after the eighth is not what
  follows a number; positions in a line's window are masked rather than
  bounds-checked. The scanner reads strings 8 bytes at a time.
- On one thread (`--threads 1`) the scanner hands each line straight to
  the reader's state, declarations included. The file is memory-mapped
  and read 16 MiB of whole lines at a time; the pages of each step are
  dropped after it, so the map does not add to peak memory. On several,
  with lazy proofs (`src/reader.rs`, `map_lines_par`), the other threads
  run the loop above on chunks of 4 MiB of the mapped file ahead of the
  reader, into tables of their own, guessing each run's first id from
  its first line; the reader takes each chunk in order, adds a run read
  ahead if it starts at the next id and its names are known (on
  Mathlib, 94% of the lines), and reads every other line itself, as on
  one thread. Without lazy proofs, each thread parses chunks of whole
  lines, and their batches are applied in file order on one thread.
- The records since the last declaration line are added in two passes:
  one down marks the records a term needs, one up adds them in order, so
  no stack is needed. Older records are added from a stack.
- An export lists each term once, so expressions are added without
  hash-consing, and their cached data (`ExprData`) is filled in one pass
  over the arena before the index. The index is built at the end, on all
  threads. On one, entries are bucketed by hash, each bucket is sorted,
  and the table is filled in order. The buckets are kept in eight
  groups, each in a memory map of its own that goes back to the system
  once the group is in the table, and the table's slots are written
  only as the buckets reach them, so the two are never all in memory
  at once. If two terms are equal after all (an export that repeats
  one), the file is read again with hash-consing.

`NITROLEAN_READ_PROFILE=1` prints the time of the read and of the index.
