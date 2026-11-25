//! nitrolean: an independent, fast, memory-light proof checker for Lean 4.
//!
//! The crate reads Lean's NDJSON kernel export (format 3, as written by
//! `leanexport`) into an [`env::Env`]: hash-consed arenas of names, universe
//! levels and expressions with `u32` ids, plus the declarations. Then
//! [`check::check_env`] type-checks every declaration, following Lean's C++
//! kernel; see the [`check`] module.
//!
//! The data model follows Lean's kernel (`src/kernel`, `src/Lean/Expr.lean`,
//! `src/Lean/Declaration.lean`); the arena-with-ids layout is in the spirit
//! of nanoda_lib and lean4lean, which also read this export format.
//!
//! Big natural literals use [`num_bigint::BigUint`]: pure Rust (no C/GMP
//! dependency to build or audit), MIT/Apache-2.0, mature, and it has every
//! operation the kernel's `Nat` extensions need (arithmetic, `gcd`, bitwise
//! ops and shifts). Literals below 2^64 never reach it: they are stored
//! inline in the 16-byte expression node.

// The one exception is the memory map in `olean::file`.
#![deny(unsafe_code)]

pub mod check;
pub mod cli;
pub mod compare;
pub mod env;
pub mod expr;
mod hash;
mod idmap;
mod intern;
pub mod json;
pub mod level;
pub mod name;
pub mod olean;
pub mod reader;
mod slab;
pub mod stats;
pub mod strings;
