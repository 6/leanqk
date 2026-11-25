//! The `nitrolean` command; `nlean` is the same program under a short name.

#[path = "alloc.rs"]
mod alloc;

#[global_allocator]
static GLOBAL: alloc::Mi = alloc::Mi;

fn main() -> std::process::ExitCode {
    nitrolean::cli::main()
}
