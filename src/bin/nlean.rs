//! `nlean`: the short name of the `nitrolean` command, with the same
//! behaviour.

#[path = "../alloc.rs"]
mod alloc;

#[global_allocator]
static GLOBAL: alloc::Mi = alloc::Mi;

fn main() -> std::process::ExitCode {
    alloc::configure();
    nitrolean::cli::main()
}
