//! `nlean`: the short name of the `nitrolean` command, with the same
//! behaviour.

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() -> std::process::ExitCode {
    nitrolean::cli::main()
}
