//! The `nitrolean` command; `nlean` is the same program under a short name.

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() -> std::process::ExitCode {
    nitrolean::cli::main()
}
