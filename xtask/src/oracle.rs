//! Stub, to be ported.

#[derive(clap::Subcommand)]
pub enum Cmd {}

pub fn main(c: Cmd) -> anyhow::Result<()> {
    match c {}
}
