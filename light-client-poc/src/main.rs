#[macro_use]
extern crate lazy_static;

use eyre::Result;

pub mod circuit;
pub mod server;
pub mod tests;
pub mod utils;

#[tokio::main]
async fn main() -> Result<()> {

    if let Some(arg1) = std::env::args().nth(1) {
        if arg1 == "--cache" {
            println!("Running cache server");
            tests::web3_rpc_cache::run().await?;
        }
    }

    Ok(())

}
