use eyre::Result;

pub mod circuit;
pub mod server;
pub mod tests;
pub mod utils;

#[tokio::main]
async fn main() -> Result<()> {

    if let Some(arg1) = std::env::args().nth(1) {
        if arg1 == "--oracle" {
            println!("Running oracle");
            tests::cache::run_oracle().await?;
        }
    }

    Ok(())

}
