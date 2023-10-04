use eyre::Result;

pub mod circuit;
pub mod server;
pub mod tests;
pub mod utils;

#[tokio::main]
async fn main() -> Result<()> {
    server::serve().await
}
