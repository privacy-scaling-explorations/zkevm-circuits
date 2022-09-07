cargo fmt
cargo clippy  -- -Dwarnings -W clippy::pedantic
cargo update
cargo test
cargo outdated --root-deps-only
