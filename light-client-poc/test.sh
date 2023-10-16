cargo build --release
../target/release/light-client-poc --oracle &
ORACLE_PID=$!
cargo test --release --features="disable-keccak" test_block_  -- --ignored --nocapture --test-threads=1
kill $ORACLE_PID
