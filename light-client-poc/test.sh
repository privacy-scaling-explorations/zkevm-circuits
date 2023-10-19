cargo run --release -- --cache &
sleep 1
ORACLE_PID=$!
cargo test --release --features="disable-keccak" test_block_  -- --ignored --nocapture --test-threads=1
kill $ORACLE_PID
