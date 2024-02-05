URL=https://drive.google.com/uc\?export\=download\&id\=1ki4OVizAlvDWHqdipJj4svMBNMBQ5cr5
CACHE_FILE=web3_rpc_cache.bin
if [ ! -f "$CACHE_FILE" ]; then
    wget -O $CACHE_FILE $URL
fi
cargo run --release