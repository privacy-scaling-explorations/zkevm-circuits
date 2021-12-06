docker-compose build
docker pull ethereum/client-go:stable
docker-compose up -d deployer geth
cd bus-mapping
cargo test --no-run --features geth_rpc_test

GethBlock=`curl localhost:8545 -X POST -H "Content-Type: application/json" -d '{"jsonrpc":"2.0","method":"eth_blockNumber","params":[],"id":1}'`

while [ $GethBlock != '{"jsonrpc":"2.0","id":1,"result":"0x2"}' ]
do
    sleep 3
    GethBlock=`curl localhost:8545 -X POST -H "Content-Type: application/json" -d '{"jsonrpc":"2.0","method":"eth_blockNumber","params":[],"id":1}'`
done

cargo test test_get_block_by_number --features geth_rpc_test
cargo test test_get_block_by_hash --features geth_rpc_test
cargo test test_get_contract_code --features geth_rpc_test
cargo test test_trace_block_by_hash --features geth_rpc_test
cargo test test_trace_block_by_number --features geth_rpc_test
cargo test test_get_proof --features geth_rpc_test
