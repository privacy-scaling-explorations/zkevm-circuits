docker-compose build
docker pull ethereum/client-go:stable
docker-compose up -d deployer geth
cargo test --no-run -- --ignored
cd bus-mapping

GethBlock=`curl localhost:8545 -X POST -H "Content-Type: application/json" -d '{"jsonrpc":"2.0","method":"eth_blockNumber","params":[],"id":1}'`

while [ $GethBlock != '{"jsonrpc":"2.0","id":1,"result":"0x2"}' ]
do
    sleep 3
    GethBlock=`curl localhost:8545 -X POST -H "Content-Type: application/json" -d '{"jsonrpc":"2.0","method":"eth_blockNumber","params":[],"id":1}'`
done

cargo test -- --ignored
