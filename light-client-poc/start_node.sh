GETH=../../go-ethereum

# clean up
rm access-list-* 
rm -rf node/geth

# build geth
(cd $GETH && make)
$GETH/build/bin/geth --datadir ./node init node/zklight.json

# set password for keystore
echo zklight > /tmp/passwd
echo >> /tmp/passwd

# run node
$GETH/build/bin/geth --rpc.enabledeprecatedpersonal --datadir ./node --bootnodes=enode://9bbc27c01a26835e18bfeb08a2c304fff29e406e94210a16d7d3ed09291b8a9c86193de027449eec8e0fbb4ee1b81f77686acbdffc8fd3522681739edfde5abb@127.0.0.1:0?discport=30301 --mine --miner.etherbase=0x5b72551fc886e8dc264b4382811e596291c0bfd4 --unlock=0x5b72551fc886e8dc264b4382811e596291c0bfd4 --http --http.port 8545 --http.api "eth,net,web3,txpool" --http.corsdomain '*' --http.vhosts '*' --allow-insecure-unlock $* < /tmp/passwd
