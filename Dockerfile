FROM shinsaku0523/zkevm:latest

COPY . .

RUN cargo test --no-run -- --ignored

# CMD sh web3-utils/script/geth.sh
