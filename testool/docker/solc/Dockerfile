FROM alpine:3.15.6 AS build

WORKDIR /solidity

RUN apk update && apk add boost-dev boost-static build-base cmake git

RUN git clone https://github.com/ethereum/solidity .
RUN git checkout v0.8.17

WORKDIR /solidity/build
RUN cmake .. -DCMAKE_BUILD_TYPE=Release
RUN make -j16

ENTRYPOINT ["/solidity/build/solc/solc"]
