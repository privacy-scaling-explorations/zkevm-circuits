FROM alpine:3.15.6 AS build

WORKDIR /solidity

RUN apk update && apk add boost-dev boost-static build-base cmake git

RUN git clone https://github.com/ethereum/solidity .
RUN git checkout 8f2595957bfc0f3cd18ca29240dabcd6b2122dfd
COPY patch.diff patch.diff
RUN patch -p1 < patch.diff

WORKDIR /solidity/build
RUN cmake .. -DCMAKE_BUILD_TYPE=Release -DLLL=1
RUN make -j2

ENTRYPOINT ["/solidity/build/lllc/lllc"]
