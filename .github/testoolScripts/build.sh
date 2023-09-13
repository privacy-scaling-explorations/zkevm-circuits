#!/bin/bash
set -x

export PATH=/home/ubuntu/.cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/snap/bin:/usr/local/go/bin/

error() {
  sudo poweroff
}
 
trap 'error' ERR

cd zkevm-circuits/testool
git submodule update --init --recursive ; git submodule update --checkout ; cargo build --release

exit 0
