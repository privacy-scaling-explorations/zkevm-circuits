#!/bin/bash
set -x

export PATH=/home/ubuntu/.cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/snap/bin:/usr/local/go/bin/

error() {
  sudo poweroff
}

trap 'error' ERR

suite=$1

cd zkevm-circuits/testool
../target/release/testool --suite $suite --report

exit 0
