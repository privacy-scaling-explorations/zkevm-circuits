#!/bin/bash
set -x

error() {
  sudo poweroff
}

trap 'error' ERR

branch=$1

rm -rf zkevm-circuits
git clone https://github.com/ntampakas/zkevm-circuits.git
cd zkevm-circuits/testool
git checkout $branch
ln -s /home/ubuntu/report report

exit 0
