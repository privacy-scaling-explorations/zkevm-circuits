#!/bin/bash
#set -e 
#set -x

prnumber=$1
base_dir="/home/ubuntu/CI_Prover_Benches/"
target_dir="$base_dir"PR"$1"
source_dir=$2

mkdir -p $target_dir

# Install a recent go toolchain
wget https://go.dev/dl/go1.22.2.linux-amd64.tar.gz
sudo rm -rf /usr/local/go && sudo tar -C /usr/local -xzf go1.22.2.linux-amd64.tar.gz
