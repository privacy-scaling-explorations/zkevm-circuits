#!/bin/bash
#set -e 
#set -x

prnumber=$1
base_dir="/home/ubuntu/CI_Prover_Benches/"
target_dir="$base_dir"PR"$1"

_revision=$2

echo $_revision

oldrev=$(egrep halo2.*rev $target_dir/Cargo.toml | awk -F\" '{ print $4 }')

sed -i "s/$oldrev/$_revision/g" $target_dir/Cargo.toml
