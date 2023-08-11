#!/bin/bash
GITHUB_RUN_ID=$1

export GOROOT="/usr/local/go"
export GOPATH="$HOME/go"
export PATH="$GOROOT/bin:$GOPATH/bin:$PATH"

# Get the latest temp directory in the home directory
current_dir="$HOME"/CI_Prover_Benches/"$GITHUB_RUN_ID"

if [ -z "$current_dir" ]; then
    echo "No temp directory found starting with 'CI_Prover_Benches__' in the home directory."
    exit 1
fi

echo "Building zkevm-circuits inside: $current_dir"
cd "$current_dir/zkevm-circuits" || exit 1
~/.cargo/bin/cargo build -q

