#!/bin/bash
set -eo pipefail

GITHUB_RUN_ID=$3
export GOROOT="/usr/local/go"
export GOPATH="$HOME/go"
export PATH="$GOROOT/bin:$GOPATH/bin:$PATH"

# Get the latest temp directory in the home directory
current_dir="$HOME"/CI_Prover_Benches/"$GITHUB_RUN_ID"

target_dir="$current_dir/zkevm-circuits"
k=$1
circuit=$(echo "$2" | awk '{ print $1 }' | tr '[:upper:]' '[:lower:]')
printf -v _date '%(%Y-%m-%d_%H:%M:%S)T' -1

case $circuit in
    "all")
        echo "To be implemented"
        exit 1
        ;;
    "evm")
        run_suffix="evm_circuit_prover"
        ;;
    "keccak")
        run_suffix="keccak_round"
        ;;
    "state")
        run_suffix="state_circuit_prover"
        ;;
    "tx")
        run_suffix="tx_circuit_prover"
        ;;
    "super")
        run_suffix="super_circuit_prover"
        ;;
    "bytecode")
        run_suffix="bytecode_circuit_prover"
        ;;
    "pi")
        run_suffix="pi_circuit_prover"
        ;;
    "exp")
        run_suffix="exp_circuit_prover"
        ;;
    "copy")
        run_suffix="copy_circuit_prover"
        ;;
    *)
        echo "No proper value"
        exit 1
        ;;
esac

cd "$target_dir";

mkdir ../results
logfile="$_date"--"${circuit}"_bench-"$k".proverlog

current_time=$(date +'%H:%M:%S')
echo "Current time: $current_time"
echo "$current_time" > ~/bench_begin
export RUST_BACKTRACE=1
echo "DEGREE=$k ~/.cargo/bin/cargo test --profile bench bench_${run_suffix} -p circuit-benchmarks --features benches  -- --nocapture > \"$target_dir/results/$logfile\" 2>&1"
DEGREE=$k ~/.cargo/bin/cargo test --profile bench bench_${run_suffix} -p circuit-benchmarks --features benches  -- --nocapture > "$target_dir/../results/$logfile" 2>&1
