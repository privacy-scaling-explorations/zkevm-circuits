#!/bin/bash
cd "$(dirname "$0")" || exit 1

GITHUB_RUN_ID=$1

PROVER_INSTANCE=$(cat "$HOME/CI_Github_Trigger/$GITHUB_RUN_ID/prover_instance")
echo "Prover instance at trigger: $PROVER_INSTANCE"

export PROVER_IP=$(tccli cvm DescribeInstances --InstanceIds "[\"$PROVER_INSTANCE\"]" | grep -A 1 PublicIpAddress | egrep -o '[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3}')
echo "Prover IP: $PROVER_IP"

rm ~/.ssh/known_hosts*

ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP "bash -s" -- <00_installGo.sh
ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP "bash -s" -- <00_installRust.sh
ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP "bash -s" -- <01_installDeps.sh
ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP "bash -s" -- <02_setup.sh

RESULT=""
run_single_benchmark() {
  local DEGREE=$1
  local CIRCUIT=$2

  ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP "bash -s" -- "$GITHUB_RUN_ID" <03_prepareProver.sh
  ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP "bash -s" -- "$GITHUB_RUN_ID" <04_clone.sh
  ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP "bash -s" -- "$GITHUB_RUN_ID" <05_build.sh
  ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP "bash -s" -- <06_rsSysstat.sh &
  sleep 5

  ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP "bash -s" -- "$DEGREE" "$CIRCUIT" "$GITHUB_RUN_ID" <07_execBench.sh
  declare -g RESULT=$?
  chmod u+x 08_processResults.sh
  ./08_processResults.sh "$CIRCUIT" "$DEGREE"
}

words="exp evm tx bytecode state pi copy super keccak"

for word in $words; do
  case "$word" in
  evm)
    # Run script for evm
    echo "Running script for evm..."
    run_single_benchmark 19 evm
    ;;
  keccak)
    # Run script for keccak
    echo "Running script for keccak..."
    run_single_benchmark 19 keccak
    ;;
  state)
    # Run script for state
    echo "Running script for state..."
    run_single_benchmark 19 state
    ;;
  tx)
    # Run script for tx
    echo "Running script for tx..."
    run_single_benchmark 19 tx
    ;;
  super)
    # Run script for super
    echo "Running script for super..."
    run_single_benchmark 19 super
    ;;
  bytecode)
    # Run script for bytecode
    echo "Running script for bytecode..."
    run_single_benchmark 19 bytecode
    ;;
  pi)
    # Run script for pi
    echo "Running script for pi..."
    run_single_benchmark 19 pi
    ;;
  exp)
    # Run script for exp
    echo "Running script for exp..."
    run_single_benchmark 19 exp
    ;;
  copy)
    # Run script for copy
    echo "Running script for copy..."
    run_single_benchmark 19 copy
    ;;
  *)
    echo "Unknown word: $word"
    ;;
  esac
done

kill_ssh() {
  sleep 30
  # Get the list of process IDs with the given IP address
  pids=$(ps aux | grep "$PROVER_IP" | grep -v "grep" | awk '{print $2}')

  # Loop through the process IDs and kill them
  for pid in $pids; do
    echo "Killing process with PID: $pid"
    kill "$pid"
  done
}

kill_ssh &

echo "Exiting bench-results-local-trigger with RESULT $RESULT"
exit $RESULT
