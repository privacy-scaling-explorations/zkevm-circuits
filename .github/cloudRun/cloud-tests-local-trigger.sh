#!/bin/bash
set -eo pipefail

cd "$(dirname "$0")" || exit 1

GITHUB_RUN_ID=$1
BRANCH_NAME=$2

PROVER_INSTANCE=$(cat "$HOME/CI_Github_Trigger/$GITHUB_RUN_ID/prover_instance")
echo "Prover instance at trigger: $PROVER_INSTANCE"

export PROVER_IP=$(tccli cvm DescribeInstances --InstanceIds "[\"$PROVER_INSTANCE\"]" | grep -A 1 PublicIpAddress | egrep -o '[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3}')
echo "Prover IP: $PROVER_IP"

rm ~/.ssh/known_hosts*

prepare_env() {
  ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@"$PROVER_IP" "bash -s" -- <../weeklyBenchScripts/00_installGo.sh
  ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@"$PROVER_IP" "bash -s" -- <../weeklyBenchScripts/00_installRust.sh
  ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@"$PROVER_IP" "bash -s" -- <../weeklyBenchScripts/01_installDeps.sh
  ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@"$PROVER_IP" "bash -s" -- <../weeklyBenchScripts/02_setup.sh
}

prepare_repo() {
  ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@"$PROVER_IP" "bash -s" -- "$GITHUB_RUN_ID" <../weeklyBenchScripts/03_prepareProver.sh
  ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@"$PROVER_IP" "bash -s" -- "$GITHUB_RUN_ID" "$BRANCH_NAME" <../weeklyBenchScripts/04_clone.sh
  ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@"$PROVER_IP" "bash -s" -- "$GITHUB_RUN_ID" <../weeklyBenchScripts/05_build.sh

}

prepare_env
prepare_repo

ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@"$PROVER_IP" "bash -s" -- "$GITHUB_RUN_ID" <run.sh
scp -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@"$PROVER_IP":"$HOME"/CI_Prover_Benches/"$GITHUB_RUN_ID"/run_result ../../../
RESULT=$(cat ../../../run_result)
echo "exiting cloud-tests-local-trigger with RESULT $RESULT"
exit "$RESULT"
