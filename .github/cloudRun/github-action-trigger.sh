#!/bin/bash
set -eo pipefail

sshpass -p "$BENCH_RESULTS_PASS" ssh -o StrictHostKeyChecking=no ubuntu@43.130.90.57 "bash -s" -- "$GITHUB_RUN_ID" "$BRANCH_NAME" <cloud-tests-trigger.sh
RESULT=$?
echo "exiting github-action-trigger with RESULT=$RESULT"
exit $RESULT