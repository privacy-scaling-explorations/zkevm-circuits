#!/bin/bash
set -eo pipefail

echo "Triggering cleanup"
sshpass -p "$BENCH_RESULTS_PASS" ssh -o StrictHostKeyChecking=no ubuntu@43.130.90.57  "bash -s" -- "$GITHUB_RUN_ID" <bench-results-cleanup.sh

echo "Exiting github-action-cleanup"
