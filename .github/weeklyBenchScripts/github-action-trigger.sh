#!/bin/bash

echo "Triggering behchmark trigger"
sshpass -p $BENCH_RESULTS_PASS ssh -o StrictHostKeyChecking=no ubuntu@43.130.90.57 "bash -s" -- "$GITHUB_RUN_ID" << EOF
$(<bench-results-trigger.sh)
EOF
RESULT=$?
echo "exiting github-acton-trigger with RESULT $RESULT"
exit $RESULT


