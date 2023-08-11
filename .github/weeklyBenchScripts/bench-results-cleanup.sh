#!/bin/bash
GITHUB_RUN_ID=$1
echo "Performing cleanup... $GITHUB_RUN_ID"
sleep 60
PROVER_INSTANCE=$(cat $HOME/CI_Github_Trigger/$GITHUB_RUN_ID/prover_instance)
echo "Prover instance at cleanup: $PROVER_INSTANCE"
tccli cvm TerminateInstances --InstanceIds "[\"$PROVER_INSTANCE\"]" --ReleasePrepaidDataDisk True
echo "Exiting bench-results-local-cleanup"
rm -rf "$HOME/CI_Github_Trigger/$GITHUB_RUN_ID"
exit 0
