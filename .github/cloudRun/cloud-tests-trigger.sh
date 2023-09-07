#!/bin/bash
set -eo pipefail

GITHUB_RUN_ID=$1
BRANCH_NAME=$2

ensure_git_installed() {
  if ! command -v git &>/dev/null; then
    echo "Git is not installed. Installing..."
    sudo apt update
    sudo apt install -y git
  else
    echo "Git is already installed."
  fi
}

ensure_git_installed

clone_zkevm-circuits() {
  git clone -q https://github.com/taikoxyz/zkevm-circuits.git
  cd zkevm-circuits || exit 1
  git checkout "$BRANCH_NAME"
  echo "Cloned zkevm-circuits"
}

directory_name="$HOME/CI_Github_Trigger/$GITHUB_RUN_ID"
cd "$directory_name" || exit 1


clone_zkevm-circuits

cd .github/cloudRun || exit 1
chmod u+x cloud-tests-local-trigger.sh
./cloud-tests-local-trigger.sh "$GITHUB_RUN_ID" "$BRANCH_NAME"
RESULT=$?
echo "exiting cloud-tests-trigger with result $RESULT"
exit $RESULT
