#!/bin/bash
GITHUB_RUN_ID=$1

ensure_git_installed() {
  if ! command -v git &>/dev/null; then
    echo "Git is not installed. Installing..."
    sudo apt update
    sudo apt install -y git
  else
    echo "Git is already installed."
  fi
}

clone_zkevm-circuits() {
  git clone -q https://github.com/taikoxyz/zkevm-circuits.git
  cd zkevm-circuits || exit 1
  echo "Cloned zkevm-circuits"
}

directory_name="$HOME/CI_Github_Trigger/$GITHUB_RUN_ID"
cd $directory_name || exit 1

ensure_git_installed
clone_zkevm-circuits

cd .github/weeklyBenchScripts || exit 1
chmod u+x bench-results-local-trigger.sh
./bench-results-local-trigger.sh $GITHUB_RUN_ID
RESULT=$?
echo "Exiting bench-results-trigger with RESULT $RESULT"
exit $RESULT
