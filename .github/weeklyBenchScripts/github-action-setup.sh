#!/bin/bash
set -eo pipefail

ensure_ssh_and_sshpass_installed() {
  # Check if 'ssh' is installed
  if ! command -v ssh &>/dev/null; then
    echo "ssh is not installed. Installing..."
    sudo apt update
    sudo apt install -y openssh-client
  else
    echo "ssh is already installed."
  fi

  # Check if 'sshpass' is installed
  if ! command -v sshpass &>/dev/null; then
    echo "sshpass is not installed. Installing..."
    sudo apt update
    sudo apt install -y sshpass
  else
    echo "sshpass is already installed."
  fi
}

ensure_ssh_and_sshpass_installed

echo "Triggering setup"
sshpass -p "$BENCH_RESULTS_PASS" ssh -o StrictHostKeyChecking=no ubuntu@43.130.90.57  "bash -s" -- "$GITHUB_RUN_ID" <bench-results-setup.sh

echo "Exiting github-action-setup"
