#!/bin/bash
set -eo pipefail

# Function to check if sysstat is installed
check_sysstat_installed() {
  if command -v sar &>/dev/null; then
    echo "sysstat is already installed."
    return 0
  else
    echo "sysstat is not installed."
    return 1
  fi
}

# Function to install sysstat
install_sysstat() {
  if [[ -f /etc/os-release ]]; then
    source /etc/os-release
    if [[ $ID == "ubuntu" || $ID == "debian" ]]; then
      sudo apt update
      sudo apt install -y sysstat
    elif [[ $ID == "centos" || $ID == "rhel" ]]; then
      sudo yum install -y sysstat
    else
      echo "Unsupported operating system. Please install sysstat manually."
      exit 1
    fi
  else
    echo "Cannot determine the operating system. Please install sysstat manually."
    exit 1
  fi
}

# Function to enable sysstat service
enable_sysstat_service() {
  sudo systemctl enable sysstat
  sudo systemctl start sysstat
  echo "sysstat service has been enabled and started."
}

# Main script
sudo timedatectl set-timezone UTC
check_sysstat_installed
if [[ $? -ne 0 ]]; then
  install_sysstat
fi

enable_sysstat_service

