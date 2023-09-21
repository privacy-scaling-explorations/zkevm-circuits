#!/bin/bash
#set -eo pipefail

echo "Killing sadc"
sudo pkill sadc
echo "Cleaning /var/log/sysstat"
sudo rm -rf /var/log/sysstat/*
echo "Running sadc"
nohup sudo /usr/lib/sysstat/sadc -S ALL 10 604800 /var/log/sysstat/ &
disown

