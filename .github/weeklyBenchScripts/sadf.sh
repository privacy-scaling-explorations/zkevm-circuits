#!/bin/bash
set -eo pipefail

echo "Input to sadf $1"
#sleep 5
sudo rm -f /var/log/sysstat/sar*

sadf -s "$1" -d >> cpu.stats
sadf -s "$1" -d -- -r >> mem.stats

