#!/bin/bash
set -x

error() {
  sudo poweroff
}

trap 'error' ERR

echo "Reports: http://testool-public.s3-website.eu-central-1.amazonaws.com"
echo "Shuting down instance..."
sudo poweroff

exit 0
