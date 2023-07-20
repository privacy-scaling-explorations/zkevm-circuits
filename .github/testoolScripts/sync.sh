#!/bin/bash
set -x

error() {
  sudo poweroff
}

trap 'error' ERR

aws s3 sync report/ s3://testool-public/

exit 0
