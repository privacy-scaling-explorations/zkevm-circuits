#!/bin/bash
set -x

error() {
  sudo poweroff
}

trap 'error' ERR

cd report
rm index.html
for i in `ls -r *.html`; do echo "<a href=\"$i\">$i</a> <br>" >> index.html; done

aws s3 sync . s3://testool-public/

exit 0
