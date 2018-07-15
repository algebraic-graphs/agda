#!/usr/bin/env bash
set -euo pipefail
rm -rf index.agda;
echo "module index where" >> index.agda;
for i in $( find src -name "*.agda" | sed 's/src\/\(.*\)\.agda/\1/' | sed 's/\//\./g' | sort ); do
    echo "import $i" >> index.agda;
done;
agda -i . -i src/ index.agda
rm -rf index.agda;
