#!/bin/zsh

mkdir -p results/

for mod in $(cat scripts/measure/modules.txt)
do
    cargo verus verify -- --verify-module $mod --time-expanded --output-json \
        | jq ".[\"times-ms\"].verification.total" >> results/$mod
done
