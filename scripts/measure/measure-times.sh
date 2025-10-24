#!/bin/zsh

mkdir -p results/series

sudo cpupower frequency-set --governor performance

for i in {1..10}
do
    echo "Run $i ..."
    cargo verus verify -- \
        --time-expanded \
        --output-json \
        > results/series/time-results-$i.json
done

sudo cpupower frequency-set --governor schedutil
