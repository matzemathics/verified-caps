sudo cpupower frequency-set --governor performance

for i in {1..10}
do
    setarch `uname -m` -R -- \
    cargo verus verify --\
        --time-expanded\
        --output-json\
        > results/series/time-results-$i.json

    sudo echo test
done

sudo cpupower frequency-set --governor schedutil
