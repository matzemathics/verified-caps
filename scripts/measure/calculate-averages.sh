for mod in $(ls $1)
do
    awk '{sum += $0; sumsq += ($0)^2}
         END{ printf "%s: \t %f ms ± %f ms \n", FILENAME, sum/NR, sqrt((sumsq-sum^2/NR)/NR) }
         ' $1/$mod
done