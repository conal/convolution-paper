
# Group "star-a"

```

benchmarking "a"/RegExp:Function
time                 442.4 ns   (439.5 ns .. 445.7 ns)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 445.6 ns   (441.9 ns .. 453.1 ns)
std dev              12.18 ns   (6.401 ns .. 18.36 ns)
variance introduced by outliers: 36% (moderately inflated)

benchmarking "a"/RegExp:Map
time                 355.3 ns   (352.7 ns .. 359.3 ns)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 355.7 ns   (353.3 ns .. 362.4 ns)
std dev              10.04 ns   (4.439 ns .. 17.40 ns)
variance introduced by outliers: 38% (moderately inflated)

benchmarking "a"/RegExp:IntMap
time                 352.6 ns   (350.9 ns .. 354.6 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 352.8 ns   (351.3 ns .. 354.6 ns)
std dev              4.295 ns   (3.512 ns .. 5.377 ns)
variance introduced by outliers: 10% (moderately inflated)

benchmarking a50/RegExp:Function
time                 15.00 μs   (14.89 μs .. 15.13 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 15.06 μs   (14.96 μs .. 15.34 μs)
std dev              377.3 ns   (172.8 ns .. 715.1 ns)
variance introduced by outliers: 24% (moderately inflated)

benchmarking a50/RegExp:Map
time                 10.59 μs   (10.54 μs .. 10.63 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 10.62 μs   (10.58 μs .. 10.67 μs)
std dev              114.1 ns   (84.24 ns .. 153.1 ns)

benchmarking a50/RegExp:IntMap
time                 10.27 μs   (10.21 μs .. 10.33 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 10.29 μs   (10.23 μs .. 10.39 μs)
std dev              195.7 ns   (131.9 ns .. 276.0 ns)
variance introduced by outliers: 16% (moderately inflated)

```

# Group "letters"

```

benchmarking asdf-50/RegExp:Function
time                 3.994 ms   (3.951 ms .. 4.040 ms)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 4.023 ms   (3.990 ms .. 4.055 ms)
std dev              81.76 μs   (61.86 μs .. 108.6 μs)

benchmarking asdf-50/RegExp:Map
time                 3.231 ms   (3.190 ms .. 3.273 ms)
                     0.999 R²   (0.998 R² .. 0.999 R²)
mean                 3.287 ms   (3.259 ms .. 3.329 ms)
std dev              86.04 μs   (57.24 μs .. 129.6 μs)

benchmarking asdf-50/RegExp:IntMap
time                 3.215 ms   (3.043 ms .. 3.354 ms)
                     0.985 R²   (0.976 R² .. 0.992 R²)
mean                 3.006 ms   (2.939 ms .. 3.099 ms)
std dev              203.4 μs   (172.1 μs .. 259.5 μs)
variance introduced by outliers: 37% (moderately inflated)

```

# Group "dyck"

```

benchmarking "[]"/RegExp:Function
time                 1.824 μs   (1.793 μs .. 1.858 μs)
                     0.996 R²   (0.993 R² .. 0.998 R²)
mean                 1.863 μs   (1.823 μs .. 1.917 μs)
std dev              129.6 ns   (85.15 ns .. 219.4 ns)
variance introduced by outliers: 77% (severely inflated)

benchmarking "[[]]"/RegExp:Function
time                 4.037 μs   (4.008 μs .. 4.076 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 4.055 μs   (4.023 μs .. 4.097 μs)
std dev              94.03 ns   (69.75 ns .. 125.5 ns)
variance introduced by outliers: 24% (moderately inflated)

benchmarking "[[a]]"/RegExp:Function
time                 3.054 μs   (3.018 μs .. 3.095 μs)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 3.059 μs   (3.025 μs .. 3.102 μs)
std dev              92.42 ns   (67.31 ns .. 126.8 ns)
variance introduced by outliers: 36% (moderately inflated)

benchmarking "[[]][]"/RegExp:Function
time                 5.524 μs   (5.461 μs .. 5.599 μs)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 5.509 μs   (5.468 μs .. 5.567 μs)
std dev              125.9 ns   (98.77 ns .. 165.2 ns)
variance introduced by outliers: 23% (moderately inflated)

```

# Group "anbn"

```

benchmarking ""/RegExp:Function
time                 27.07 ns   (26.89 ns .. 27.25 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 27.02 ns   (26.88 ns .. 27.22 ns)
std dev              397.1 ps   (275.1 ps .. 561.2 ps)
variance introduced by outliers: 17% (moderately inflated)

benchmarking "ab"/RegExp:Function
time                 1.486 μs   (1.475 μs .. 1.498 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 1.485 μs   (1.473 μs .. 1.500 μs)
std dev              31.58 ns   (21.79 ns .. 48.42 ns)
variance introduced by outliers: 23% (moderately inflated)

benchmarking "aacbb"/RegExp:Function
time                 2.666 μs   (2.645 μs .. 2.684 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 2.654 μs   (2.641 μs .. 2.674 μs)
std dev              37.57 ns   (27.44 ns .. 50.11 ns)
variance introduced by outliers: 11% (moderately inflated)

benchmarking "aaabbb"/RegExp:Function
time                 4.693 μs   (4.667 μs .. 4.717 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 4.685 μs   (4.662 μs .. 4.707 μs)
std dev              60.54 ns   (48.42 ns .. 83.94 ns)

benchmarking "aaabbbb"/RegExp:Function
time                 4.780 μs   (4.739 μs .. 4.822 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 4.762 μs   (4.724 μs .. 4.824 μs)
std dev              122.1 ns   (84.35 ns .. 193.5 ns)
variance introduced by outliers: 28% (moderately inflated)

benchmarking 30/RegExp:Function
time                 278.9 μs   (277.7 μs .. 280.5 μs)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 283.1 μs   (280.7 μs .. 291.4 μs)
std dev              10.39 μs   (4.486 μs .. 20.61 μs)
variance introduced by outliers: 27% (moderately inflated)

```
