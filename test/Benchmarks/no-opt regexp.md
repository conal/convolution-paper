
# Group "star-a"

```

benchmarking "a"/RegExp:Function
time                 368.5 ns   (365.8 ns .. 371.5 ns)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 369.7 ns   (366.8 ns .. 374.1 ns)
std dev              8.669 ns   (6.324 ns .. 12.29 ns)
variance introduced by outliers: 30% (moderately inflated)

benchmarking "a"/RegExp:Map
time                 353.3 ns   (349.8 ns .. 357.2 ns)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 352.4 ns   (350.0 ns .. 355.5 ns)
std dev              6.608 ns   (4.544 ns .. 9.254 ns)
variance introduced by outliers: 21% (moderately inflated)

benchmarking "a"/RegExp:IntMap
time                 355.2 ns   (353.0 ns .. 357.5 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 356.1 ns   (354.0 ns .. 358.0 ns)
std dev              5.292 ns   (4.270 ns .. 6.328 ns)
variance introduced by outliers: 15% (moderately inflated)

benchmarking a50/RegExp:Function
time                 3.266 ms   (3.223 ms .. 3.323 ms)
                     0.998 R²   (0.996 R² .. 0.999 R²)
mean                 3.299 ms   (3.270 ms .. 3.338 ms)
std dev              89.00 μs   (66.92 μs .. 131.0 μs)

benchmarking a50/RegExp:Map
time                 17.97 μs   (17.82 μs .. 18.14 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 18.02 μs   (17.87 μs .. 18.20 μs)
std dev              389.9 ns   (313.0 ns .. 482.6 ns)
variance introduced by outliers: 19% (moderately inflated)

benchmarking a50/RegExp:IntMap
time                 18.62 μs   (18.18 μs .. 19.10 μs)
                     0.997 R²   (0.996 R² .. 0.999 R²)
mean                 18.52 μs   (18.30 μs .. 18.90 μs)
std dev              695.1 ns   (462.1 ns .. 994.4 ns)
variance introduced by outliers: 41% (moderately inflated)

```

# Group "letters"

```

benchmarking asdf-50/RegExp:Function
time                 22.67 s    (22.00 s .. 24.17 s)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 22.39 s    (22.21 s .. 22.57 s)
std dev              227.9 ms   (99.00 ms .. 287.7 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking asdf-50/RegExp:Map
time                 3.334 ms   (3.267 ms .. 3.405 ms)
                     0.998 R²   (0.996 R² .. 0.999 R²)
mean                 3.466 ms   (3.423 ms .. 3.527 ms)
std dev              127.9 μs   (87.80 μs .. 181.3 μs)
variance introduced by outliers: 15% (moderately inflated)

benchmarking asdf-50/RegExp:IntMap
time                 3.114 ms   (3.016 ms .. 3.233 ms)
                     0.996 R²   (0.993 R² .. 0.999 R²)
mean                 3.135 ms   (3.099 ms .. 3.170 ms)
std dev              91.81 μs   (74.63 μs .. 116.6 μs)
variance introduced by outliers: 11% (moderately inflated)

```

# Group "dyck"

```

benchmarking "[]"/RegExp:Function
time                 2.430 μs   (2.410 μs .. 2.450 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 2.440 μs   (2.422 μs .. 2.461 μs)
std dev              51.17 ns   (40.01 ns .. 68.95 ns)
variance introduced by outliers: 22% (moderately inflated)

benchmarking "[[]]"/RegExp:Function
time                 10.70 μs   (10.48 μs .. 10.88 μs)
                     0.998 R²   (0.998 R² .. 0.999 R²)
mean                 10.56 μs   (10.46 μs .. 10.71 μs)
std dev              305.8 ns   (233.4 ns .. 442.1 ns)
variance introduced by outliers: 31% (moderately inflated)

benchmarking "[[a]]"/RegExp:Function
time                 17.56 μs   (17.47 μs .. 17.67 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 17.71 μs   (17.59 μs .. 17.87 μs)
std dev              330.3 ns   (253.1 ns .. 448.6 ns)
variance introduced by outliers: 15% (moderately inflated)

benchmarking "[[]][]"/RegExp:Function
time                 27.58 μs   (27.02 μs .. 28.02 μs)
                     0.999 R²   (0.998 R² .. 0.999 R²)
mean                 27.26 μs   (27.03 μs .. 27.60 μs)
std dev              723.2 ns   (530.5 ns .. 940.6 ns)
variance introduced by outliers: 24% (moderately inflated)

```

# Group "anbn"

```

benchmarking ""/RegExp:Function
time                 28.50 ns   (28.24 ns .. 28.87 ns)
                     0.999 R²   (0.999 R² .. 0.999 R²)
mean                 28.72 ns   (28.40 ns .. 29.03 ns)
std dev              787.8 ps   (681.4 ps .. 974.4 ps)
variance introduced by outliers: 42% (moderately inflated)

benchmarking "ab"/RegExp:Function
time                 2.294 μs   (2.264 μs .. 2.336 μs)
                     0.998 R²   (0.997 R² .. 0.999 R²)
mean                 2.315 μs   (2.283 μs .. 2.368 μs)
std dev              102.2 ns   (68.07 ns .. 136.0 ns)
variance introduced by outliers: 56% (severely inflated)

benchmarking "aacbb"/RegExp:Function
time                 15.73 μs   (15.45 μs .. 16.05 μs)
                     0.998 R²   (0.997 R² .. 0.999 R²)
mean                 15.80 μs   (15.55 μs .. 16.05 μs)
std dev              610.3 ns   (513.3 ns .. 727.4 ns)
variance introduced by outliers: 43% (moderately inflated)

benchmarking "aaabbb"/RegExp:Function
time                 24.06 μs   (23.92 μs .. 24.23 μs)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 24.28 μs   (24.02 μs .. 24.63 μs)
std dev              757.8 ns   (497.2 ns .. 1.004 μs)
variance introduced by outliers: 31% (moderately inflated)

benchmarking "aaabbbb"/RegExp:Function
time                 36.65 μs   (36.48 μs .. 36.87 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 36.85 μs   (36.59 μs .. 37.26 μs)
std dev              802.4 ns   (506.3 ns .. 1.238 μs)
variance introduced by outliers: 18% (moderately inflated)

benchmarking 30/RegExp:Function
time                 96.66 ms   (94.61 ms .. 99.47 ms)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 92.75 ms   (90.01 ms .. 94.29 ms)
std dev              2.748 ms   (1.469 ms .. 3.980 ms)
variance introduced by outliers: 14% (moderately inflated)

```
