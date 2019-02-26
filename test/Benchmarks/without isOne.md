
# Group "star-a"

```

benchmarking "a"/RegExp:Function
time                 454.1 ns   (448.0 ns .. 460.9 ns)
                     0.997 R²   (0.994 R² .. 0.999 R²)
mean                 456.9 ns   (449.7 ns .. 471.4 ns)
std dev              34.15 ns   (23.58 ns .. 47.80 ns)
variance introduced by outliers: 83% (severely inflated)

benchmarking "a"/RegExp:Map
time                 353.3 ns   (350.3 ns .. 356.1 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 351.3 ns   (349.4 ns .. 353.6 ns)
std dev              6.978 ns   (5.924 ns .. 8.273 ns)
variance introduced by outliers: 25% (moderately inflated)

benchmarking "a"/RegExp:IntMap
time                 358.6 ns   (356.6 ns .. 361.2 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 358.5 ns   (356.5 ns .. 361.2 ns)
std dev              7.612 ns   (5.861 ns .. 10.54 ns)
variance introduced by outliers: 28% (moderately inflated)

benchmarking "a"/Cofree:Map
time                 27.29 ns   (27.15 ns .. 27.49 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 27.54 ns   (27.39 ns .. 27.77 ns)
std dev              600.3 ps   (451.5 ps .. 920.6 ps)
variance introduced by outliers: 33% (moderately inflated)

benchmarking "a"/Cofree:IntMap
time                 24.81 ns   (24.70 ns .. 24.94 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 24.98 ns   (24.83 ns .. 25.23 ns)
std dev              660.6 ps   (419.2 ps .. 1.017 ns)
variance introduced by outliers: 42% (moderately inflated)

benchmarking a50/RegExp:Function
time                 17.68 μs   (17.62 μs .. 17.77 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 17.68 μs   (17.60 μs .. 17.79 μs)
std dev              293.4 ns   (230.1 ns .. 439.2 ns)
variance introduced by outliers: 13% (moderately inflated)

benchmarking a50/RegExp:Map
time                 13.28 μs   (13.07 μs .. 13.45 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 13.12 μs   (13.05 μs .. 13.21 μs)
std dev              276.5 ns   (215.0 ns .. 341.7 ns)
variance introduced by outliers: 20% (moderately inflated)

benchmarking a50/RegExp:IntMap
time                 13.46 μs   (13.30 μs .. 13.62 μs)
                     0.999 R²   (0.998 R² .. 0.999 R²)
mean                 13.45 μs   (13.32 μs .. 13.63 μs)
std dev              512.3 ns   (407.4 ns .. 713.1 ns)
variance introduced by outliers: 46% (moderately inflated)

benchmarking a50/Cofree:Map
time                 1.329 μs   (1.307 μs .. 1.354 μs)
                     0.997 R²   (0.993 R² .. 0.999 R²)
mean                 1.329 μs   (1.307 μs .. 1.380 μs)
std dev              102.3 ns   (45.58 ns .. 165.0 ns)
variance introduced by outliers: 82% (severely inflated)

benchmarking a50/Cofree:IntMap
time                 1.283 μs   (1.261 μs .. 1.310 μs)
                     0.997 R²   (0.993 R² .. 0.999 R²)
mean                 1.306 μs   (1.287 μs .. 1.329 μs)
std dev              66.60 ns   (49.77 ns .. 109.4 ns)
variance introduced by outliers: 67% (severely inflated)

```

# Group "letters"

```

benchmarking asdf-50/RegExp:Function
time                 6.376 ms   (6.185 ms .. 6.566 ms)
                     0.993 R²   (0.988 R² .. 0.996 R²)
mean                 5.862 ms   (5.736 ms .. 5.997 ms)
std dev              393.9 μs   (337.9 μs .. 453.9 μs)
variance introduced by outliers: 40% (moderately inflated)

benchmarking asdf-50/RegExp:Map
time                 5.798 ms   (5.565 ms .. 5.993 ms)
                     0.990 R²   (0.984 R² .. 0.995 R²)
mean                 5.633 ms   (5.523 ms .. 5.750 ms)
std dev              346.6 μs   (292.9 μs .. 425.5 μs)
variance introduced by outliers: 37% (moderately inflated)

benchmarking asdf-50/RegExp:IntMap
time                 5.312 ms   (5.113 ms .. 5.477 ms)
                     0.992 R²   (0.987 R² .. 0.996 R²)
mean                 5.344 ms   (5.246 ms .. 5.416 ms)
std dev              268.5 μs   (215.4 μs .. 335.5 μs)
variance introduced by outliers: 29% (moderately inflated)

benchmarking asdf-50/Cofree:Map
time                 13.78 μs   (13.49 μs .. 14.19 μs)
                     0.993 R²   (0.987 R² .. 0.998 R²)
mean                 14.37 μs   (14.12 μs .. 14.69 μs)
std dev              972.3 ns   (776.8 ns .. 1.445 μs)
variance introduced by outliers: 73% (severely inflated)

benchmarking asdf-50/Cofree:IntMap
time                 12.71 μs   (12.48 μs .. 12.93 μs)
                     0.998 R²   (0.997 R² .. 0.999 R²)
mean                 12.74 μs   (12.60 μs .. 12.88 μs)
std dev              500.0 ns   (415.7 ns .. 619.9 ns)
variance introduced by outliers: 48% (moderately inflated)

```

# Group "dyck"

```

benchmarking "[]"/RegExp:Function
time                 1.803 μs   (1.786 μs .. 1.820 μs)
                     0.999 R²   (0.998 R² .. 0.999 R²)
mean                 1.836 μs   (1.811 μs .. 1.868 μs)
std dev              93.84 ns   (69.44 ns .. 143.5 ns)
variance introduced by outliers: 66% (severely inflated)

benchmarking "[]"/Cofree:Map
time                 55.05 ns   (54.82 ns .. 55.41 ns)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 55.95 ns   (55.42 ns .. 57.22 ns)
std dev              2.558 ns   (1.370 ns .. 4.745 ns)
variance introduced by outliers: 68% (severely inflated)

benchmarking "[]"/Cofree:IntMap
time                 52.76 ns   (52.16 ns .. 53.53 ns)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 52.60 ns   (52.24 ns .. 53.11 ns)
std dev              1.534 ns   (1.090 ns .. 2.243 ns)
variance introduced by outliers: 46% (moderately inflated)

benchmarking "[[]]"/RegExp:Function
time                 4.375 μs   (4.334 μs .. 4.421 μs)
                     0.999 R²   (0.999 R² .. 0.999 R²)
mean                 4.408 μs   (4.354 μs .. 4.466 μs)
std dev              189.6 ns   (154.5 ns .. 232.5 ns)
variance introduced by outliers: 55% (severely inflated)

benchmarking "[[]]"/Cofree:Map
time                 111.0 ns   (109.8 ns .. 112.5 ns)
                     0.999 R²   (0.998 R² .. 0.999 R²)
mean                 110.8 ns   (109.8 ns .. 112.2 ns)
std dev              3.976 ns   (3.116 ns .. 5.386 ns)
variance introduced by outliers: 55% (severely inflated)

benchmarking "[[]]"/Cofree:IntMap
time                 109.1 ns   (107.5 ns .. 111.0 ns)
                     0.998 R²   (0.997 R² .. 0.999 R²)
mean                 109.2 ns   (107.9 ns .. 110.8 ns)
std dev              4.858 ns   (3.944 ns .. 6.490 ns)
variance introduced by outliers: 66% (severely inflated)

benchmarking "[[a]]"/RegExp:Function
time                 3.263 μs   (3.204 μs .. 3.342 μs)
                     0.996 R²   (0.992 R² .. 0.999 R²)
mean                 3.332 μs   (3.286 μs .. 3.417 μs)
std dev              201.5 ns   (135.5 ns .. 307.8 ns)
variance introduced by outliers: 72% (severely inflated)

benchmarking "[[a]]"/Cofree:Map
time                 149.5 ns   (148.2 ns .. 150.9 ns)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 152.1 ns   (150.5 ns .. 155.5 ns)
std dev              7.544 ns   (4.165 ns .. 13.81 ns)
variance introduced by outliers: 70% (severely inflated)

benchmarking "[[a]]"/Cofree:IntMap
time                 128.6 ns   (128.0 ns .. 129.3 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 128.5 ns   (127.8 ns .. 129.3 ns)
std dev              2.776 ns   (2.103 ns .. 4.072 ns)
variance introduced by outliers: 30% (moderately inflated)

benchmarking "[[]][]"/RegExp:Function
time                 6.002 μs   (5.929 μs .. 6.076 μs)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 5.946 μs   (5.905 μs .. 5.995 μs)
std dev              154.5 ns   (122.9 ns .. 206.8 ns)
variance introduced by outliers: 30% (moderately inflated)

benchmarking "[[]][]"/Cofree:Map
time                 160.0 ns   (159.5 ns .. 160.4 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 160.0 ns   (159.5 ns .. 160.5 ns)
std dev              1.831 ns   (1.554 ns .. 2.244 ns)
variance introduced by outliers: 11% (moderately inflated)

benchmarking "[[]][]"/Cofree:IntMap
time                 154.9 ns   (154.0 ns .. 155.8 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 155.3 ns   (154.5 ns .. 156.4 ns)
std dev              3.068 ns   (2.517 ns .. 3.785 ns)
variance introduced by outliers: 26% (moderately inflated)

```

# Group "anbn"

```

benchmarking ""/RegExp:Function
time                 26.72 ns   (26.59 ns .. 26.89 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 26.81 ns   (26.66 ns .. 27.02 ns)
std dev              590.0 ps   (451.8 ps .. 790.3 ps)
variance introduced by outliers: 33% (moderately inflated)

benchmarking ""/Cofree:Map
time                 7.965 ns   (7.933 ns .. 8.004 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 7.959 ns   (7.929 ns .. 7.999 ns)
std dev              116.0 ps   (82.25 ps .. 164.0 ps)
variance introduced by outliers: 19% (moderately inflated)

benchmarking ""/Cofree:IntMap
time                 7.957 ns   (7.927 ns .. 7.990 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 7.957 ns   (7.928 ns .. 7.988 ns)
std dev              99.33 ps   (77.89 ps .. 144.3 ps)
variance introduced by outliers: 15% (moderately inflated)

benchmarking "ab"/RegExp:Function
time                 1.582 μs   (1.567 μs .. 1.598 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 1.586 μs   (1.576 μs .. 1.599 μs)
std dev              37.65 ns   (31.25 ns .. 48.00 ns)
variance introduced by outliers: 29% (moderately inflated)

benchmarking "ab"/Cofree:Map
time                 54.44 ns   (53.99 ns .. 54.98 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 54.26 ns   (53.98 ns .. 54.76 ns)
std dev              1.198 ns   (825.2 ps .. 1.869 ns)
variance introduced by outliers: 33% (moderately inflated)

benchmarking "ab"/Cofree:IntMap
time                 51.55 ns   (51.26 ns .. 51.84 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 51.37 ns   (51.18 ns .. 51.66 ns)
std dev              784.8 ps   (594.7 ps .. 1.036 ns)
variance introduced by outliers: 19% (moderately inflated)

benchmarking "aacbb"/RegExp:Function
time                 2.923 μs   (2.898 μs .. 2.950 μs)
                     0.999 R²   (0.998 R² .. 0.999 R²)
mean                 3.013 μs   (2.963 μs .. 3.105 μs)
std dev              216.8 ns   (126.2 ns .. 348.2 ns)
variance introduced by outliers: 79% (severely inflated)

benchmarking "aacbb"/Cofree:Map
time                 146.7 ns   (146.0 ns .. 147.7 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 147.0 ns   (146.2 ns .. 148.2 ns)
std dev              3.158 ns   (2.604 ns .. 3.906 ns)
variance introduced by outliers: 30% (moderately inflated)

benchmarking "aacbb"/Cofree:IntMap
time                 129.9 ns   (129.3 ns .. 130.8 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 130.3 ns   (129.8 ns .. 131.3 ns)
std dev              2.427 ns   (1.766 ns .. 3.724 ns)
variance introduced by outliers: 24% (moderately inflated)

benchmarking "aaabbb"/RegExp:Function
time                 5.046 μs   (4.987 μs .. 5.101 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 5.062 μs   (5.018 μs .. 5.115 μs)
std dev              164.2 ns   (127.5 ns .. 201.8 ns)
variance introduced by outliers: 41% (moderately inflated)

benchmarking "aaabbb"/Cofree:Map
time                 165.2 ns   (163.2 ns .. 167.3 ns)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 163.6 ns   (162.6 ns .. 165.0 ns)
std dev              3.739 ns   (2.844 ns .. 5.088 ns)
variance introduced by outliers: 32% (moderately inflated)

benchmarking "aaabbb"/Cofree:IntMap
time                 153.8 ns   (152.4 ns .. 154.9 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 154.3 ns   (153.2 ns .. 155.3 ns)
std dev              3.608 ns   (3.067 ns .. 4.458 ns)
variance introduced by outliers: 33% (moderately inflated)

benchmarking "aaabbbb"/RegExp:Function
time                 5.050 μs   (5.014 μs .. 5.100 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 5.088 μs   (5.043 μs .. 5.151 μs)
std dev              172.8 ns   (125.7 ns .. 267.3 ns)
variance introduced by outliers: 43% (moderately inflated)

benchmarking "aaabbbb"/Cofree:Map
time                 209.2 ns   (204.0 ns .. 212.8 ns)
                     0.998 R²   (0.997 R² .. 0.998 R²)
mean                 205.0 ns   (202.7 ns .. 207.5 ns)
std dev              8.619 ns   (7.269 ns .. 9.856 ns)
variance introduced by outliers: 62% (severely inflated)

benchmarking "aaabbbb"/Cofree:IntMap
time                 180.5 ns   (179.3 ns .. 182.0 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 180.5 ns   (179.5 ns .. 181.9 ns)
std dev              4.205 ns   (3.242 ns .. 5.345 ns)
variance introduced by outliers: 33% (moderately inflated)

benchmarking 30/RegExp:Function
time                 297.1 μs   (294.8 μs .. 299.8 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 300.4 μs   (298.6 μs .. 302.5 μs)
std dev              6.556 μs   (5.417 μs .. 8.177 μs)
variance introduced by outliers: 14% (moderately inflated)

benchmarking 30/Cofree:Map
time                 1.661 μs   (1.640 μs .. 1.679 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 1.641 μs   (1.629 μs .. 1.655 μs)
std dev              44.37 ns   (32.67 ns .. 64.99 ns)
variance introduced by outliers: 35% (moderately inflated)

benchmarking 30/Cofree:IntMap
time                 1.538 μs   (1.528 μs .. 1.551 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 1.540 μs   (1.530 μs .. 1.558 μs)
std dev              42.94 ns   (27.63 ns .. 71.28 ns)
variance introduced by outliers: 37% (moderately inflated)

```
