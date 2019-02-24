
# Group "star-a"

```

benchmarking "a"/RegExp:Function
time                 448.9 ns   (442.9 ns .. 456.6 ns)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 454.3 ns   (449.1 ns .. 476.1 ns)
std dev              29.27 ns   (9.824 ns .. 68.71 ns)
variance introduced by outliers: 78% (severely inflated)

benchmarking "a"/RegExp:Map
time                 364.0 ns   (361.2 ns .. 367.4 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 364.1 ns   (361.8 ns .. 366.6 ns)
std dev              8.325 ns   (6.594 ns .. 10.44 ns)
variance introduced by outliers: 31% (moderately inflated)

benchmarking "a"/RegExp:IntMap
time                 363.0 ns   (358.2 ns .. 368.2 ns)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 362.9 ns   (360.2 ns .. 366.3 ns)
std dev              11.06 ns   (8.428 ns .. 16.36 ns)
variance introduced by outliers: 44% (moderately inflated)

benchmarking "a"/LTrie:Map
time                 25.71 ns   (25.48 ns .. 25.97 ns)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 25.64 ns   (25.50 ns .. 25.84 ns)
std dev              554.5 ps   (431.9 ps .. 735.4 ps)
variance introduced by outliers: 33% (moderately inflated)

benchmarking "a"/LTrie:IntMap
time                 24.44 ns   (24.29 ns .. 24.60 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 24.48 ns   (24.36 ns .. 24.60 ns)
std dev              414.3 ps   (336.1 ps .. 563.0 ps)
variance introduced by outliers: 23% (moderately inflated)

benchmarking a50/RegExp:Function
time                 14.65 μs   (14.55 μs .. 14.76 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 14.61 μs   (14.51 μs .. 14.73 μs)
std dev              348.4 ns   (259.3 ns .. 480.2 ns)
variance introduced by outliers: 24% (moderately inflated)

benchmarking a50/RegExp:Map
time                 11.07 μs   (10.98 μs .. 11.16 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 11.10 μs   (11.01 μs .. 11.21 μs)
std dev              329.8 ns   (252.6 ns .. 443.9 ns)
variance introduced by outliers: 34% (moderately inflated)

benchmarking a50/RegExp:IntMap
time                 10.83 μs   (10.67 μs .. 10.97 μs)
                     0.999 R²   (0.998 R² .. 0.999 R²)
mean                 10.71 μs   (10.62 μs .. 10.80 μs)
std dev              303.4 ns   (249.6 ns .. 357.6 ns)
variance introduced by outliers: 32% (moderately inflated)

benchmarking a50/LTrie:Map
time                 1.297 μs   (1.288 μs .. 1.308 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 1.301 μs   (1.292 μs .. 1.312 μs)
std dev              33.40 ns   (27.52 ns .. 41.50 ns)
variance introduced by outliers: 33% (moderately inflated)

benchmarking a50/LTrie:IntMap
time                 1.230 μs   (1.218 μs .. 1.240 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 1.226 μs   (1.219 μs .. 1.237 μs)
std dev              28.83 ns   (20.17 ns .. 40.29 ns)
variance introduced by outliers: 30% (moderately inflated)

```

# Group "letters"

```

benchmarking asdf-50/RegExp:Function
time                 4.091 ms   (4.051 ms .. 4.131 ms)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 4.013 ms   (3.985 ms .. 4.043 ms)
std dev              90.09 μs   (74.66 μs .. 117.6 μs)

benchmarking asdf-50/RegExp:Map
time                 3.297 ms   (3.263 ms .. 3.329 ms)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 3.326 ms   (3.304 ms .. 3.348 ms)
std dev              70.53 μs   (58.53 μs .. 92.42 μs)

benchmarking asdf-50/RegExp:IntMap
time                 2.840 ms   (2.813 ms .. 2.873 ms)
                     0.998 R²   (0.996 R² .. 0.999 R²)
mean                 2.936 ms   (2.894 ms .. 2.999 ms)
std dev              161.0 μs   (116.5 μs .. 217.3 μs)
variance introduced by outliers: 36% (moderately inflated)

benchmarking asdf-50/LTrie:Map
time                 7.288 μs   (7.247 μs .. 7.331 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 7.286 μs   (7.249 μs .. 7.331 μs)
std dev              131.6 ns   (104.4 ns .. 160.1 ns)
variance introduced by outliers: 17% (moderately inflated)

benchmarking asdf-50/LTrie:IntMap
time                 6.775 μs   (6.741 μs .. 6.809 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 6.787 μs   (6.753 μs .. 6.819 μs)
std dev              112.8 ns   (95.03 ns .. 137.5 ns)
variance introduced by outliers: 15% (moderately inflated)

```

# Group "dyck"

```

benchmarking "[]"/RegExp:Function
time                 1.661 μs   (1.642 μs .. 1.678 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 1.649 μs   (1.637 μs .. 1.662 μs)
std dev              40.52 ns   (31.23 ns .. 52.59 ns)
variance introduced by outliers: 31% (moderately inflated)

benchmarking "[]"/LTrie:Map
time                 51.63 ns   (51.37 ns .. 51.94 ns)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 52.07 ns   (51.55 ns .. 53.30 ns)
std dev              2.716 ns   (1.141 ns .. 5.270 ns)
variance introduced by outliers: 73% (severely inflated)

benchmarking "[]"/LTrie:IntMap
time                 51.72 ns   (51.33 ns .. 52.06 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 51.76 ns   (51.39 ns .. 52.72 ns)
std dev              1.908 ns   (757.1 ps .. 4.039 ns)
variance introduced by outliers: 58% (severely inflated)

benchmarking "[[]]"/RegExp:Function
time                 3.913 μs   (3.885 μs .. 3.950 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 3.934 μs   (3.910 μs .. 3.960 μs)
std dev              83.99 ns   (70.03 ns .. 100.5 ns)
variance introduced by outliers: 23% (moderately inflated)

benchmarking "[[]]"/LTrie:Map
time                 104.8 ns   (104.0 ns .. 105.6 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 104.7 ns   (104.2 ns .. 105.5 ns)
std dev              2.141 ns   (1.646 ns .. 2.729 ns)
variance introduced by outliers: 28% (moderately inflated)

benchmarking "[[]]"/LTrie:IntMap
time                 103.9 ns   (103.2 ns .. 104.6 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 103.9 ns   (103.4 ns .. 104.6 ns)
std dev              1.846 ns   (1.494 ns .. 2.460 ns)
variance introduced by outliers: 23% (moderately inflated)

benchmarking "[[a]]"/RegExp:Function
time                 2.951 μs   (2.941 μs .. 2.963 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 2.937 μs   (2.926 μs .. 2.949 μs)
std dev              38.86 ns   (31.23 ns .. 50.80 ns)
variance introduced by outliers: 11% (moderately inflated)

benchmarking "[[a]]"/LTrie:Map
time                 142.2 ns   (140.7 ns .. 143.9 ns)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 141.4 ns   (140.5 ns .. 142.5 ns)
std dev              3.432 ns   (2.651 ns .. 5.189 ns)
variance introduced by outliers: 35% (moderately inflated)

benchmarking "[[a]]"/LTrie:IntMap
time                 128.1 ns   (127.6 ns .. 128.7 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 128.8 ns   (128.0 ns .. 130.5 ns)
std dev              3.726 ns   (2.232 ns .. 6.185 ns)
variance introduced by outliers: 44% (moderately inflated)

benchmarking "[[]][]"/RegExp:Function
time                 5.295 μs   (5.267 μs .. 5.318 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 5.252 μs   (5.229 μs .. 5.275 μs)
std dev              78.17 ns   (69.57 ns .. 89.95 ns)
variance introduced by outliers: 12% (moderately inflated)

benchmarking "[[]][]"/LTrie:Map
time                 161.0 ns   (159.9 ns .. 162.0 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 160.5 ns   (159.8 ns .. 161.3 ns)
std dev              2.586 ns   (2.240 ns .. 3.098 ns)
variance introduced by outliers: 19% (moderately inflated)

benchmarking "[[]][]"/LTrie:IntMap
time                 157.7 ns   (156.0 ns .. 159.7 ns)
                     0.999 R²   (0.998 R² .. 0.999 R²)
mean                 159.8 ns   (158.1 ns .. 162.3 ns)
std dev              6.857 ns   (4.853 ns .. 9.427 ns)
variance introduced by outliers: 63% (severely inflated)

```

# Group "anbn"

```

benchmarking ""/RegExp:Function
time                 27.02 ns   (26.85 ns .. 27.20 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 27.21 ns   (27.04 ns .. 27.41 ns)
std dev              636.5 ps   (531.6 ps .. 781.0 ps)
variance introduced by outliers: 36% (moderately inflated)

benchmarking ""/LTrie:Map
time                 7.891 ns   (7.816 ns .. 7.950 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 7.806 ns   (7.772 ns .. 7.852 ns)
std dev              136.7 ps   (105.1 ps .. 195.5 ps)
variance introduced by outliers: 26% (moderately inflated)

benchmarking ""/LTrie:IntMap
time                 7.962 ns   (7.879 ns .. 8.048 ns)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 8.016 ns   (7.946 ns .. 8.104 ns)
std dev              259.6 ps   (207.8 ps .. 337.5 ps)
variance introduced by outliers: 55% (severely inflated)

benchmarking "ab"/RegExp:Function
time                 1.473 μs   (1.465 μs .. 1.483 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 1.483 μs   (1.473 μs .. 1.499 μs)
std dev              44.05 ns   (31.24 ns .. 65.88 ns)
variance introduced by outliers: 39% (moderately inflated)

benchmarking "ab"/LTrie:Map
time                 51.86 ns   (51.60 ns .. 52.24 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 51.71 ns   (51.48 ns .. 51.99 ns)
std dev              830.9 ps   (644.1 ps .. 1.072 ns)
variance introduced by outliers: 20% (moderately inflated)

benchmarking "ab"/LTrie:IntMap
time                 52.55 ns   (51.82 ns .. 53.33 ns)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 52.11 ns   (51.81 ns .. 52.48 ns)
std dev              1.208 ns   (920.3 ps .. 1.534 ns)
variance introduced by outliers: 35% (moderately inflated)

benchmarking "aacbb"/RegExp:Function
time                 2.682 μs   (2.653 μs .. 2.718 μs)
                     0.999 R²   (0.997 R² .. 1.000 R²)
mean                 2.658 μs   (2.638 μs .. 2.695 μs)
std dev              89.17 ns   (50.82 ns .. 151.7 ns)
variance introduced by outliers: 44% (moderately inflated)

benchmarking "aacbb"/LTrie:Map
time                 141.0 ns   (140.0 ns .. 142.2 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 142.0 ns   (141.2 ns .. 143.1 ns)
std dev              3.433 ns   (2.370 ns .. 5.616 ns)
variance introduced by outliers: 35% (moderately inflated)

benchmarking "aacbb"/LTrie:IntMap
time                 130.9 ns   (130.2 ns .. 132.0 ns)
                     0.998 R²   (0.996 R² .. 1.000 R²)
mean                 134.0 ns   (132.1 ns .. 139.1 ns)
std dev              9.891 ns   (4.344 ns .. 18.19 ns)
variance introduced by outliers: 84% (severely inflated)

benchmarking "aaabbb"/RegExp:Function
time                 4.607 μs   (4.564 μs .. 4.672 μs)
                     0.999 R²   (0.998 R² .. 0.999 R²)
mean                 4.749 μs   (4.693 μs .. 4.833 μs)
std dev              233.4 ns   (173.3 ns .. 356.6 ns)
variance introduced by outliers: 62% (severely inflated)

benchmarking "aaabbb"/LTrie:Map
time                 162.7 ns   (159.1 ns .. 167.3 ns)
                     0.997 R²   (0.995 R² .. 1.000 R²)
mean                 160.3 ns   (159.2 ns .. 162.6 ns)
std dev              5.071 ns   (3.128 ns .. 9.120 ns)
variance introduced by outliers: 48% (moderately inflated)

benchmarking "aaabbb"/LTrie:IntMap
time                 153.2 ns   (152.3 ns .. 154.4 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 154.0 ns   (153.4 ns .. 155.3 ns)
std dev              2.928 ns   (1.756 ns .. 4.910 ns)
variance introduced by outliers: 25% (moderately inflated)

benchmarking "aaabbbb"/RegExp:Function
time                 4.641 μs   (4.613 μs .. 4.669 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 4.629 μs   (4.600 μs .. 4.662 μs)
std dev              105.4 ns   (74.39 ns .. 141.8 ns)
variance introduced by outliers: 25% (moderately inflated)

benchmarking "aaabbbb"/LTrie:Map
time                 198.1 ns   (195.8 ns .. 201.3 ns)
                     0.997 R²   (0.993 R² .. 0.999 R²)
mean                 200.6 ns   (197.0 ns .. 206.6 ns)
std dev              15.21 ns   (9.733 ns .. 22.60 ns)
variance introduced by outliers: 84% (severely inflated)

benchmarking "aaabbbb"/LTrie:IntMap
time                 179.6 ns   (178.4 ns .. 180.6 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 178.7 ns   (177.8 ns .. 179.7 ns)
std dev              3.004 ns   (2.585 ns .. 3.640 ns)
variance introduced by outliers: 20% (moderately inflated)

benchmarking 30/RegExp:Function
time                 302.3 μs   (296.2 μs .. 309.6 μs)
                     0.997 R²   (0.996 R² .. 0.998 R²)
mean                 309.5 μs   (304.8 μs .. 314.3 μs)
std dev              17.20 μs   (13.48 μs .. 23.80 μs)
variance introduced by outliers: 52% (severely inflated)

benchmarking 30/LTrie:Map
time                 1.629 μs   (1.617 μs .. 1.642 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 1.631 μs   (1.619 μs .. 1.651 μs)
std dev              49.53 ns   (33.25 ns .. 93.67 ns)
variance introduced by outliers: 40% (moderately inflated)

benchmarking 30/LTrie:IntMap
time                 1.525 μs   (1.515 μs .. 1.535 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 1.532 μs   (1.519 μs .. 1.574 μs)
std dev              66.66 ns   (23.25 ns .. 153.9 ns)
variance introduced by outliers: 58% (severely inflated)

```
