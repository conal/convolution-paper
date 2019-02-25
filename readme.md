## Efficient parsing and generalized convolution

A paper for submission to ICFP 2019

### Abstract

*Goes here.*

### Haskell source code

You can find the source code for the paper's functionality and examples in the `src` directory.

Instructions for trying out the implementation:

*   Compile: `stack build`
*   Tests: `stack test`
*   Benchmarks: `stack bench`

Some of the modules contain comments like the following:

``` haskell
-- >>> let p = single 1 <+> value 3 :: Poly1 Z
-- >>> p
-- x + 3
-- 
-- >>> p^3
-- x^3 + 9 * x^2 + 27 * x + 27
-- 
-- >>> p^5
-- x^5 + 15 * x^4 + 90 * x^3 + 270 * x^2 + 405 * x + 243
```

If you use Emacs and have [dante](https://github.com/jyp/dante) installed, you can run these examples in place via `dante-eval-block` (`C-c "`).


