## Generalized Convolution and Efficient Language Recognition

This repo contains an unpublished [paper](http://conal.net/papers/convolution/) along with the source code appearing in the paper.


### Abstract

*Convolution* is a broadly useful operation with applications including signal processing, machine learning, probability, optics, polynomial multiplication, and efficient parsing. Usually, however, this operation is understood and implemented in more specialized forms, hiding commonalities and limiting usefulness. This paper formulates convolution in the common algebraic framework of semirings and semimodules and populates that framework with various representation types. One of those types is the grand abstract template and itself generalizes to the free semimodule monad. Other representations serve varied uses and performance trade-offs, with implementations calculated from simple and regular specifications.

Of particular interest is Brzozowski's method for regular expression matching. Uncovering the method's essence frees it from syntactic manipulations, while generalizing from boolean to weighted membership (such as multisets and probability distributions) and from sets to *n*-ary relations. The classic *trie* data structure then provides an elegant and efficient alternative to syntax. Pleasantly, polynomial arithmetic requires no additional implementation effort, works correctly with a variety of representations, and handles multivariate polynomials and power series with ease. Image convolution also falls out as a special case.

Pleasantly, polynomial arithmetic requires no additional implementation effort, works correctly with a variety of representations, and handles multivariate polynomials and power series with ease.
Image convolution also falls out as a special case.


### Haskell source code

You can find the source code for the paper's functionality and examples in the `src` directory.

To try out the Haskell implementation, make sure you have [`stack`](https://docs.haskellstack.org/en/stable/README/) installed, and then

*   Compile: `stack build`
*   Gold tests: `stack test`.
    These gold tests check that all of the representations yield the same answer.
*   Benchmarks: `stack bench`.
    This one takes a while and generates stats.html as well as a lot of textual statistics.
    You can make it go faster (at the cost of less accurate measurements) by lowing `timeLimit` in test/Benchmark.hs.
    The examples (`anbn` and `dyck`) that don't terminate with `RegExp (Map Char)` appear to have running times of about 3 ns but really are skipped.
*   To run the image convolution examples:

        (cd test; stack build :image-test && stack exec image-test)


Some of the modules contain comments like the following (in src/Poly.hs):

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


