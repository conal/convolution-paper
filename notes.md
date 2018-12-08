---
title: Notes for a paper about generalized convolution
substMap: [("<+>","+"),("<.>","·")]
...

[*Derivatives of Regular Expressions*]: http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.98.4378 "paper by Janusz Brzozowski (1964"

## Paper outline

### Contributions

Generalize and unify:

*   Parsing by "derivatives" for regular languages and beyond, generalized beyond *sets* of strings.
    Some other possibilities: multisets, fuzzy sets, parsing probability distributions.
    Can we get semantic analysis cheaply?
*   Includes probabilistic computing.
*   Maybe generalize parsing beyond strings to trees and other shapes.
    Perhaps 2D parsing?
*   Polynomial arithmetic (addition, multiplication, and I hope composition), generalized to multivariate case.
*   Convolution: higher dimensions, continuous and discrete, and other shaped spaces.
*   Super-memoization.

### Languages and parsing

Summarize/review languages as sets, including singleton, union, concatenation, and star/closure.
For regular languages specified in this vocabulary, the classic technique for efficient parsing is to generate a finite state machine.
Another technique is Brzozowski's "derivatives of regular expressions", extended much more recently to context-free languages.
Revisit Brzozowski's technique.
Calculate a generalized variant from a simple specification.
Key is a known but not widely used monadic structure, namely that of *free semimodules*.

### Other applications

*   Univariate and multivariate polynomials.
*   Convolution: discrete and continuous, one- and multi-dimensional, dense and sparse.
*   2D parsing?

## Miscellaneous notes

*   The `Comonad` interface captures Brzozowski's two main operations: contains-empty and derivative
    ([notes](11-25#Parsing-with-derivatives-(A))).
*   There's also a `Monad` for functions that's unlike the usual one and seems to support convolution
    ([notes](11-25#Parsing-with-derivatives-(A))).
    Is this monad known?
    Maybe it corresponds to the vector space monad in one of Dan Piponi blog posts.
    Yes; it's the "free vector space monad", and more generally the "free semimodule monad".
*   I think the monad structure is more essential than the comonad structure.
    ([notes](12-02#Parsing-with-derivatives-(A))).
*   Generalize and use theorem 4.4 from [*Derivatives of Regular Expressions*]
    ([notes](11-25#Parsing-with-derivatives-(B/))).
*   Is Day convolution helpful?
*   Can I define languages monadically and get efficient convolutional parsing?
    Must values then be in a semiring?
*   Multivariate polynomials and power series.
    Rational? Streams?
*   Come up with another data type besides lists having a useful binary operation.
    Needn't be monoidal.
    Trees?


## Super-memoization

I suspect that my take on Brzozowski's technique is just one example of a much more general technique akin to memoization but in which we get partial sharing of work across calls to a function with *different* arguments (unlike regular memoization).

