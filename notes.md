---
title: Notes for a paper about generalized convolution
substMap: [("<+>","+"),("<.>","·")]
...

[*Derivatives of Regular Expressions*]: http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.98.4378 "paper by Janusz Brzozowski (1964"

\newcommand\set[1]{\{\,#1\,\}}
\newcommand\Pow{\mathcal{P}}
\newcommand\setop[1]{\mathbin{\hat{#1}}}
\newcommand\eps{\varepsilon}
\newcommand\closure[1]{#1^{\ast}}
\newcommand\mappend{\diamond}
\newcommand\cat{\cdot}
\newcommand\single\overline
\newcommand\union{+}
\newcommand\bigunion{\sum}
\newcommand\has[2]{\delta_{#1}\,#2}
\newcommand\del[1]{\has\eps{#1}}
\newcommand\consl[2]{\single{[#1]} \cat #2}
\newcommand\conslp[2]{\consl{#1}{(#2)}}
\newcommand\lquot{\setminus}

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

### Languages

*   Identify the vocabulary of a "language" (singleton plus semiring).
*   Define where a language is set of strings.
*   Note the semiring interface.

### Matching

*   The set-based language definition doesn't give an implementation, because the sets may be infinite.
*   Change to a predicate, and specify the new method definitions via homomorphism equations.
    Easy to solve, and gets an effective implementation (thanks to laziness).
*   Rephrase in terms of string predicates/recognizers, where $s \lquot p$ becomes $p \circ (s\,\mappend)$, which specializes to $p \circ (c:)$ when $s=[c]$.

### List of successes

### Efficient matching

*   First decomposition law: $p = \bigcup\limits_{s \in p} \single s$.
*   Second decomposition law: $p = \bigcup\limits_s \has s p$, where
    $\has s p =
    \begin{cases}
    \single s & \text{if $s \in p$} \\
    \emptyset & \text{otherwise}
    \end{cases}$.
    Specialize to empty strings: $\del p = \has \eps p$.
*   So far we can accommodate any monoid.
    Now focus on sequences.
*   "Derivative": $c \lquot p = \set {s \mid c:s \in p}$.
*   Third decomposition law [Brzozowski, 1964, Theorem 4.4]:
    $p = \del p \union \bigcup\limits_{c\,\in\,A} \single c \cat (c \lquot p)$.
    Holds for all languages, not just regular.
*   Maybe same for a free representation (regular expressions), though trivial.
*   Review (string) tries.
    Note the appearance of $p \eps$ and $p \circ (c:)$.
    Define the homomorphism equations, which are easy to solve, via trie isomorphism.
    Simplifying yields a simple and efficient implementation.

### Generalizing

*   Semirings.
*   Convolution.
*   Beyond convolution: the free semimodule monad.
*   Variations: counting, probability distributions, temporal/spatial convolution.

### Other applications

*   Univariate and multivariate polynomials.
*   Convolution: discrete and continuous, one- and multi-dimensional, dense and sparse.
*   2D parsing?

## Miscellaneous notes

*   Summarize/review languages as sets, including singleton, union, concatenation, and star/closure.
    Survey some representations for parsing, including a naive one as predicates (requiring nondeterministic splitting).
    For regular languages specified in this vocabulary, the classic technique for efficient parsing is to generate a finite state machine.
    Another technique is Brzozowski's "derivatives of regular expressions", extended much more recently to context-free languages.
    Maybe revisit Brzozowski's technique; alternatively just mention, and compare in related work.
    Calculate a generalized variant from a simple specification.
    Key is a known but not widely used monadic structure, namely that of *free semimodules*.

*   Once I have a restricted `Applicative` instance, I can make language itself be a monoid in a perfectly standard way, with `mempty = pure mempty` and `mappend = liftA2 mappend`.
    Likewise, temporal and (multidimensional) spatial convolution is simply `liftA2 (+)`, which is a standard definition for `(+)` on applicatives.
    We can give full instances for numeric classes in this style.
*   For multivariate polynomials, I was thinking of using maps from exponent tuples.
    Alternatively, replace tuples by statically sized vectors.
    More generally, use a representable functor or even zippable.
    I guess anything "summable", i.e., a monoid.
    Perhaps whatever simplifies parsing and unparsing.
*   What symbol to use for `mappend`?
    Some candidates: \\cdot, \\diamond, \\ast, \\circledast, \\APLstar, several dingbats choices (\\ding), \\Snowflake.
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
*   Discuss the function-of-monoid perspective explored in my journal notes for 2018-12-29 and 2018-12-30.
    I like its duality with the *Comonad* instance for the same type.

## Super-memoization

I suspect that my take on Brzozowski's technique is just one example of a much more general technique akin to memoization but in which we get partial sharing of work across calls to a function with *different* arguments (unlike regular memoization).
