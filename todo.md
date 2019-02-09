---
title: To-do items for the paper and code
substMap: [("<+>","+"),("<.>","∗"),(".>","·"),("+->","↦"),("<--","←")]
...

## To-do items for the paper and code

*   Factor `Additive` out of `Semiring`, and drop the `Monoid` requirement for `Additive (b :<-- a)` and `Applicative ((:<--) a)`.
    I'll have to return to defining my own classes. Tip my hat to semiring-num.
*   Maybe drop `HasSingle` and define `single` via `fmap` and `one`.
*   Derive a semiring for lists based on a homomorphism from `[a]` to `a <-- Nat`.
*   From recognition to "parsing", i.e., generating rich representations.
*   Learn about tree grammars, and see how they fit with parsing with derivatives.
*   Try using `TMap` from [total-map](https://github.com/conal/total-map) in place of `Map` from containers, including the `Applicative` and `Monad` instances.
    I may have to add some operations.
*   Consider the following intuition.
    The result of `fmap h (F f)` is moving all of the values in `f` to new locations according to `h`, summing all values that get moved to the same place.
    Similarly for `liftA2`.
    Graphics has a similar issue!
    Spatial transformations may be one-to-many, especially if non-projective.
*   [Free semirings](http://hackage.haskell.org/package/semiring-num-1.6.0.1/docs/Data-Semiring-Free.html)
*   Convolution commutes with currying and with uncurrying.
    So do addition, zero, and one, but `single` is different.
    See 2019-01-28 notes.
*   Sets are to languages as binary relations are to what?
    Currying gets us to `String -> String -> Bool` (for sets).
    Is there anything interesting and/or useful here?
    Note that a (generalized) trie from pairs of strings is going to look like a curried trie anyway.
*   Generalize lists to end with a value, where the usual lists end with unit.
    Then monadic bind generalizes appending, i.e., `(++) = (>>)`.
    Now generalize from the unary/sequential nature of lists, and we get monadic bind as "substitution".
    I think the generalization here is to the free monad induced by some functor.
    For `[a]`, that functor is `(a :*)`.
*   Polynomials and perhaps integer multiplication.
*   Implement convolution (really `liftA2 add`) on statically sized arrays.
    I think I'll want an interface for enumerating all values of a type.
    The finite-typelits library has useful operations:
    ``` haskell
    finites :: KnownNat n => [Finite n]
    add :: Finite n -> Finite m -> Finite (n + m)
    ```

    Try 1D and 2D examples.
*   Use semiring-num instead of my own classes for `Semiring`, `ClosedSemiring`, and `DetectableZero`. 
    Consider uses for the other instances defined there.
*   Define `sum` and `product` at their first use.
    Consider renaming as in semiring-num.
*   Tropical semirings?
*   Generalize to other tries.
*   Counting and closure and infinity.
*   Probability distribution semiring:
    *   Uses?
    *   Closure
*   Understand and apply [this MathOverflow answer](https://math.stackexchange.com/a/1651127) on convolution and Day convolution.
*   Track down references for convolution over functions with arbitrary *monoidal* domains.
    Also "convolutional algebras".
    See, e.g., "[group algebra](https://www.encyclopediaofmath.org/index.php/Group_algebra)" and "[convolution algebra](https://ncatlab.org/nlab/show/convolution+algebra)".
*   Some references:
    *   Brzozowski derivatives:
        *   [Wikipedia page on the *Brzozowski derivative*](https://en.wikipedia.org/wiki/Brzozowski_derivative)
        *   [*Derivatives of Regular Expressions*]
        *   [*Rewriting Extended Regular Expressions*]
        *   [*Some Properties of Brzozowski Derivatives of Regular Expressions*]
        *   [*Derivatives of Regular Expressions and an Application*]
        *   [*Regular-expression derivatives reexamined*]
        *   [*Derivatives for Enhanced Regular Expressions*]
        *   [*Regular expression sub-matching using partial derivatives*]
        *   [*Testing Extended Regular Language Membership Incrementally by Rewriting*]
        *   [*Yacc is dead*]
        *   [*Yacc is dead: An update*]
    *   Semirings:
        *   [*Some Recent Applications of Semiring Theory*]
        *   [*Fun with Semirings: A functional pearl on the abuse of linear algebra*]
        *   [*Linear Algebra Over Semirings*]
    *   On semirings and parsing:
        *   [*Parsing Inside-Out*]
        *   [*Semiring Parsing*]
        *   [*Algebraic Foundation of Statistical Parsing: Semiring Parsing*]
        *   [*Goodman: Semiring Parsing*]
    *   Comonad references:
        *   [Monads from Comonads](http://comonad.com/reader/2011/monads-from-comonads/) (blog post by Ed Kmett, 2011)
        *   [*Monads from Comonads, Comonads from Monads*]
        *   [*Should I use a Monad or a Comonad?*]
    *   Other:
        *   [*Convolution as a Unifying Concept: Applications in Separation Logic, Interval Calculi, and Concurrency*]
        *   [*Introduction to weighted automata theory*]
        *   [*Weighted Automata*]
        *   [*Quantifiers on languages and codensity monads*]
        *   [What is a coalgebra intuitively?](https://mathoverflow.net/questions/76509/what-is-a-coalgebra-intuitively)
        *   [*Bases as coalgebras*](https://arxiv.org/pdf/1309.0844.pdf)
        *   [*The Dual of Substitution is Redecoration*]
        *   [*Higher Dimensional Trees, Algebraically*]
*   Super-memoization.
    See notes from 2018-12-02 and 2018-12-05

## Did

*   Remove a bunch of unused code, first moving to `Other`.
*   Summation (etc) notation style:
    *   Consider moving the condition to the body where it becomes multiplication:

        ``` haskell
          liftA2 h (Pred f) (Pred g) = Pred (\ w -> or (u,v) (f u && g v && h u v == w))
        ``` 

        Note that `w` appears only in the third conjunct.
    *   Generalizing from predicates to flipped functions, 

        ``` haskell
          liftA2 h (F f) (F g) = F (\ w -> sum (u,v) (f u * g v * single (h u v) w))
        ```

    *   Simplify further

        ``` haskell
          liftA2 h (F f) (F g)
        = F (\ w -> sum (u,v) (f u * g v * single (h u v) w))
        = sum (u,v) (\ w -> f u * g v * single (h u v) w)
        = sum (u,v) ((f u * g v) .> (\ w -> single (h u v) w))
        = sum (u,v) ((f u * g v) .> single (h u v))
        ```

    *   Then simplify the "standard FunApp" proof.
    *   Introduce notation "`a +-> b = b .> single a`".
        Then `liftA2 h (F f) (F g) = sum (u,v) (f u * g v +-> h u v)`. 


[*Differentiation of higher-order types*]: http://conal.net/blog/posts/differentiation-of-higher-order-types/ "blog post"

[*Another angle on zippers*]: http://conal.net/blog/posts/another-angle-on-zippers/ "blog post"

[*Derivatives of Regular Expressions*]: http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.98.4378 "paper by Janusz Brzozowski (1964"

[*Rewriting Extended Regular Expressions*]: http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.54.7335 "paper by by Valentin Antimirov and Peter Mosses (1994)"

[*Some Properties of Brzozowski Derivatives of Regular Expressions*]: https://arxiv.org/abs/1407.5902 "paper by N.Murugesan and O.V.Shanmuga Sundaram (2014)"

[*Derivatives of Regular Expressions and an Application*]: https://www.researchgate.net/publication/221350925_Derivatives_of_Regular_Expressions_and_an_Application "paper by Haiming ChenHaiming ChenSheng and YuSheng Yu (2012)"

[*Regular-expression derivatives reexamined*]: http://www.ccs.neu.edu/home/turon/re-deriv.pdf "paper by Scott Owens, John Reppy, and Aaron Turon (2009)"

[*Derivatives for Enhanced Regular Expressions*]: https://arxiv.org/abs/1605.00817 "paper by Peter Thiemann (2016)"

[*Regular expression sub-matching using partial derivatives*]: http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.605.6379 "by Martin Sulzmann, Kenny Zhuo, and Ming Lu (2012)"

[*Testing Extended Regular Language Membership Incrementally by Rewriting*]: https://www.semanticscholar.org/paper/Testing-Extended-Regular-Language-Membership-by-Rosu-Viswanathan/90fdd53e5b29705967c3cc21c050463ded1b514d "paper by Grigore Rosu and Mahesh Viswanathan (2003)"

[*Yacc is dead*]: https://arxiv.org/abs/1010.5023 "paper by Matthew Might and David Darais (2010)"

[*Yacc is dead: An update*]: http://matt.might.net/articles/parsing-with-derivatives/ "blog post by Matt Might ()"

[*DFINITY Technology Overview Series, Consensus System*]: https://arxiv.org/abs/1805.04548 "paper by Timo Hanke, Mahnush Movahedi, and Dominic Williams (2018)"

[*Compiling to categories*]: http://conal.net/papers/compiling-to-categories "paper by Conal Elliott (2017)"

[*The simple essence of automatic differentiation*]: http://conal.net/papers/essence-of-ad "paper by Conal Elliott (2018)"

[*Generic functional parallel algorithms: Scan and FFT*]: http://conal.net/papers/generic-parallel-functional "paper by Conal Elliott (2017)"

[*Parsing Inside-Out*]: https://arxiv.org/abs/cmp-lg/9805007 "doctoral thesis by Joshua Goodman (1998)"

[*Semiring Parsing*]: http://www.aclweb.org/anthology/J99-4004 "Paper by Joshua Goodman (1999)"

[*Algebraic Foundation of Statistical Parsing: Semiring Parsing*]: https://pdfs.semanticscholar.org/7938/c9b56de70eb641d946353b9c0fa255f48b4f.pdf "PhD Depth Examination Report by Yudong Liu (2004)"

[*Goodman: Semiring Parsing*]: https://kevinbinz.com/2014/11/16/goodman-semiring-parsing/ "blog post by Kevin Binz (2014)"

[*Monads from Comonads, Comonads from Monads*]: http://www.cs.ox.ac.uk/ralf.hinze/WG2.8/28/slides/Comonad.pdf "paper by Ralf Hinze (2011?)"

[*Should I use a Monad or a Comonad?*]: https://www.semanticscholar.org/paper/Should-I-use-a-Monad-or-a-Comonad-%3F-Orchard/bec621991dd3e8b1e118fdd0a1d7b5819471a964 "paper by Dominic A. Orchard (2012)"

[`Data.Functor.Day`]: https://hackage.haskell.org/package/kan-extensions/docs/Data-Functor-Day.html "Haskell source module by Edward Kmett (2014--2016)"

[*Comonads and Day Convolution*]: https://blog.functorial.com/posts/2016-08-08-Comonad-And-Day-Convolution.html "blog post by Phil Freeman (2016)"

[*Quantifiers on languages and codensity monads*]: https://arxiv.org/abs/1702.08841 "paper by Mai Gehrke, Daniela Petrisan, and Luca Reggio
(2018)"

[*Towards a Coalgebraic Chomsky Hierarchy*]: https://arxiv.org/abs/1401.5277v3 "paper by Sergey Goncharov, Stefan Milius, Alexandra Silva (2014)"

[*The monads of classical algebra are seldom weakly cartesian*]: https://link.springer.com/article/10.1007/s40062-013-0063-2 "paper by Maria Manuel Clementino, Dirk Hofmann, and George Janelidze (2013)"

[*Fun with Semirings: A functional pearl on the abuse of linear algebra*]: http://stedolan.net/research/semirings.pdf "paper by Stephen Dolan (2013)"

[*The Dual of Substitution is Redecoration*]: http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.16.9369 "paper by Tarmo Uustalu and Varmo Vene (2002)"

[*Higher Dimensional Trees, Algebraically*]: https://www.semanticscholar.org/paper/Higher-Dimensional-Trees%2C-Algebraically-Ghani-Kurz/3b650d5ee01ac35c721c5bd51e4859aebe3880e2 "paper by Neil Ghani, Alexander Kurz (2007)"

[*Convolution as a Unifying Concept: Applications in Separation Logic, Interval Calculi, and Concurrency*]: https://dl.acm.org/citation.cfm?id=2874773 "paper by Brijesh Dongol, Ian J. Hayes, and Georg Struth (2016)"

[*Introduction to weighted automata theory*]: https://perso.telecom-paristech.fr/jsaka/CONF/Files/IWAT.pdf "Presentation by Jacques Sakarovitch (year?)"

[*Weighted Automata*]: https://www.semanticscholar.org/paper/Weighted-automata-Droste-Kuske/f8d5980f23814e1d69a737f1f178d4a2565f7c22 "paper by Manfred Droste and Dietrich Kuske (2012)"

[*Some Recent Applications of Semiring Theory*]: http://moonstone.math.ncku.edu.tw/Conferences/BeidarConference/golantalk.pdf "Paper by Jonathan S. Golan (2005)"

[*Linear Algebra Over Semirings*]: https://www.research.manchester.ac.uk/portal/files/54562608/FULL_TEXT.PDF "PhD thesis by David Wilding (2014)"
