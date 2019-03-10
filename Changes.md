---
title: Description of changes
...


## Submitted to ICFP (March 1, 2019)

*   Submitted version: [Git commit](https://github.com/conal/convolution-paper/commit/65c5fd3a08172b19e35eddda9f07c56fd2fc2f48) and [PDF](https://github.com/conal/convolution-paper/blob/master/icfp19-paper46-submitted.pdf).

## Updates

### March 9, 2019

*   Errata noted and fixed:
    *   In Figure 4, replace `Indexable` instances first two lines with the following line

            instance Indexable c (Cofree h b) (h (Cofree h b)) => Indexable [c] b (Cofree h b) where

    *   The definition of `lift2` in Section 11 shouldn't have "`\ w ->".
*   Section 11 (Beyond Convolution):
    *   In Figure 8 ("Functor and Applicative classes and some instances"): Added *Functor* and *Applicative* instances for *(→) a*, aside the instances for *(←) b*.
    *   In Figure 9 ("The a → b and b ← a semirings"): Added 𝒫' type and *Semiring* instance.
    *   Added function preimages example.

