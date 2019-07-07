% Reviews for "Generalized Convolution and Efficient Language Recognition"

ICFP 2019 Paper #46 Reviews and Comments
===========================================================================
Paper #46 Generalized Convolution and Efficient Language Recognition


Review #46A
===========================================================================

Overall merit
-------------
C. Weak paper, though I will not fight strongly against it.

Reviewer expertise
------------------
Y. I am knowledgeable in the area, though not an expert.

Paper summary
-------------
This paper remarks that convolution is a general operation that endows
semiring structure on the set of functions from any monoid to any
semiring.  Usually the word "convolution" evokes a domain monoid of
integers (giving rise to polynomial convolution) or of integer tuples
(giving rise to image convolution).  But when the domain monoid is
the monoid of lists (i.e., strings), the paper generalizes Brzozowski
derivatives from sets (i.e., when the range semiring is the semiring of
Booleans) to any other range semiring, and derives two implementations:
one that stores regular expressions and one that stores tries.

Comments for author
-------------------
The generalizations represented in Figures 1-4 are worthwhile and to my
knowledge novel.  But these contributions are buried among definitions
and derivations whose applications within and beyond the paper remain
unclear.

- For example, it's not clear how Sections 10-13 are novel or help
  to produce Figure 9 efficiently or at all.  The paper would be far
  more interesting if it were shown that a generic implementation of
  convolution can achieve performance competitive against existing
  specialized implementations for string matching and image blurring.

- To take another example, line 664 introduces "an alternative to
  repeated syntactic differentiation" but it's unclear what shared goal
  is achieved by both "repeated syntactic differentiation" and this
  "alternative", there is no demonstration of "the syntactic overhead",
  and it is unclear what "f" means in "a choice of f".
  *[Conal: "f" should be "h".]*

This paper lacks

- upfront signposting of dependencies and contributions

  Examples of roadmap descriptions that need to be preponed in the
  paper include the first sentence of Section 7, the first paragraph
  of Section 8, and the first paragraph of Section 10.  It is unclear
  where lines 611-640 and lines 991-993 are used.  The implementations
  in Figures 3 and 4 should be demonstrated in the style of lines
  1163-1172.

- evidence of computational practicality

  Phrases such as "quite efficient" (line 85) and "dramatic speed
  improvement" (line 92) are vague because the standards of comparison
  are unclear.  And performance comparisons are not interesting if they
  are only made against other implementations in the same work.  Hence,
  Figure 6 should compare against at least one existing implementation
  (such as Happy).  Measurements should show standard errors.  Both
  matching and non-matching strings should be tested.

- comparison with related work

  The first paragraph of Section 14 is not enough because there is no
  comparison.

The code shown in the paper does not seem trustworthy: infinite sums
are confused with finite sums (for example on line 1106), and the `Key`
of an `Indexable` type constructor is sometimes expressed using a
functional dependency (line 300) and sometimes expressed using a type
family (lines 614, 789).

Minor comments:

*   Line 75 "the second and seventh decades of the twentieth century": just
    name the decades or years (1910s? etc.) to avoid off-by-one confusion.
*   Lines 87-90: This (4th) bullet point is unclear.  What "key operations"?
    What "comonad operations"? What "various representations"?  Each bullet
    point should name the specific section of the paper that makes that
    contribution.
    *[Conal: Added detail: "Observation that Brzozowski's two key operations on languages (emptiness and differentiation) generalize to the comonad operations (*coreturn* and *cojoin*) of the standard function-from-monoid comonad and various representations of those functions (including generalized regular expressions)."]*
*   Line 171 "this instance" referent unclear (too far from line 160).
    *[Conal: "... the `Additive (a -> b)` instance above"]*
*   Line 222: Clarify whether these two equations are equivalent.
*   Line 243 "a additive" -> "an additive" *[Conal: fixed]*
*   Line 265: Isn't this instance missing some context such as `Semiring s =>`?
    *[Conal: fixed.]*
    And why not generalize `(a -> s)` to `(a -> s')`?
    *[Conal: Because the type of multiplication requires that its arguments have the same type.]*
*   Line 329: $\sum$ is undefined, and what if $f$ maps an infinite number
    of $a$s to nonzero $b$s?
*   Lemma 6 seems to hold only for the instance on line 315.
    *[Conal: Yes, because of the use of curry. Clarified by adding "For functions,".]*
*   Lemma 7 seems unused in the rest of the paper.
    *[Conal: Yes. It's part of the theory developed here, though unused in this paper.]*
*   Line 339 `(->) a` needs to refer more explicitly to the instance on line 265.
    *[Conal: Added "(given the LeftSemimodule s (a → s) instance in Section 2.5)".*]
*   Line 340 "homomorphisms" needs an `instance LeftSemimodule s s`.
*   Line 340 `single` seems like it should be `value`.
    *[Conal: Indeed. Fixed.]*
*   Line 340 "semiring homomorphism" between which instances?
*   Lines 436 and 440 typeset `P` inconsistently (as $P$ and $\mathcal{P}$)
    *[Conal: Fixed.]*
*   Lines 460-461 "apply the same sort of reasoning as in Section 3 and then
    generalize from Bool to an arbitrary semiring" needs more details.
*   Line 489 "represented is" -> "represented as"
    *[Conal: Fixed.]*
*   Line 501 `M.null` -> `all isZero . M.elems`.
*   Line 583 is only proven for finite p, so it is not proven.
*   Line 742: Please parenthesize `c -> LTrie c b`
    *[Conal: Fixed.]*
*   Line 766 "sanity check" -> "smoke test"
*   Line 781 "one more crucial tricks" -> "one more crucial trick"
    *[Conal: fixed to "one or more crucial trick".]*
*   Line 782 "might" and line 783 "might" are not informative.
*   Figure 6:  All time measurements should be given in the same unit (μs
    for example) (lines 771-772), and all decimal points in each column
    should be aligned.  Whether the two occurrences of $\infty$ represent
    nontermination in theory or running out of time in practice should be
    ascertained (lines 780-781).
*   Line 901 "no fmap" is unclear.
    *[Conal: removed "and no fmap". I don't remember what I was trying to say there.]*
*   Line ~~1047~~ 1062 "a the" -> "the"
    *[Conal: fixed.]*
*   Switching `Semiring` instances in Figure 8 is confusing.  Instead, just
    define `<-` early and use it in Figure 1. 
*   Theorem 16 is meaningless because the Fourier transform is not defined
    for generic types `a` and `b`.
*   Line 1118: How does this `Show` instance enumerate the support of z?
    *[Conal: Via a type-check I elided from the paper.]*



Review #46B
===========================================================================

Overall merit
-------------
C. Weak paper, though I will not fight strongly against it.

Reviewer expertise
------------------
Y. I am knowledgeable in the area, though not an expert.

Paper summary
-------------
This paper provides a formalization of semirings, convolutions, and
Brzozowski's derivatives (hereinafter simply called "derivatives")
using functional programming idioms (i.e., type classes, monads,
etc.).

Comments for author
-------------------
Generally I like this kind of papers. Re-formulation from functional
programming may bring new perspectives and moreover general, concise,
and correct-by-construction implementations. However, for this
particular paper, I unfortunately did not get favorable impression. 

First, the contributions around derivatives seem (at least, partially)
known.  Derivatives for "weighted" regular expressions are studied in
the following papers.

* Sylvain Lombardy, Jacques Sakarovitch:
  Derivatives of rational expressions with multiplicity.
  Theor. Comput. Sci. 332(1-3): 141-177 (2005)
* Jean-Marc Champarnaud, Gerard Duchamp:
  Derivatives of rational expressions and related theorems.
  Theor. Comput. Sci. 313(1): 31-44 (2004)

Moreover, a connection between convolutions and derivatives can be found
in the following paper.

* Jan J. M. M. Rutten:
  Behavioural differential equations: a coinductive calculus of
  streams, automata, and power series.
  Theor. Comput. Sci. 308(1-3): 1-53 (2003)

These preceding studies are not reasons for rejecting the current
paper if a new insight from a perspective from functional programming
is presented.  However, such an insight is unclear. For example:
"comonadic understanding of derivatives" sounds interesting, but so
what?  Are comonad laws useful for reasoning about derivatives for
generalized regular expressions, for example?

A potential benefit is that the formalism itself is a run-able
implementation. However, for regular expression matching, even
specialized efficient implementations are favorable, and the current
evaluation is not convincing that the developed implementation is
efficient. The implementation can do more than regular expression
matching, but usefulness of the generality is not presented.

Another weakness of the current paper is its presentation. In my
impression, the focus and the technical developments are somewhat
unclear. I pick up a few relatively serious issues:
- Section 3 says "This process of calculating instances from
  homomorphisms is the central guiding principle of this paper", but I
  could not find such a "guiding principle". Most discussions are the
  converse direction, namely giving an instance and then showing it is
  a homomorphism.
- Although convolutions are the central topic of this paper, their
  introduction in Section 4 (the first paragraph of p.10) is
  unreasonable.  Why is the usual definition disappointing? Why are
  "the same sort of reasoning" omitted?
- Although convolutions are the central topic of this paper,
  connection between convolution and derivatives is unclear.
  Convolution is introduced as an operation on some kinds of functions
  in Section 4, and after that, never mentioned until Section 10.
- (Though I have known derivatives) I suspect that for those who do
  not know derivatives Section 6 seems not understandable. The
  author(s) should explain why such decomposition is considered here
  and what at_e and D are.

From above-mentioned issues, I judged the current paper is premature
for publication, even though it studies potentially interesting
research topic.



Review #46C
===========================================================================

Overall merit
-------------
C. Weak paper, though I will not fight strongly against it.

Reviewer expertise
------------------
Y. I am knowledgeable in the area, though not an expert.

Paper summary
-------------
This work presents a quite interesting and powerful generalization of regular expressions and the associated method of Brzozowski derivatives. The authors present regular expression concatenation (or more generally, formal language concatenation)  as a special case of convolution and propose a couple of general algebraic structures that can represent a wide range of use cases beyond regular expression matching.

Comments for author
-------------------
When I read the abstract and the introduction of the paper, I was rather thrilled and was eager to accept and support the paper. The authors have obviously invested a lot of time and thought into this work. I find the proposed generalization quite interesting and would love to see it published.

However, my main problem with the paper is that it is presented in a way that makes it really hard to understand what is going on. There is so much barely explained code in the paper, and very little guidance of the reader, that I got lost completely somewhere around p.13 and I stopped reading.

Below I'll give some more detailed hints of where I think the presentation is lacking. If the paper gets rejected, I strongly encourage the papers to continue this line of work and resubmit a revised version soon. If the paper gets accepted, I also suggest to revise the paper for readability.

Detailed comments:

In general, I thought that the paper lacks a proper structure that is easy to understand. In the first sections, it was never clear to me whether the authors summarize preliminaries or whether there are novel ideas in here. I was always waiting impatiently for the "meat" of the paper to begin. I think you should at least give the reader some kind of roadmap about how you present the material, especially since it takes a very long time before you return to the issues mentioned in the introduction.

l.479ff: Here I was rather puzzled that you suddenly talk about "testing for membership" but without demonstrating how one does test for membership. I would have appreciated if you had shown the full code here and illustrated which type class instances are derived and needed for that example to go through.

In section 6, I began to feel completely lost. All that code in Lemma 9 with no guidance about what it does.

With regard to the definition of D in l. 534 I wondered whether you are cheating in the sense that the Brzozowski algorithm gives me a concrete regular expression that represents the set of suffixes that can still follow, but in l. 534 it looks like you are merely creating a closure and nothing happens until the closure is applied to a concrete suffix.

l.570: I was rather confused that you merely drop the words "coreturn", "cojoin" etc. here without explaining what they mean and how exactly that correspondence works out.
