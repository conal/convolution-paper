% -*- latex -*-

%% While editing/previewing, use 12pt and tiny margin.
\documentclass[hidelinks,twoside]{article}  % fleqn, 

\usepackage[margin=0.12in]{geometry}  % 0.12in, 0.9in, 1in
% \geometry{paperwidth=6.75in}  % Handy for previewing in portrait

%% \documentclass{article}
%% \usepackage{fullpage}

\usepackage[us,12hr]{datetime}
\usepackage{setspace}

%% Temporary title
\def\tit{Efficient language recognition and generalized convolution}

\author{Conal Elliott}

\usepackage{fancyhdr}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[LO]\tit
\fancyhead[RE]{%
Conal Elliott
}
\fancyhead[LE,RO]{\thepage}
% \rnc{\headrulewidth}{0pt}

%include polycode.fmt
%include forall.fmt
%include greek.fmt
%include formatting.fmt

\input{macros}

\calculationcomments

\usepackage[square]{natbib}
\bibliographystyle{plainnat}

%% % author-date form
%% \usepackage[]{natbib}
%% \bibpunct();A{},
\let\cite=\citep

\title\tit
\date{Early draft of \today{} \currenttime}

\setlength{\blanklineskip}{2ex} % blank lines in code environment

\nc\proofLabel[1]{\label{proof:#1}}
%if short
\nc\proofRef[1]{proof in \citep[Appendix C]{Elliott-2019-convolution-extended}}
%else
\nc\proofRef[1]{Appendix \ref{proof:#1}}
%endif
\nc\provedIn[1]{\textnormal{Proved in \proofRef{#1}}}

\nc\set[1]{\{\,#1\,\}}
\nc\Pow{\mathcal{P}}
\nc\mempty{\varepsilon}
\nc\closure[1]{#1^{\ast}}
\nc\mappend{\diamond}
\nc\cat{\mathop{}}
\nc\single\overline
\nc\union{\cup}
\nc\bigunion{\bigcup\limits}
\nc\has[1]{\mathop{\delta_{#1}}}
\nc\derivOp{\mathcal{D}}
%% \nc\derivsOp{\derivOp^{\ast}}
%% \nc\deriv[1]{\mathop{\derivOp_{#1}}}
%% \nc\derivs[1]{\mathop{\derivsOp_{#1}}}
%% \nc\conv{\ast}
\nc\conv{*}
\nc\zero{\mathbf{0}}
\nc\one{\mathbf{1}}
\nc\hasEps{\mathop{\Varid{has}_{\mempty}}}
\nc\id{\mathop{\Varid{id}}}
\nc\ite[3]{\text{if}\ #1\ \text{then}\ #2\ \text{else}\ #3}
\newcommand\iteB[3]{
\begin{cases}
#2 & \text{if $#1$} \\
#3 & \text{otherwise}
\end{cases}}
\nc\lis{\mathop{\Varid{list}}}
\nc\liftA{\mathop{\Varid{liftA}}}
\nc\cons{\mathit{:}}

%% \DeclareMathOperator{\true}{true}
%% \DeclareMathOperator{\false}{false}

%% TODO: eliminate most of these latex macros, in favor of lhs2tex rendering.

\nc\bigOp[3]{{\displaystyle \hspace{-#3ex}#1\limits_{\substack{#2}}\hspace{-#3ex}}}

\begin{document}

\maketitle

\begin{abstract}

A number of useful and interesting tasks can be formulated in the vocabulary of \emph{semirings}\out{, which are types that have addition, multiplication, and their corresponding identities zero and one.
Multiplication with one must form a monoid, while addition with zero must form commutative monoid.
As in a ring, multiplication distributes over addition, but unlike rings, there needn't be an additive inverse}.
A somewhat less well-known abstraction is \emph{semimodules}, which are like vector spaces but with the requirement of a \emph{field} of scalars relaxed to a semiring.
Using the perspective of semirings and free semimodules, this paper explores formal languages and derives algorithms for language recognition (matching) that correspond to a method of Brzozowski, while generalizing this method to a broader setting, including counted and weighted ``languages'' as well as relations.

Although Brzozowski formulated his method in terms of regular expressions, free semimodules appear to be a more natural and general setting.
Regular expressions become a special case, while \emph{tries} offer a natural alternative that appears to be simpler and more efficient.
Rather than constructing a grammatical representation that gets successively ``differentiated'' in Brzozowski's method, the standard notion of trie already has derivatives built in, saving much redundant work without the need for explicit memoization.
Since tries generalize elegantly from sets to functions and from strings to algebraic data types, the essential theory and algorithms extend far beyond languages in the sense of sets of strings.
Underlying these variations is a notion of generalized \emph{convolution}, which itself (along with probabilistic computation) generalizes to the free semimodule monad.
This paper shows how to perform (generalized) convolution efficiently and easily, in one dimension or many, on time or space and on languages.
Aside from applications in image processing and machine learning, a simple and direct application of convolution is multiplication of polynomials, again in one or many dimensions (i.e., univariate or multivariate).
Along the way, we will the question of whether language ``derivatives'' are indeed derivatives, and in particular, of what functions.
The (affirmative) answer to this question draws a lovely path from a simple, well-known, and highly inefficient parsing technique based on backtracking to efficient, backtracking-free parsing.

All of the algorithms in the paper follow from very simple specifications in the form of homomorphisms that relate different representations to each other.

\end{abstract}

%format <+> = +
%format <.> = *
%% %format zero = 0
%% %format one = 1
%format zero = "\mathbf{0}"
%format one = "\mathbf{1}"

%% experiment
%format * = "\times"

%format `elem` = "\mathbin{`\Varid{elem}`}"
%format <# = "\mathop{\in}"
%format # = "\mid"

%format (wrap (a)) = a

%format (paren (e)) = "\left(" e "\right)"

%format N = "\mathbb{N}"
%format Pow = "\Pow"
%format emptyset = "\emptyset"
%format (single (s)) = "\single{"s"}"
%format (set (e)) = "\set{"e"}"
%format bigunion (lim) (body) = "\bigunion_{" lim "}{" body "}"
%format pow a (b) = a "^{" b "}"
%format `union` = "\cup"
%format union = (`union`)
%format star p = "\closure{"p"}"

%format bigUnion (lim) = "\bigOp\bigcup{" lim "}{0}"
%format bigSum (lim) = "\bigOp\sum{" lim "}{0}"
%format bigSumQ (lim) = "\bigOp\sum{" lim "}{1.5}"

%% \sectionl{Introduction}

\sectionl{Monoids, Semirings and Semimodules}

The ideas in this paper revolve around a small collection of closely related algebraic abstractions, so let's begin by introducing these abstractions along with examples.

\subsectionl{Monoids}

The simplest abstraction we'll use is the monoid, expressed in Haskell as follows:
\begin{code}
class Monoid a where
  mempty  :: a
  (<>)    :: a -> a -> a
  infixr 6 <>
\end{code}
The monoid laws require that |(<>)| (sometimes pronounced ``mappend'') be associative and that |mempty| is its left and right identity, i.e.,
\begin{code}
(u <> v) <> w == u <> (v <> w)
mempty <> v == v
u <> mempty == u
\end{code}
One monoid especially familiar to functional programmers is lists with append:
\begin{code}
instance Monoid [a] where
  mempty  = []
  (<>)    = (++)
\end{code}
Natural numbers form a monoid under addition and zero.

These two monoids are related via the function |length :: [a] -> N|, which not only maps lists to natural numbers, but does so in a way that preserves monoid structure:
\begin{code}
    length mempty
==  length []
==  0
==  mempty

    length (u <> v)
==  length (u ++ v)
==  length u + length v
==  length u <> length v
\end{code}
This pattern is common and useful enough to have a name:
\begin{definition}
A function |h| from one monoid to another is called a \emph{monoid homomorphism} when it satisfies the following properties:
\begin{code}
h mempty == mempty
h (u <> v) == h u <> h v
\end{code}
\end{definition}

A fancier monoid example is functions from a type to itself, also known as \emph{endofunctions}, for which |mempty| is the identity function, and |(<>)| is composition:
\begin{code}
newtype Endo a = Endo (a -> a)

instance Monoid (Endo a) where
  mempty = Endo id
  Endo g <> Endo f = Endo (g . f)
\end{code}
The identity and associativity monoid laws follow from the identity and associativity category laws, so we can generalize to endomorphisms, i.e., morphisms from an object to itself in any category.

A modest generalization of Cayley's theorem states that every monoid is isomorphic to a monoid of endofunctions \needcite{}.
(The Yoneda embedding generalizes this theorem to categories and endomorphisms \needcite{}.)
\begin{code}
toEndo :: Monoid a => a -> Endo a
toEndo a = Endo (\ z -> a <> z)

fromEndo :: Monoid a => Endo a -> a
fromEndo (Endo f) = f mempty
\end{code}
The embedding of |a| into |Endo a| provides another example of a monoid homomorphism:
\begin{code}
    toEndo mempty
==  Endo (\ z -> mempty <> z)                     -- |toEndo| definition
==  Endo (\ z -> z)                               -- monoid law
==  mempty                                        -- |id| on |Endo a|

    toEndo (a <> b)
==  Endo (\ z -> (a <> b) <> z)                   -- |toEndo| definition
==  Endo (\ z -> a <> (b <> z))                   -- monoid law
==  Endo ((\ z -> a <> z) . (\ z -> b <> z))      -- |(.)| definition
==  Endo (\ z -> a <> z) <> Endo (\ z -> b <> z)  -- |(<>)| on |Endo a|
==  toEndo a <> toEndo b                          -- |toEndo| definition (twice)
\end{code}
This embedding is useful for turning quadratic-time algorithms linear \needcite{}.

\subsectionl{Additive monoids}

While |(<>)| must be associative, it needn't be commutative.
Commutative monoids, however, will play an important role in this paper as well.
For clarity and familiarity, it will be convenient to use the name ``|(+)|'' instead of ``|(<>)|'' and refer to such monoids as ``additive'':
\begin{code}
class Additive b where
  zero  :: b
  (+)   :: b -> b -> b
  infixl 6 +
\end{code}
The |Additive| laws as the same as for |Monoid| (translating |mempty| and |(<>)| to |zero| and |(+)|), together with commutativity:
\begin{code}
(u + v) + w == u + (v + w)
zero + v == v
u + zero == u

u + v == v + u
\end{code}
While lists with append form a non-additive monoid, natural numbers with addition do.
Another example is sets with union:
\begin{code}
instance Additive (Pow a) where
  zero  = emptyset
  (+)   = union
\end{code}
Another example is functions with pointwise addition, with any domain and with any \emph{additive} codomain:
\begin{code}
instance Additive b => Additive (a -> b) where
  zero = \ a -> zero
  f + g  = \ a -> f a + g a
\end{code}
Curried functions of \emph{any number} of arguments (and additive result type) are additive, thanks to repeated application of this instance.
In fact, currying itself is an \emph{additive monoid homomorphism}:
\notefoot{Move these proofs to the appendix.}
\begin{code}
    curry zero
==  curry (\ (x,y) -> zero)                  -- |zero| on functions
==  \ x -> \ y -> zero                       -- |curry| definition
==  \ x -> zero                              -- |zero| on functions
==  zero                                     -- |zero| on functions

    curry (f + g)
==  curry (\ (x,y) -> f (x,y) + g (x,y))     -- |(+)| on functions
==  \ x -> \ y -> f (x,y) + g (x,y)          -- |curry| definition
==  \ x -> \ y -> curry f x y + curry g x y  -- |curry| definition (twice)
==  \ x -> curry f x + curry g x             -- |(+)| on functions
==  curry f + curry g                        -- |(+)| on functions
\end{code}
Likewise for uncurrying:
\notefoot{Probably suggest as an exercise.}
\begin{code}
    uncurry zero
==  uncurry (\ x -> zero)                         -- |zero| on functions
==  uncurry (\ x -> \ y -> zero)                  -- |zero| on functions
==  \ (x,y) -> zero                               -- |uncurry| definition
==  zero                                          -- |zero| on functions
    
    uncurry (f + g)
==  uncurry (\ x -> f x + g x)                    -- |(+)| on functions
==  uncurry (\ x -> \ y -> f x y + g x y)         -- |(+)| on functions
==  \ (x,y) -> f x y + g x y                      -- |uncurry| definition
==  \ (x,y) -> uncurry f (x,y) + uncurry g (x,y)  -- |uncurry| definition (twice)
==  uncurry f + uncurry g                         -- |(+)| on functions
\end{code}

\subsectionl{Semirings}

The natural numbers form a monoid in two familiar ways: addition and zero, and multiplication and one.
Moreover, these monoids interact usefully in two ways: multiplication distributes over addition, and multiplication by zero (the additive identity) yields zero (i.e., ``annihilates'').
Similarly, \emph{linear} endofunctions and their various representations (e.g., square matrices) forms a monoid in via addition and via composition, with composition distributing over addition, and composition with zero yielding zero.
In both examples, addition commutes; but natural number multiplication commutes, while composition does not.
The vocabulary and laws these examples share is called a \emph{semiring} (distinguished from a ring by dropping the requirement of additive inverses):
\begin{code}
class Additive b => Semiring b where
  one    :: b
  (<.>)  :: b -> b -> b
  infixl 7 <.>
\end{code}
The laws, in addition to those for |Additive| above, include multiplicative monoid, distribution, and annihilation:
\begin{code}
(u * v) * w == u * (v * w)
one * v == v
u * one == u

p * (q + r) == p * q + p * r
(p + q) * r == p * r + q * r

u * zero == zero
zero * v == zero
\end{code}
As mentioned, numbers and various linear endofunction representations form semirings.
A much simpler example is the semiring of booleans, with disjunction as addition and conjunction as multiplication (though we could reverse roles):
\begin{code}
instance Additive Bool where
  zero   = False
  (<+>)  = (||)

instance Semiring Bool where
  one    = True
  (<.>)  = (&&)
\end{code}
An example of a semiring homomorphism is a positivity test for natural numbers:
\begin{code}
positive :: N -> Bool
positive n = n > 0
\end{code}
Then |positive| is a semiring homomorphism, i.e., the following properties hold for |m,n :: N|:%
\footnote{\emph{Exercise:} What goes wrong if we replace natural numbers by integers?}
\begin{spacing}{1.5}
\begin{code}
positive zero  ==  False  == zero
positive one   ==  True   == one
positive (m  +  n) == positive m  ||  positive n == positive m  +  positive n
positive (m  *  n) == positive m  &&  positive n == positive m  *  positive n
\end{code}
\end{spacing}

\noindent
Another example semiring is functions, building on the |Additive (a -> b)| instance above:
\begin{code}
instance Semiring b => Semiring (a -> b) where
  one = \ a -> one
  f * g  = \ a -> f a * g a
\end{code}
As with |Additive|, this |Semiring| instance implies that curried functions (of any number and type of arguments and with semiring result type) are semirings, with |curry| and |uncurry| being semiring homomorphisms.

\subsectionl{Star semirings}

The semiring operations allow all \emph{finite} combinations of addition, zero, multiplication, and one.
It's often useful, however, to form infinite combinations, particularly in the form of Stephen Kleene's ``star'' (or ``closure'') operation:
% I can't get pow i working in context here
%format ptoi = "p^i"
\begin{code}
star p = bigSum (i>=0) (wrap (pow p i)) -- where |pow p 0 = one|, and |pow p (n+1) = p * pow p n|.
\end{code}
Another characterization is as a solution to either of the following semiring equations:
\begin{code}
star p == one + p * star p
star p == one + star p * p
\end{code}
which we will take as a laws for a new abstraction, as well as a default recursive implementation:
\begin{code}
class Semiring b => StarSemiring b  where
  star :: b -> b
  star p = one <+> p * star p
\end{code}
%format (inverse x) = x "^{-1}"
Sometimes there are more appealing alternative implementations.
For instance, when subtraction and division are available, we can instead define |star p = inverse (one - p)|.

One simple example of a star semiring (also known as a ``closed semiring'' \citet{Lehmann77}) is booleans:
\begin{code}
instance StarSemiring Bool where
  star b  = one + b * star b
          = True || (b && star b)
          = True
\end{code}
Another example is functions to any semiring:
\begin{code}
instance StarSemiring b => StarSemiring (a -> b) where
  star f = \ a -> star (f a)
\end{code}
To see that the law holds:
\begin{code}
    one + f * star f
==  \ a -> one + f a * star f a    -- |one|, |(+)|, and |(*)| on functions
==  \ a -> one + f a * star (f a)  -- |star| on functions
==  \ a -> star (f a)              -- star semiring law
==  star f                         -- |star| on functions
\end{code}

\noindent
An example star semiring homomorphism applies a given function to |mempty| (though any other domain value would serve):
%format atEps = "\Varid{at}_\epsilon"
\begin{code}
atEps :: ([a] -> Bool) -> Bool
atEps f = f mempty
\end{code}

A useful property of star semirings is that recursive affine equations have solutions.
Specifically, |p = b + m * p| has solution |p = star m * b| \citep{Dolan2013FunSemi}:
\begin{code}
    b + m * (star m * b)
==  b + (m * star m) * b      -- associativity of |(+)|
==  one * b + m * star m * b  -- identity for |(*)|
==  (one + m * star m) * b    -- distributivity
==  star m * b                -- star semiring law
\end{code}

\note{Mention tropical semirings, optimization algebra, schedule algebra (max-plus), and optimization algebra \citep{Golan2005RecentSemi}. Maybe also polynomials.}

\subsectionl{Semimodules}

%format .> = "\cdot"

%% Temporary deception. Later change scale's formatting back to the usual,
%% and introduce (.>).

%% %format `scale` = .>
%% %format scale = (`scale`)

As fields are to vector spaces, rings are to modules, and semirings are to \emph{semimodules}.
For any semiring |s|, a \emph{left |s|-semimodule} is a additive monoid whose values can be multiplied on the left by |s| values, which play the role of ``scalars''.
\begin{code}
class (Semiring s, Additive b) => LeftSemimodule s b | b -> s where
  (.>) :: s -> b -> b
\end{code}
In addition to the laws for the additive monoid |b| and the semiring |s|, we have the following laws specific to left semimodules: \citep{Golan2005RecentSemi}:
\begin{code}
(s * t) .> b == s .> (t .> b)
(s + t) .> b == s .> b + t .> b
s .> (b + c) == s .> b + s .> c

one   .> b == b
zero  .> b == zero
\end{code}
There is also a corresponding notion of \emph{right} |s|-semimodule with multiplication on the right by |s| values, which we will not need in this paper.
(Rings also have left- and right-modules, and in \emph{commutative} rings and semirings (including vector spaces), the left and right variant coincide.)

Familiar |s|-semimodule examples include various containers of |s| values, including single- or multi-dimensional arrays, infinite streams, sets, and multisets.
Another, of particular interest in this paper, is functions from any type to any semiring:
For instance,
\begin{code}
instance LeftSemimodule s (a -> s) where
  s .> f = \ a -> s * f a
\end{code}

%format <# = "\mathop{\in}"
%format # = "\mid"
\noindent
Next consider sets of values taken from a semiring.
We might be tempted to define |s .> p| to multiply |s| by each value in |p|, i.e.,
\begin{code}
instance LeftSemimodule s (Pow s) where s .> p = set (s * t | t <# p)    -- Wrong!
\end{code}
This definition, however, would violate the semimodule law that |zero .> p == zero|, since |zero .> p| would be |set zero|, but |zero| for sets is |emptyset|.
Both semimodule distributive fail as well.
There is an alternative, which though seemingly obscure at first, will prove useful later on.
If we ``scale'' by a boolean, the semimodule laws require |True| (|one|) to preserve sets and |False| (|zero|) to annihilate them:
\begin{code}
instance LeftSemimodule Bool (Pow a) where
  s .> p = if s then p else emptyset
\end{code}
so that |forall a. (a <# s .> p) <=> (s && a <# p)|, which resembles the |LeftSemimodule (a -> b)| instance given above.
This resemblance can be explained by noting the bijection between |Pow a| and |a -> Bool|:
\begin{code}
setTest :: Pow a -> (a -> Bool)
setTest as = \ a -> a <# as

testSet :: (a -> Bool) -> Pow a
testSet f = set (a | f a)
\end{code}
This relationship is not only a bijection, but a \emph{semimodule isomorphism} (i.e., a bijective semimodule homomorphism).

\subsectionl{Semimodules as semirings}

\note{I might next consider possibilities for sets as a semiring. One tempting possibility is to use ``nondeterministic'' addition and multiplication, but distributivity fails.
For instance, |(set 3 + set 5) * {0,...,10}| vs |set 3 * {0,...,10} + set 5 * {0,...,10}|, as the latter has many more values than the former.}

%% *   Languages
%% *   Regular expressions
%% *   Monoid semirings and convolution

\bibliography{bib}

\end{document}

*   Monoids, semirings and semimodules (with examples, interface, and laws):
    *   Monoids: lists, endomorphisms (Cayley)
    *   Commutative ("additive") monoids: natural numbers with addition (no negation), sets, functions.
    *   Semirings:
        *   Numbers
        *   Booleans
        *   Functions
        *   Square matrices (linear endomorphisms)
    *   Star semirings: sets, booleans, functions; affine fixed points
    *   Semimodules:
        *   Generalization/relaxation of vector spaces.
        *   Sets, multisets, fuzzy sets
        *   Free semimodules: isomorphic to functions from any type to any semiring
    *   Semimodules as semirings:
        *   Languages
        *   Regular expressions
        *   Monoid semirings and convolution
*   Homomorphisms:
    *   Definitions
    *   Examples:
        *   Natural numbers to booleans
        *   Lists to sets or to multisets
        *   Multisets to sets (cf natural numbers to booleans)
        *   Regular expressions to sets
        *   Contains `mempty` (`hasEps`)
    *   Homomorphisms as specifications
*   Language "derivatives":
    *   I'm unsure whether to place this section here.
        If so, how can I make it flow well?
    *   Briefly present Brzozowski's method (for recognizing regular languages).
    *   Context-free languages
*   Unsorted:
    *   Relate Brzozowski derivatives to the derivatives of residual functions, as in the notes below.
    *   Currying and convolution.
        Is currying a (star) semiring homomorphism?
    *   I think I want to say and demonstrate that Brzozowski's derivatives are not about regular expressions, grammars, or languages, so much as functions from lists and types that can be interpreted as functions from lists and a decomposition principle for such functions.
        Application of this principle to tries than to regular expressions is more natural and yields a more efficient implementation.
    *   The trie perspective naturally leads to generalizing from lists to arbitrary (regular?) algebraic data types.
        I'm less confident about this generalization claim, since I think we need a suitable monoid.
        I think there's an underlying generic monad that specializes to lists and other algebraic data types, with monadic bind specializing to `mappend`.
        On the other hand, with multiple substitution sites, inverting `mappend` seems tricky.
        Does it give a useful form of constrained or context-sensitive grammars?
    *   Convolution is a special case of the free semimodule applicative/monad.
    *   Since `[()] =~ N`, the technique specializes to 1D discrete convolution.
        We can increase the dimension for the general and special case via currying, which also corresponds to tries over higher-D indices.
