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

%format `elem` = "\mathbin{`\Varid{elem}`}"
%format <# = "\mathop{\in}"
%format # = "\mid"

%format (wrap (a)) = a

%format (paren (e)) = "\left(" e "\right)"

%format Pow = "\Pow"
%format emptyset = "\emptyset"
%format (single (s)) = "\single{"s"}"
%format (set (e)) = "\set{"e"}"
%format bigunion (lim) (body) = "\bigunion_{" lim "}{" body "}"
%format pow a (b) = a "^{" b "}"
%format `union` = "\cup"
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
  infixr 6 <>
  (<>)    :: a -> a -> a
\end{code}
The monoid laws require that |(<>)| (sometimes pronounced ``mappend'') be associative and that |mempty| is its left and right identity, i.e.,
\begin{code}
(u <> v) <> w == u <> (v <> w)
mempty <> v == v
u <> mempty == u
\end{code}
One monoid especially familiar to functional programmers is lists:
\notefoot{Maybe just say ``|(<>) = (++)|'' instead.}
\begin{code}
instance Monoid [a] where
  mempty = []
  [] <> bs = bs
  (a:as) <> bs = a : (as <> bs)
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
  infixl 6 +
  (+)   :: b -> b -> b
\end{code}
The |Additive| laws as the same as for |Monoid| (translating |mempty| and |(<>)| to |zero| and |(+)|), together with commutativity:
\begin{code}
(u + v) + w == u + (v + w)
zero + v == v
u + zero == u

u + v == v + u
\end{code}
Examples of additive monoids include natural numbers with addition and sets with union (but not lists with append).
Another example is functions with pointwise addition, with any domain and with any \emph{additive} codomain:
\begin{code}
instance Additive b => Additive (a -> b) where
  zero   = \ a -> zero
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
  infixl 7 <.>
  (<.>)  :: b -> b -> b
  one    :: b
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
  (<+>) = (||)
  zero = False

instance Semiring Bool where
  (<.>) = (&&)
  one = True
\end{code}
Another example is functions, building on the |Additive (a -> b)| instance above:
\begin{code}
instance Semiring b => Semiring (a -> b) where
  f * g  = \ a -> f a * g a
  one = \ a -> one
\end{code}
As with |Additive|, this |Semiring| instance implies that curried functions (of any number of arguments and with semiring result type) are semirings, with |curry| and |uncurry| being semiring homomorphisms.

\subsectionl{Star semirings}

The semiring operations allow all \emph{finite} combinations of addition, zero, multiplication, and one.
It's often useful, however, to form infinite combinations, particularly in the form of Stephen Kleene's ``star'' (or ``closure'') operation:
% I can't get pow i working in context here
%format ptoi = "p^i"
\begin{code}
star p = bigSum (i>=0) (wrap (pow p i)) -- where |pow p 0 = one|, and |pow p (n+1) = p * pow p n|.
\end{code}
Another characterization is as a solution to the following semiring equation:
\begin{code}
star p == one + p * star p
\end{code}
which we will take as a law for a new abstraction, as well as a default recursive implementation:
\begin{code}
class Semiring b => StarSemiring b  where
  star    :: b -> b
  star p  = one <+> p * star p
\end{code}
%format (inverse x) = x "^{-1}"
Sometimes there are more appealing alternative implementations.
For instance, when subtraction and division are available, we can instead define |star p = inverse (1 - p)|.

%% *   Semirings:
%%     *   Numbers
%%     *   Booleans
%%     *   Functions
%%     *   Square matrices (linear endomorphisms)
%% *   Star semirings: sets, booleans, functions; affine fixed points

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

