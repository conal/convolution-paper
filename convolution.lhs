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
%format zero = 0
%format one = 1
%% %format zero = "\mathbf{0}"
%% %format one = "\mathbf{1}"

%% experiment
%% %format * = "\times"

%format `elem` = "\mathbin{`\Varid{elem}`}"
%format <# = "\mathop{\in}"
%format # = "\mid"

%% Sometimes formatting breaks without an infix separator.
%format @@ = "{\,}"
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
%format `intersection` = "\cap"
%format intersection = (`intersection`)
%format star p = "\closure{"p"}"
%format exists = "\exists"

%format bigUnion (lim) = "\bigOp\bigcup{" lim "}{0}"
%format bigSum (lim) = "\bigOp\sum{" lim "}{0}"
%format bigSumQ (lim) = "\bigOp\sum{" lim "}{1}"

%format bigOr (lim) = "\bigOp\bigvee{" lim "}{0}"
%format bigOrQ (lim) = "\bigOp\bigvee{" lim "}{1.5}"
%format BR = "\!\!\\\!\!"
%% %format BR = "\hspace{-5mu}\\\hspace{-5mu}"

%format (inverse x) = x "^{-1}"

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
==  length []             -- |mempty| on |[a]|
==  zero                  -- |length| definition
==  mempty                -- |zero| on |N|

    length (u <> v)
==  length (u ++ v)       -- |(<>)| on |[a]|
==  length u + length v   -- |length| definition and induction
==  length u <> length v  -- |(<>)| on |N|
\end{code}
This pattern is common and useful enough to have a name:
\begin{definition} \deflabel{monoid homomorphism}
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

\subsectionl{Additive Monoids}

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

\noindent
Additive monoids have their form of homomorphism:
\begin{definition} \deflabel{additive monoid homomorphism}
A function |h| from one additive monoid to another is an \emph{additive monoid homomorphism} if it satisfies the following properties:
\begin{code}
h zero == zero
h (u + v) == h u + h v
\end{code}
\end{definition}
\noindent
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

\noindent
\begin{definition} \deflabel{semiring homomorphism}
A function |h| from one semiring to another is a \emph{semiring homomorphism} if it is an additive monoid homomorphism (\defref{additive monoid homomorphism}) and satisfies the following additional properties:
\begin{code}
h one == one
h (u * v) == h u * h v
\end{code}
\end{definition}

\noindent
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

\subsectionl{Star Semirings}

The semiring operations allow all \emph{finite} combinations of addition, zero, multiplication, and one.
It's often useful, however, to form infinite combinations, particularly in the form of Stephen Kleene's ``star'' (or ``closure'') operation:
% I can't get pow i working in context here
%format ptoi = "p^i"
\begin{code}
star p = bigSum (i>=0) @@ pow p i -- where |pow p 0 = one|, and |pow p (n+1) = p * pow p n|.
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
Sometimes there are more appealing alternative implementations.
For instance, when subtraction and division are available, we can instead define |star p = inverse (one - p)|.

Predictably,
\begin{definition} \deflabel{star semiring homomorphism}
A function |h| from one star semiring to another is a \emph{star semiring homomorphism} if it is a semiring homomorphism (\defref{semiring homomorphism}) and satisfies the following additional property:
\begin{code}
h (star p) = star (h p)
\end{code}
\end{definition}

\noindent
One simple example of a star semiring (also known as a ``closed semiring'' \citet{Lehmann77}) is booleans:
\begin{code}
instance StarSemiring Bool where
  star b  = one + b * star b
          = True || (b && star b)
          = True
          = one
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
Combining these two instances, consider |star f| for |f :: a -> Bool| (a ``predicate''):
\begin{code}
    star f
==  \ a -> star (f a)  -- |star| on functions
==  \ a -> one         -- |star| on |Bool|
==  one                -- |one| on functions
\end{code}

%if False
%% Now in a later section
\noindent
An example star semiring homomorphism applies a given function to |mempty| (though any other domain value would serve):
%format atEps = "\Varid{at}_\epsilon"
\begin{code}
atEps :: ([a] -> Bool) -> Bool
atEps f = f mempty
\end{code}
%endif

A useful property of star semirings is that recursive affine equations have solutions:
\begin{lemma}\lemlabel{affine over semiring}
The affine equation |p = b + m * p| has solution |p = star m * b| \citep{Dolan2013FunSemi}:
\end{lemma}
\begin{code}
    b + m * (star m * b)
==  b + (m * star m) * b      -- associativity of |(+)|
==  one * b + m * star m * b  -- identity for |(*)|
==  (one + m * star m) * b    -- distributivity
==  star m * b                -- star semiring law
\end{code}

\note{Mention tropical semirings, schedule algebra (max-plus), and optimization algebra (min-plus) \citep{Golan2005RecentSemi}. Maybe also polynomials.}

\subsectionl{Semimodules}

%format .> = "\cdot"

%% Temporary deception. Later change scale's formatting back to the usual,
%% and introduce (.>).

As fields are to vector spaces, rings are to modules, and semirings are to \emph{semimodules}.
For any semiring |s|, a \emph{left |s|-semimodule} |b| is a additive monoid whose values can be multiplied on the left by |s| values.
Here, |s| plays the role of ``scalars'', while |b| plays the role of ``vectors''.
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
There is also a corresponding notion of \emph{right} |s|-semimodule (with multiplication on the right by |s| values), which we will not need in this paper.
(Rings also have left- and right-modules, and in \emph{commutative} rings and semirings (including vector spaces), the left and right variants coincide.)

As usual, we have a corresponding notion of homomorphism, which is more commonly referred to as ``linearity'':
\begin{definition} \deflabel{left semimodule homomorphism}
A function |h| from one left |s|-semimodule to another is a \emph{left |s|-semimodule homomorphism} if it is an additive monoid homomorphism (\defref{additive monoid homomorphism}) and satisfies the following additional properties:
\begin{code}
h (s .> b) == s .> h b
\end{code}
\end{definition}

Familiar |s|-semimodule examples include various containers of |s| values, including single- or multi-dimensional arrays, infinite streams, sets, and multisets.
Another, of particular interest in this paper, is functions from any type to any semiring:
For instance,
\begin{code}
instance LeftSemimodule s (a -> s) where
  s .> f = \ a -> s * f a
\end{code}
If we think of |a -> s| as a ``vector'' of |s| values, indexed by |a|, then |s .> f| scales each component of the vector |f| by |s|.

%format `scale` = "\mathbin{\hat{".>"}}"
%format scale = "("`scale`")"
There's a very important optimization to be made for scaling.
When |s == zero|, |s .> p == zero|, so we can discard |p| entirely.
Rather than burden each |LeftSemimodule| instance with this optimization, let's define |(.>)| to apply this optimization on top of a more primitive |scale| method:
\begin{code}
class (Semiring s, Additive b) => LeftSemimodule s b | b -> s where
  scale :: s -> b -> b

(.>) :: (Semiring b, Scalable b s, DetectableZero s) => s -> b -> b
s .> b  | isZero s   = zero
        | otherwise  = s `scale` b
\end{code}
The |DetectableZero| class \citep{semiring-num}:
\begin{code}
class Semiring a => DetectableZero a where isZero :: a -> Bool
\end{code}

Recursive affine equations in semimodules over star semirings have solutions:
\begin{lemma}\lemlabel{affine over semimodule}
The affine equation |q == r <+> s .> q| has solution |q = star s .> r|.
\end{lemma}
\begin{proof}~
\begin{code}
    star s .> r
==  (one <+> s <.> star s) .> r         -- star semiring law
==  one .> r <+> (s <.> star s) .> r    -- distributivity
==  r <+> s .> (star s .> r)            -- multiplicative identity and associativity
\end{code}
\end{proof}

\subsectionl{Singletons}

We now have a fair amount of vocabulary for combining values.
We'll also want an operation that constructs a ``vector'' with a single non-zero component:
%format +-> = "\mapsto"
\begin{code}
infix 1 +->
class HasSingle a b x | x -> a b where
  infixr 1 +->
  (+->) :: a -> b -> x
\end{code}
Two specializations of |a +-> b| will come in handy: one for |a = mempty|, and one for |b = one|.
\begin{code}
single :: (HasSingle a b x, Semiring b) => a -> x
single a = a +-> one

value :: (HasSingle a b x, Monoid a) => b -> x
value b = mempty +-> b
\end{code}
In particular, |mempty +-> one == single mempty == value one|.
As first examples, we have sets and functions:
\begin{code}
instance HasSingle a Bool (P a) where
  a +-> b = if b then set a else emptyset

instance (Eq a, Additive b) => HasSingle a b (a -> b) where
  a +-> b = \ a' -> if a == a' then b else zero
\end{code}

\noindent
The |(+->)| operation gives a way to decompose arbitrary functions:
\begin{lemma}[\provedIn{lemma:decomp +->}]\lemlabel{decomp +->}
For all |f :: a -> b| where |b| is a semiring,
\begin{code}
f == bigSum a a +-> f a
\end{code}
\end{lemma}

\sectionl{Calculating Instances from Homomorphisms}

In \secref{Monoids, Semirings and Semimodules}, we met the |Additive| instance for sets, along with the |Additive|, |Semiring|, and |LeftSemimodule| instances for functions.
Do sets also have (law-abiding) |Semiring| and |LeftSemimodule| instances?
Is there more than one choice, and if so, how might we choose?

Let's start investigating these questions by reviewing the |Additive| instances for functions and sets from \secref{Additive Monoids}:
\\
\begin{minipage}[b]{0.41\textwidth}
\begin{code}
instance Additive b => Additive (a -> b) where
  zero = \ a -> zero
  f + g  = \ a -> f a + g a
\end{code}
\end{minipage}
\begin{minipage}[b]{0ex}{\rule[2ex]{0.5pt}{0.5in}}\end{minipage}
\begin{minipage}[b]{0.3\textwidth} % \mathindent1em
\begin{code}
instance Additive (Pow a) where
  zero = emptyset
  p + q = p `union` q
\end{code}
\end{minipage}
\\
Sets and functions-to-booleans (``predicates'') are closely related via set membership:
%format setPred = pred
%% doesn't work
%format predSet = inverse setPred
%format predSet = setPred "^{-1}"
\begin{code}
setPred :: Pow a -> (a -> Bool)
setPred as = \ a -> a <# as

predSet :: (a -> Bool) -> Pow a
predSet f = set (a | f a)
\end{code}
This relationship is not only a bijection, but a \emph{bijective additive monoid homomorphism}:
\begin{code}
    setPred zero
==  \ a -> a <# zero                  -- |setPred| definition
==  \ a -> a <# emptyset              -- |zero| on |P a|
==  \ a -> False                      -- property of sets
==  \ a -> zero                       -- |zero| on |Bool|
==  zero                              -- |zero| on functions

    setPred (p + q)
==  \ a -> a <# (p + q)               -- |setPred| definition
==  \ a -> a <# (p `union` q)         -- |(+)| on |P a|
==  \ a -> (a <# p) || (a <# q)       -- property of sets
==  \ a -> (a <# p) + (a <# q)        -- |(+)| on |Bool|
==  \ a -> setPred p a + setPred q a  -- |setPred| definition
==  setPred p + setPred q             -- |(+)| on functions
\end{code}
Likewise for |predSet|, following from similar reasoning or more immediately from bijectivity%
%if False
.
%else
:
\begin{code}
    predSet zero
==  predSet (setPred zero)                               -- above
==  zero                                                 -- |predSet . setPred == id|

    predSet (f + g)
==  predSet (setPred (predSet f) + setPred (predSet g))  -- |setPred . predSet == id|
==  predSet (setPred (predSet f + predSet g))            -- above
==  predSet f + predSet g                                -- |setPred . predSet == id|
\end{code}
%endif

So far, we've started with instance definitions and then proved such homomorphisms.
We can instead invert the process, taking homomorphisms as specifications and \emph{calculating} instance definitions that satisfy them.
This process of calculating instances from homomorphisms is the central guiding principle throughout the rest of this paper, so let's see how it works.

We have a |Semiring| instance for functions to any semiring---and hence to |Bool| in particular---and we have a function |setPred| from sets to membership functions (predicates).
We've see that |setPred| is an additive monoid homomorphism, based on a known |Additive| instance for sets.
Now let's also require |setPred| to be a \emph{semiring homomorphism} and deduce a sufficient |Semiring| instance for sets.
The needed homomorphism properties:
\begin{spacing}{1.2}
\begin{code}
setPred one == one
setPred (p * q) == setPred p * setPred q
\end{code}
\end{spacing}
We already know definitions of |setPred| as well as the function versions of |one| and |(*)| (on the RHS) but not yet the set versions of |one| and |(*)| (on the LHS).
We thus have two algebra problems in two unknowns.
Since only one unknown appears in each homomorphism equation, we can solve them independently.
The |setPred|/|predSet| isomorphism makes it easy to solve these equations, and removes all semantic choice (allowing only varying implementations of the same meaning).
\begin{code}
     setPred one == one
<=>  predSet (setPred one) == predSet one                          -- |predSet| injectivity
<=>  one == predSet one                                            -- |predSet . setPred == id|

     setPred (p * q) == setPred p * setPred q
<=>  predSet (setPred (p * q)) == predSet (setPred p * setPred q)  -- |predSet| injectivity
<=>  p * q == predSet (setPred p * setPred q)                      -- |predSet . setPred == id|
\end{code}
We thus have a sufficient (and in this case semantically necessary) definitions for |one| and |(*)| on sets.
Now let's simplify to get more direct definitions:
\begin{code}
    predSet one
==  predSet (\ a -> one)                         -- |one| on functions
==  predSet (\ a -> True)                        -- |one| on |Bool|
==  set (a # True)                               -- |predSet| definition

    predSet (setPred p * setPred q)
==  predSet ((\ a -> a <# p) * (\ a -> a <# q))  -- |setPred| definition (twice)
==  predSet (\ a -> (a <# p) * (a <# q))         -- |(*)| on functions
==  predSet (\ a -> a <# p && a <# q)            -- |(*)| on |Bool|
==  set (a # a <# p && a <# q)                   -- |predSet| definition
==  p `intersection` q                           -- |intersect| definition
\end{code}
Without applying any real creativity, we have deduced the desired |Semiring| instance for sets, which has a pleasing duality with the |Additive| instance:
\begin{code}
instance Semiring (P a) where
  one = set (a # True)
  p * q = p `intersection` q
\end{code}

We can similarly calculate a |StarSemiring| instance for sets from a requirement that |predSet| be a star semiring homomorphism.
That homomorphism equation:
\begin{code}
setPred (star p) == star (setPred p)
\end{code}
Equivalently,
\begin{code}
    star p
==  predSet (star (setPred p))  -- |predSet| injectivity
==  predSet one                 -- |star| on |Bool| (\secref{Star Semirings})
==  one                         -- |predSet| is a semiring homomorphism
\end{code}

Next consider a |LeftSemimodule| instance for sets.
We might be tempted to define |s .> p| to multiply |s| by each value in |p|, i.e.,
\begin{code}
instance LeftSemimodule s (Pow s) where s `scale` p = set (s * t | t <# p)    -- \emph{wrong}
\end{code}
This definition, however, would violate the semimodule law that |zero .> p == zero|, since |zero .> p| would be |set zero|, but |zero| for sets is |emptyset|.
Both semimodule distributive laws fail as well.
There is an alternative choice, necessitated by requiring that |predSet| be a left |Bool|-semimodule homomorphism.
The choice of |Bool| is inevitable from the type of |predSet| and the fact that |a -> b| is a |b|-semimodule for all semirings |b|, so |a -> Bool| is a |Bool|-semimodule.
The necessary homomorphism property:
\begin{code}
setPred (s .> p) == s .> setPred p
\end{code}
Equivalently,
\begin{code}
    s .> p
==  predSet (s .> setPred p)                                    -- |predSet| injectivity
==  predSet (s .> (\ a -> a <# p))                              -- |setPred| definition
==  predSet (\ a -> s * (a <# p))                               -- |(.>)| on functions
==  predSet (\ a -> s && a <# p)                                -- |(*)| on |Bool|
==  set (a # s && a <# p)                                       -- |predSet| definition
==  if s then set (a # s && a <# p) else set (a # s && a <# p)  -- property of |if|
==  if s then set (a # a <# p) else emptyset                    -- simplify conditional branches
==  if s then p else emptyset                                   -- |predSet . setPred == id|
==  if s then p else zero                                       -- |zero| for sets
\end{code}
Summarizing,
\begin{code}
instance LeftSemimodule Bool (Pow a) where
  s `scale` p = if s then p else zero
\end{code}
While perhaps obscure at first, this alternative will prove useful later on.

Note that the left |s|-semimodule laws specialized to |s=Bool| require |True| (|one|) to preserve and |False| (|zero|) to annihilate the second |(.>)| argument, so \emph{every} left |Bool|-semimodule instance must agree with this definition.
\out{Also note that |forall a. (a <# s .> p) <=> (s && a <# p)|, which resembles the |LeftSemimodule (a -> b)| instance given above.}

\note{Demonstrate that homomorphic specifications also guarantee that laws hold, assuming that equality is consistent with homomorphism.}

\sectionl{Languages and the monoid semiring}

A ``language'' is a set of strings over some alphabet, so the |Additive|, |Semiring|, and |LeftSemimodule| instances for sets given above apply directly to languages.
Other than |(.>)| and |star|, all of the operations provided by these instances correspond to common and useful building blocks of languages.
Conspicuously missing, however, are the usual notions of language concatenation and closure (Kleene star), defined as follows for languages |U| and |V|:
\begin{code}
U V = set (u <> v | u <# U && v <# V)

star U = bigUnion (i >= 0) @@ pow U i -- where |pow U 0 = one|, and |pow U (n+1) = U @@ pow U n|.
\end{code}
Intriguingly, this |star U| definition would satisfy the |StarSemiring| laws if |(*)| were language concatenation.
A bit of reasoning shows that all of the semiring laws would hold as well:
\begin{itemize}
\item Concatenation is associative and has as identity the language |set mempty|.
\item Concatenation distributes over union, both from the left and from the right.
\item The |zero| (empty) language annihilates (yields |zero|) under concatenation, both from the left and from the right.
\end{itemize}
Moreover, all we needed from strings is that they form a monoid.

We could decide that we have the wrong |Semiring| instance for sets, which would imply that the |setPred| homomorphisms in \secref{Calculating Instances from Homomorphisms} are the wrong specifications to use.
The existing |Semiring| instance for sets is useful, however, and is compelling in its relationship to functions and |Bool|.
Moreover, the concatenation-based semiring only applies to sets of values from a monoid, while the existing instance applies to sets of all types.
Instead of replacing our |Semiring (P a)| instance, let's add a new one.
Doing so requires a new type that shares essentially the same |Additive| and |LeftSemimodule| instances:\footnote{The ``|deriving|'' clause \needcite{}, of which we'll make similar use later in the paper, means that the |newtype| constructor/isomorphism is a homomorphism for the derived classes (|Additive|, |LeftSemimodule|, and |HasSingle|) and so is equivalent to the following instance definitions:
\begin{code}
instance Additive (Language a) where
  zero = L zero
  L p + L q = L (p + q)

instance LeftSemimodule Bool (Language a) where
  s `scale` L p = L (s .> p)

instance HasSingle Bool (Language a) where
  a +-> b = L (a +-> b)
\end{code}
}
\begin{code}
type Language a = L (P a) deriving (Additive, LeftSemimodule Bool, HasSingle a Bool)

instance Monoid a => Semiring (Language a) where
  one = L (set mempty) -- |== mempty +-> one == single mempty == value one| (\secref{Singletons})
  L p * L q = L (set (u <> v # u <# p && v <# q))

instance StarSemiring (Language a) -- use default |star| definition (\secref{Star Semirings}).
\end{code}

\noindent
%format <-- = "\leftarrow"
These new instances indeed satisfy the laws for additive monoids, semimodules, semirings, and star semirings.
They seem to spring from nothing, however, which is a bit disappointing compared with the way the set instances follow inevitably from the requirement that |setPred| be a star semiring homomorphism (\secref{Calculating Instances from Homomorphisms}).
Let's not give up yet, however.
Perhaps there's a variation of the |a -> b| semiring that specializes with |b = Bool| to bear the same relationship to |Language a| that |a -> Bool| bears to |P a|.
For reasons to become clear later, let's call this |a -> b| variation ``|b <-- a|'':
\notefoot{Introduce |Indexable| sooner, and add to the |deriving| list.}
\begin{code}
infixl 0 <--
newtype b <-- a = F (a -> b) deriving (Additive, HasSingle a b, LeftSemimodule b, Indexable a b)
\end{code}
The least imaginative thing we can try is to exactly mirror the |setPred|/|predSet| isomorphism:
%format recogLang = lang
%format langRecog = inverse recogLang
%format langRecog = recogLang "^{-1}"
\begin{code}
recogLang :: (Bool <-- a) -> Set a
recogLang (F f) = L (predSet f)

langRecog :: Language a -> (Bool <-- a)
langRecog (L p) = F (setPred p)
\end{code}
To cement our analogy, let's require that |recogLang| (and hence |langRecog|) be a homomorphism for all of the classes defined in \secref{Monoids, Semirings and Semimodules}.
If we apply the same sort of reasoning as in \secref{Calculating Instances from Homomorphisms} and then generalize from |Bool| to an arbitrary semiring, we get the definitions in \figrefdef{<--}{The monoid semiring}{
\begin{code}
instance (Semiring b, Monoid a) => Semiring (b <-- a) where
  one = F (single mempty)
  F f * F g  = bigSum (u,v) u <> v +-> f u <.> g v
             = F (\ w -> bigSumQ (u,v BR u <> v == w) f u <.> g v)

instance (Semiring b, Monoid a)  => StarSemiring (b <-- a)  -- default |star|
\end{code}
}.
The |b <-- a| type is known as ``the monoid semiring'', and its |(*)| operation as ``convolution'' \citep{golan2013semirings,wilding2015linear}.

\begin{theorem}[\provedIn{theorem:Semiring (b <-- a)}]\thmlabel{Semiring (b <-- a)}
Given the derived and explicitly defined instances for |b <-- a| above, |recogLang| is a homomorphism with respect to each instantiated class.
\end{theorem}

%% %format splits = split
For some monoids, we can also express the product operation in a more clearly computable form via \emph{splittings}:
%format bigSumSplits (lim) = "\bigOp\sum{" lim "}{2.5}"
\begin{code}
  F f <.> F g = F (\ w -> bigSumSplits ((u,v) <# splits w) f u * g v)
\end{code}
where |splits w| yields all pairs |(u,v)| such that |u <> v == w|:
% \notefoot{Maybe generalize from \emph{lists} of pairs to an associated |Foldable|.}
\begin{code}
class Monoid t => Splittable t where
  splits   :: t -> [(t,t)]  -- multi-valued inverse of |mappend|
\end{code}
Examples of splittable monoids include natural numbers and lists:
\begin{code}
instance Splittable N where
  splits n = [(i, n-i) | i <- [0 .. n]]

instance Splittable [a] where
  splits []      = [([],[])]
  splits (a:as)  = ([],a:as) : [((a:l),r) | (l,r) <- splits as]
\end{code}

\sectionl{Finite maps}

%% I'd like to 
%if False
\nc\mapSym{{}^{\scriptscriptstyle m}}
%format ->* = "\underset{\mapSym\:}{"->"}"
%format *<- = "\underset{\:\mapSym}{"<--"}"
%else
\nc\mapSym{{}_{\scriptscriptstyle\mathit{m}}}
%format ->* = "\overset{\mapSym\:}{"->"}"
%format *<- = "\overset{\:\mapSym}{"<--"}"
%endif

One representation of \emph{partial} functions is the type of finite maps, |a ->* b| from keys of type |a| to values of type |b|, represented is a key-ordered balanced tree \needcite{}.
To model \emph{total} functions instead, we can treat unassigned keys as denoting zero.
Conversely, merging two finite maps can yield a key collision, which can be resolved by addition.
Both interpretations require |b| to be a semiring.

Because we will encounter more representations of functions, let's use a common operation name for ``indexing'', or equivalently for interpreting as a function:
\begin{code}
class Indexable k v p | p -> k v where
  infixl 9 !
  (!) :: p -> k -> v
\end{code}
Given the definitions in \figrefdef{Map}{Finite maps as |a -> b|}{
\begin{code}
infixr 0 ->*
type a ->* b = Map a b

instance (Ord a, Additive b) => Indexable a b (a ->* b) where
  m ! k = M.findWithDefault zero k m

instance (Ord a, Additive b) => Additive (a ->* b) where
  zero = M.empty
  (<+>) = M.unionWith (<+>)

instance Ord a => LeftSemimodule (a ->* b) where
  s `scale` m = fmap (s NOP <.>) m

instance (Ord a, Additive b) => DetectableZero (a ->* b) where isZero = M.null

instance HasSingle a b (a ->* b) where (+->) = M.singleton
\end{code}
\vspace{-4ex}
}, |(!)| is a homomorphism with respect to each instantiated class.%
\footnote{The ``|M|'' module qualifier indicates names coming from the finite map library.}
\notefoot{Do I want a theorem and proof here?
I think so, though I'll have to make a few assumptions about finite maps.
On the other hand, those assumptions don't differ much from the homomorphism properties I'm claiming to hold.}
A semantically suitable |p <.> q| could be defined by assigning key |k| to |p ! k <.> q ! k| for keys defined in \emph{both} |p| and |q| and discarding the rest, which would otherwise multiply to zero.
On the other hand, a valid |one| for finite maps would have to assign |one| to \emph{every} key, of which there may well be infinitely many.

We can wrap |a ->* b| into a new type that does have a |Semiring| instance homomorphic to (and very closely resembling) that of |b <-- a| from \secref{Languages and the monoid semiring}, as shown in \figrefdef{*<-}{Finite maps as |b <-- a|}{
%format bigSumKeys (lim) = "\bigOp\sum{" lim "}{2}"
\begin{code}
infixl 0 *<-
newtype b *<- a = M (a ->* b) deriving (Additive, HasSingle a b, LeftSemimodule b, Indexable a b)

instance (Ord a, Monoid a, Semiring b) => Semiring (b *<- a) where
  one = single mempty
  M p <.> M q = bigSumKeys (u <# M.keys p BR v <# M.keys q) u <> v +-> p!u <.> q!v
\end{code}
\vspace{-4ex}
}.
%format !^ = "\hat{"!"}"
The finiteness of finite maps, however, interferes with giving a useful |StarSemiring| instance.
Given the definitions in \figref{*<-}, |(!^)| is a homomorphism with respect to each instantiated class, where |(!^)| interprets a representation as |b <-- a| instead of |a -> b|:
\begin{code}
(!^) :: Indexable a b z => z -> (b <-- a)
(!^) = F . (!)
\end{code}

\sectionl{Decomposing Functions from Lists}

%format <: = "\mathrel{\blacktriangleleft}"
%format <: = "\mathrel\triangleleft"
%format atEps = "\Varid{at}_\epsilon"
%format deriv = "\derivOp"

For functions from \emph{lists} specifically, we can decompose in a way that lays the groundwork for more efficient implementations than the ones in previous sections.
\begin{lemma}[\provedIn{lemma:decomp (b <-- [c])}]\lemlabel{decomp (b <-- [c])}
Any |f :: b <-- [c]| can be decomposed as follows:\footnote{In terms of |a -> [c]| rather than |[c] <-- a|, the definitions would read more simply:
\begin{code}
atEps f = f mempty
deriv f c cs = f (c:cs)
b <: h = \ NOP case {NOP [] -> b NOP ; NOP c:cs -> h c cs NOP}
\end{code}
%% (b <: h) []      = b
%% (b <: h) (c:cs)  = h c cs
\vspace{-3ex}
}
\begin{code}
f == atEps f <: deriv f
\end{code}
Moreover, for all |b| and |h|,
\begin{code}
atEps  (b <: h) = b
deriv  (b <: h) = h
\end{code}
where
\begin{code}
atEps :: (b <-- [c]) -> b
atEps (F f) = f mempty

deriv :: (b <-- [c]) -> c -> (b <-- [c])
deriv (F f) = \ c -> F (\ cs -> f (c:cs))

infix 1 <:
(<:) :: b -> (c -> (b <-- [c]) -> (b <-- [c])
b <: h = F (\ NOP case {NOP [] -> b NOP;NOP c:cs  -> unF (h c) cs NOP})
\end{code}
\vspace{-3ex}
\end{lemma}
\noindent
Considering the isomorphism |Pow [c] =~ Bool <-- [c]|, this decomposition generalizes the |delta| and |deriv| operations used by \citet{Brzozowski64} mapping languages to languages (as sets of strings), the latter of which he referred to as the ``derivative''.\footnote{Brzozowski wrote ``$\derivOp_c\,p$'' instead of ``|deriv p c|'', but the latter will prove more convenient below.}

Understanding how |atEps| and |deriv| relate to the semiring vocabulary will help us develop an efficient implementation in \secref{Tries}.

\begin{lemma}[\provedIn{lemma:atEps b <-- [c]}]\lemlabel{atEps b <-- [c]}
The |atEps| function is a star semiring and left semimodule homomorphism, i.e.,
\begin{code}
atEps zero         == zero
atEps one          == one
atEps (p  <+>  q)  == atEps p  <+>  atEps q 
atEps (p  <.>  q)  == atEps p  <.>  atEps q 

atEps (star p) == star (atEps p)
\end{code}
Moreover,\footnote{Mathematically, |atEps| is thus a left |b|-semiring homomorphism as well, since every semiring is a (left and right) semimodule over itself. Declaring them as such in the Haskell implementation, however, would lead to ambiguity during type inference.}
\begin{code}
atEps (s .> p) == s * atEps p
atEps (w +-> b) == if null w then b else zero
\end{code}
\note{Look for a more homomorphic framing of the |(+->)| equation, say ``|null w +-> b|'' or even ``|atEps w +-> b|''.
Again, there may be ambiguity issues with Haskell type inference.}
\end{lemma}
\begin{lemma}[\provedIn{lemma:deriv b <-- [c]}, generalizing Lemma 3.1 of \citet{Brzozowski64}]\lemlabel{deriv b <-- [c]}
Differentiation has the following properties:
\notefoot{If I replace application to |c| by indexing by |c| (i.e., |(! NOP c)|), will this lemma hold for all of the representations? I suspect so. Idea: Define $\derivOp_c\,p = \derivOp\,p\:!\:c$.}
\begin{code}
deriv zero  c == zero
deriv one   c == zero
deriv (p  <+>  q) c == deriv p c <+> deriv q c
deriv (p  <.>  q) c == atEps p .> deriv q c <+> deriv p c <.> q

deriv (star p) c == star (atEps p) .> deriv p c * star p

deriv (s .> p) c == s .> deriv p c

deriv (single [d]) c == equal c d
\end{code}
\end{lemma}
\begin{theorem}[\provedIn{theorem:semiring decomp b <-- [c]}]\thmlabel{semiring decomp b <-- [c]}
The following properties hold:
\begin{spacing}{1.2}
\begin{code}
zero  == zero  <: zero
one   == one   <: zero
(a  <:  dp) <+> (b <: dq)  == a  <+>  b <: dp <+> dq
(a  <:  dp) <.> q == a .> q <+> (zero <: fmap (<.> NOP q) dp)
star (a <: dp) = q where q = star a .> (one <: fmap (<.> NOP q) dp)

single w = product (map symbol w) where symbol d = zero <: equal d

s .> (a <: dp) = s <.> a <: fmap (s NOP .>) dp
\end{code}
\vspace{-6ex}
\end{spacing}
\end{theorem}

\workingHere

\note{Introduce decomposition first on |[c] -> b|, skipping |Semiring| and |StarSemiring|.
Then note that we'll want to generalize the decomposition, so define the |Decomposable| class.
Work out what laws I need for |Decomposable| in order to give one |Semiring| and one |StarSemiring| instance that covers various cases, even beyond lists.
I think I'll want to redefine |(<--)|, |LTrie'|, and |RegExp'|.}

\noindent
To make use of these insights, it will be convenient to generalize the decomposition to other representations:
\begin{code}
class Decomposable a h s | a -> h s where
  infix 1 <:
  (<:)   :: s -> h a -> a
  atEps  :: a -> s
  deriv  :: a -> h a
\end{code}
The definitions of |(<:)|, |atEps|, and |deriv| given above correspond to an instance |Semiring b => Decomposable (b <-- [c]) ((->) c) b|.

\note{Use an associated pattern synonym instead, as I've now done in the implementation.}

\sectionl{Tries}

\secref{Languages and the monoid semiring} gives an implementation of language recognition and its generalization to the monoid semiring |b <-- a|, packaged as instances of a few common algebraic abstractions (|Additive| etc).
While simple and correct, these implementations are quite inefficient, primarily due to naive backtracking.
As a simple example, consider the language |single "pickles" + single "pickled"|, and suppose we want to test the word ``pickling'' for membership.
The simple implementations above will first try ``pickles'', fail near the end, and then backtrack all the way to the beginning to try ``pickled''.
The second attempt redundantly discovers that the prefix ``pickl'' is also a prefix of the candidate word.
\note{Also mention nondeterministic splitting (|(<>)| inversion) for |(*)|, and clearly articulate how to avoid it. This explanation is less clear to me.}

This problem of redundant comparison is solved elegantly by the classic trie (``prefix tree'') data structure \needcite{}.
This data structure was later generalized to arbitrary (regular) algebraic data types \needcite{} and then from sets to functions \needcite{}.
We'll explore the data type generalization later.\notefoot{Add a forward pointer, or remove the promise.}
Restricting our attention to functions of lists (``strings'' over some alphabet), we can formulate a simple trie data type as follows:
\notefoot{Maybe another oppositely pointing arrows of some sort.
I might want yet another pair for generalized tries.}
%format :< = "\mathrel{\Varid{:\!\!\triangleleft}}"
\begin{code}
infix 1 :<
data LTrie c b = b :< (c ->* LTrie c b)
\end{code}
The similarity between the |LTrie| type and the function decomposition from \secref{Decomposing Functions from Lists} (motivating the constructor's name) makes for easy instance calculation.
As with |Pow a| and |a ->* b|, we can define a trie counterpart to the monoid semiring, here |b <-- [c]|.
\note{Consider combining the following two theorems into one.}
\begin{theorem}[\provedIn{theorem:LTrie}]\thmlabel{LTrie}
Given the definitions in \figrefdef{LTrie}{Tries as |[c] -> b|}{
\begin{code}
infix 1 :<
data LTrie c b = b :< (c ->* LTrie c b)

instance (Ord c, Additive b) => Indexable [c] b (LTrie c b) where
  (b :< dp) ! w = case w of {NOP [] -> b NOP;NOP c:cs -> dp ! c ! cs NOP}

instance (Ord c, Additive b) => Additive (LTrie c b) where
  zero = zero :< zero
  (a :< dp) <+> (b :< dq) = a <+> b  :<  dp <+> dq

instance (Ord c, Semiring b) => LeftSemimodule b (LTrie c b) where
  s `scale` (b :< dp) = s <.> b :< fmap (s NOP `scale`) dp

instance (Ord c, Additive b, DetectableZero b) => DetectableZero (LTrie c b) where
  isZero (a :< dp) = isZero a && isZero dp

instance (Ord c, Additive b) => HasSingle [c] b (LTrie c b) where
  w +-> b = foldr (\ c t -> zero :< (c +-> t)) (b :< zero) w
\end{code}
\vspace{-4ex}
}, |(!)| is a homomorphism with respect to each instantiated class.
\end{theorem}
%format :<: = "\mathrel{\Varid{:\!\!\triangleleft\!:}}"
\begin{theorem}[\provedIn{theorem:LTrie'}]\thmlabel{LTrie'}
Given the definitions in \figrefdef{LTrie'}{Tries as |b <-- [c]|}{
\begin{code}

newtype LTrie' b c = L (LTrie c b) deriving (Additive, HasSingle [c] b, LeftSemimodule b, Indexable [c] b)

infix 1 :<:
pattern (:<:) :: b -> (c ->* LTrie' b c) -> LTrie' b c
pattern b :<: d <- L (b :< (coerce -> d)) where b :<: d = L (b :< coerce d)

instance (Ord c, Semiring b, DetectableZero b) => Semiring (LTrie' b c) where
  one = one :<: zero
  (a :<: dp) <.> q = a .> q <+> (zero :<: fmap (<.> q) dp)

instance (Ord c, StarSemiring b, DetectableZero b) => StarSemiring (LTrie' b c) where
  star (a :<: dp) = q where q = star a .> (one :<: fmap (<.> q) dp)
\end{code}
}, |(!^)| is a homomorphism with respect to each instantiated class.\footnote{The pattern synonym |(:<:)| enables matching and constructing |LTrie'| values as if they were defined as |data LTrie' b c = b :<: (c ->* LTrie' c b)| \needcite{}.
This definition uses safe, zero-cost coercions between |c ->* LTrie c b| and |c ->* LTrie' b c| \needcite{Breitner2016SZC}.}
\notefoot{Introduce |DetectableZero| earlier.}
\end{theorem}

\workingHere

\sectionl{Regular Expressions}

\note{A sort of ``free'' variant of functions. Easy to derive homomorphically. Corresponds to \citet{Brzozowski64} and other work on recognizing and parsing by derivatives.}

\sectionl{What's to come}

\begin{itemize}
\item |DetectableZero|
\item Decomposing list functions
\end{itemize}

\sectionl{Miscellaneous notes}

\begin{itemize}
\item Say just ``semimodule'', and add a remark that I really mean ``left semimodule'' throughout.
  Or start out with ``left'', then make the remark, and then perhaps add an occasional ``(left)''.
\item Finite maps, either as a running example or in its own section.
One version like |a -> b| and another like |b <-- a|.
\item |single| as a monoid homomorphism (targeting the product monoid).
\item
  Homomorphisms:
  \begin{itemize}
  \item
    Definitions
  \item
    Examples:
    \begin{itemize}
    \item
      Natural numbers to booleans
    \item
      Lists to sets or to multisets
    \item
      Multisets to sets (cf natural numbers to booleans)
    \item
      Regular expressions to sets
    \item
      Contains |mempty| (|hasEps|)
    \end{itemize}
  \item
    Homomorphisms as specifications
  \end{itemize}
\item
  Language ``derivatives'':
  \begin{itemize}
  \item
    I'm unsure where to place this section.
  \item
    Briefly present Brzozowski's method (for recognizing regular languages).
  \item
    Context-free languages
  \end{itemize}
\item
  Unsorted:
  \begin{itemize}
  \item
    Relate Brzozowski derivatives to the derivatives of residual functions, as in the notes below.
  \item
    Currying and convolution.
    Is currying a (star) semiring homomorphism?
  \item
    I think I want to say and demonstrate that Brzozowski's derivatives are not about regular expressions, grammars, or languages, so much as functions from lists and types that can be interpreted as functions from lists and a decomposition principle for such functions.
    Application of this principle to tries than to regular expressions is more natural and yields a more efficient implementation.
  \item
    The trie perspective naturally leads to generalizing from lists to arbitrary (regular?) algebraic data types.
    I'm less confident about this generalization claim, since I think we need a suitable monoid.
    I think there's an underlying generic monad that specializes to lists and other algebraic data types, with monadic bind specializing to |mappend|.
    On the other hand, with multiple substitution sites, inverting |mappend| seems tricky.
    Does it give a useful form of constrained or context-sensitive grammars?
  \item
    Convolution is a special case of the free semimodule applicative/monad.
  \item
    Since |N =~ [()]|, the technique specializes to 1D discrete convolution.
    We can increase the dimension for the general and special case via currying, which also corresponds to tries over higher-D indices.
  \end{itemize}
\end{itemize}

\note{I might next consider possibilities for sets as a semiring. One tempting possibility is to use ``nondeterministic'' addition and multiplication, but distributivity fails.
For instance, |(set 3 + set 5) * {0,...,10}| vs |set 3 * {0,...,10} + set 5 * {0,...,10}|, as the latter has many more values than the former.}

\appendix

\sectionl{Proofs}

\subsection{\lemref{decomp +->}}\proofLabel{lemma:decomp +->}

\begin{code}
    bigSum a a +-> f a
==  bigSum a (\ a' -> if a' == a then f a else zero)  -- |(+->)| on |a -> b|
==  \ a' -> bigSum a if a' == a then f a else zero    -- |(<+>)| on |a -> b|
==  \ a' -> f a'                                      -- other addends vanish
==  f                                                 -- $\eta$ reduction
\end{code}

\subsection{\thmref{Semiring (b <-- a)}}\proofLabel{theorem:Semiring (b <-- a)}

There are three parts to the homomorphism requirements (\defreftwo{star semiring homomorphism}{left semimodule homomorphism}):
\begin{enumerate}

\item From |Additive|, |LeftSemimodule|, and |HasSingle|:
\begin{code}
recogLang zero == zero
recogLang (p + q) == recogLang p + recogLang q

recogLang (s .> p) == s .> recogLang p

recogLang (a +-> b) == a +-> b
\end{code}
These three equations hold due to the |deriving| clause in the |Language| definition above.
For instance,
\begin{code}
    recogLang (F f + F g)
==  recogLang (F (f + g))              -- |(+)| on |b <-- a| (derived)
==  L (predSet (f + g))                -- |recogLang| definition
==  L (predSet f + predSet g)          -- |predSet| is an |Additive| homomorphism
==  L (predSet f) + L (predSet g)      -- |(+)| on |Language a| (derived)
==  recogLang (F f) + recogLang (F g)  -- |recogLang| definition
\end{code}

\item From |Semiring|:
\begin{code}
recogLang one == one
recogLang (p * q) = recogLang p * recogLang q
\end{code}
Equivalently, applying |langRecog| to both sides and replacing |p| and |q| by |F f| and |F g|,
\begin{code}
one == langRecog one
F f * F g == langRecog (recogLang (F f) * recogLang (F g))
\end{code}
Simplify, and generalize the domain |b| from |Bool| to an arbitrary semiring:
\begin{code}
    langRecog one
==  langRecog (L (set mempty))                                       -- |one| on |Language a|
==  F (setPred (set mempty))                                         -- |langRecog| definition
==  F (\ w -> w <# set mempty)                                       -- |pred| definition
==  F (\ w -> w == mempty)                                           -- property of sets
==  F (mempty +-> one)                                               -- generalize |False|/|True| to |zero|/|one|
    
    langRecog (recogLang (F f) * recogLang (F g))
==  langRecog (L (predSet f) * L (predSet g))                        -- |recogLang| definition (twice)
==  langRecog (L (set (u <> v # u <# predSet f && v <# predSet g)))  -- |(*)| on |Language a|
==  langRecog (L (set (u <> v # f u && g v)))                        -- |predSet| definition (twice)
==  F (setPred (set (u <> v # f u && g v)))                          -- |langRecog| definition
==  F (\ w -> w <# set (u <> v # f u && g v))                        -- |setPred| definition
==  F (\ w -> bigOrQ (u,v BR u <> v == w) f u && g v)                -- property of sets
==  F (\ w -> bigSumQ (u,v BR u <> v == w) f u * g v)                -- generalize |(||||)|/|(&&)| to |(+)|/|(*)|
==  F (\ w -> bigSum (u,v) if u <> v == w then f u * g v else zero)  -- summation property
==  F (bigSum (u,v) u <> v +-> f u * g v)                            -- |(+->)| on |a -> b|
==  bigSum (u,v) F (u <> v +-> f u * g v)                            -- |(+)| on |b <-- a| (derived)
==  bigSum (u,v) u <> v +-> f u * g v                                -- |(+->)| on |b <-- a| (derived)
\end{code}

\note{Redo this proof, aiming at the |(+->)| form first, which more closely resembles the set version.
Then simplify to the lambda/sum form.}

\item For |StarSemiring| the default recursive definition embodies the star semiring law.
\note{Hm. Assuming not bottom?}

\end{enumerate}

%% \subsection{\thmref{Map}}\proofLabel{theorem:Map}

\subsection{\lemref{decomp (b <-- [c])}}\proofLabel{lemma:decomp (b <-- [c])}

\begin{proof}
Any argument to |f| must be either |[]| or |c : cs| for some value |c| and list |cs|.
Consider each case:
\begin{code}
    (atEps f <: deriv f) []
==  atEps f []                   -- |b <: h| definition
==  f []                         -- |atEps| definition
                                           
    (atEps f <: deriv f) (c:cs)  NOP
==  deriv f (c:cs)               -- |b <: h| definition
==  f (c:cs)                     -- |deriv| definition
\end{code}
Thus, for \emph{all} |w :: [c]|, |f w == (atEps f <: deriv f) w|, from which the lemma follows by extensionality.

For the other two equations:
\begin{code}
    atEps (b <: h)
==  atEps (F (\ NOP case {NOP [] -> b NOP ; NOP c:cs -> h c cs NOP}))                  -- |(<:)| definition
==  (\ NOP case {NOP [] -> b NOP ; NOP c:cs -> h c cs NOP}) []                         -- |atEps| definition
==  b                                                                                  -- semantics of |case|
\end{code}
\begin{code}
    deriv (b <: h)
==  deriv (F (\ NOP case {NOP [] -> b NOP ; NOP c:cs -> h c cs NOP}))                  -- |(<:)| definition
==  \ c -> F (\ cs -> (\ NOP case {NOP [] -> b NOP ; NOP c:cs -> h c cs NOP}) (c:cs))  -- |deriv| definition
==  \ c -> F (\ cs -> unF (h c) cs)                                                    -- semantics of |case|
==  \ c -> F (unF (h c))                                                               -- $\eta$ reduction
==  \ c -> h c                                                                         -- |F . unF == id|
==  h                                                                                  -- $\eta$ reduction
\end{code}
\end{proof}

\subsection{\lemref{atEps b <-- [c]}}\proofLabel{lemma:atEps b <-- [c]}

\begin{code}
    atEps zero
==  atEps (F (\ a -> zero))  -- |zero| on |b <-- a|
==  (\ a -> zero) []         -- |atEps| definition
==  zero                     -- $\beta$ reduction
\end{code}
\begin{code}
    atEps one
==  atEps (F (equal mempty))  -- |one| on |b <-- a|
==  equal mempty mempty       -- |atEps| definition            
==  one                       -- |equal| definition
\end{code}
\begin{code}
    atEps (F f <+> F g)
==  atEps (F (\ a -> f a <+> g a))      -- |(<+>)| on |b <-- a|
==  (\ a -> f a <+> g a) []             -- |atEps| definition
==  f [] <+> g []                       -- $\beta$ reduction
==  atEps (F f) <+> atEps (F g)         -- |atEps| definition
\end{code}
\begin{code}
    atEps (F f <.> F g)
==  atEps (bigSum (u,v) u <> v +-> f u <.> g v)               -- |(<.>)| on |b <-- a|
==  atEps (\ w -> bigSumQ (u,v BR u <> v == []) f u <.> g v)  -- alternative definition from \figref{<--}
==  bigSumKeys (u,v BR u == [] && v == []) NOP f u <.> g v    -- |u <> v == [] <=> u == [] && v == []| 
==  f [] <.> g []                                             -- singleton sum
==  atEps (F f) <.> atEps (F g)                               -- |atEps| definition
\end{code}
\begin{code}
    atEps (star p)
==  atEps (one <+> p <.> star p)        -- defining property of |star|
==  one <+> atEps p <.> atEps (star p)  -- |atEps| distributes over |one|, |(<+>)| and |(<.>)|
==  one <+> atEps p <.> star (atEps p)  -- \note{coinduction?}
==  star (atEps p)                      -- defining property of |star|
\end{code}
\begin{code}
    atEps (s .> F f)
==  atEps (F (\ a -> s * f a))  -- |(.>)| on |b <-- a|
==  (\ a -> s * f a) []         -- |atEps| definition
==  s * f []                    -- $\beta$ reduction
==  s * atEps (F f)             -- |atEps| definition
\end{code}
\begin{code}
    atEps (w +-> b)
==  atEps (F (\ w' -> if w' == w then b else zero))  -- |(+->)| on |b <-- [c]|
==  (\ w' -> if w' == w then b else zero) []         -- |atEps| definition
==  if [] == w then b else zero                      -- $\beta$ reduction
==  if null w then b else zero                       -- |null| definition
\end{code}

\note{To do: Fix various lemmas, theorems, and proofs to use |a +-> b| instead of |single a|.}

\note{For the |star p| proof, maybe instead show inductively that |atEps (pow p n) == pow (atEps p) n| for all |n >= 0|, and then appeal to the summation definition of |star p|.}

\subsection{\lemref{deriv b <-- [c]}}\proofLabel{lemma:deriv b <-- [c]}

\begin{code}
    deriv zero
==  deriv (F (\ w -> zero))                  -- |zero| on |b <-- a|
==  \ c -> F (\ cs -> (\ w -> zero) (c:cs))  -- |deriv| on |b <-- a|
==  \ c -> F (\ cs -> zero)                  -- $\beta$ reduction
==  \ c -> zero                              -- |zero| on |b <-- a|
==  zero                                     -- |zero| on |a -> b|
\end{code}
\vspace{-3ex}
\begin{code}
    deriv one
==  deriv (single mempty)                   -- |one| on |b <-- a|
==  deriv (F (equal mempty))                -- |single| on |b <-- a|
==  \ c -> F (\ cs -> equal mempty (c:cs))  -- |deriv| on |b <-- a|
==  \ c -> F (\ cs -> zero)                 -- |c:cs /= mempty|
==  \ c -> zero                             -- |zero| on |b <-- a|
==  zero                                    -- |zero| on |a -> b|
\end{code}
\vspace{-3ex}
\begin{code}
    deriv (F f <+> F g)
==  deriv (F (\ w -> f w <+> g w))                        -- |(<+>)| on |b <-- a|
==  \ c -> F (\ cs -> (\ w -> f w <+> g w) (c:cs))        -- |deriv| on |b <-- a|
==  \ c -> F (\ cs -> f (c:cs) <+> g (c:cs))              -- $\beta$ reduction
==  \ c -> F (\ cs -> f (c:cs)) <+> F (\ cs -> g (c:cs))  -- |(<+>)| on |b <-- a|
==  \ c -> deriv (F f) c <+> deriv (F g) c                -- |deriv| on |b <-- a|
==  deriv (F f) <+> deriv (F g)                           -- |(<+>)| on |a -> b|
\end{code}
\begin{code}
    deriv (F f <.> F g)
==  deriv (bigSum (u,v) u <> v +-> f u <.> g v)                                                                             -- |(<.>)| on |b <-- a|
==  deriv (bigSum v (mempty <> v +-> f mempty <.> g v) <+> bigSumQ (c',u',v) ((c':u') <> v +-> f (c':u') <.> g v))          -- empty vs nonempty |u|
==  deriv (bigSum v (mempty <> v +-> f mempty <.> g v)) <+> deriv (bigSumA (c',u',v) ((c':u') <> v +-> f (c':u') <.> g v))  -- additivity of |deriv| (above)
\end{code}
First addend:
\begin{code}
    deriv (bigSum v (mempty <> v +-> f mempty <.> g v))
==  deriv (bigSum v (v +-> f mempty <.> g v))  -- monoid law
==  deriv (f mempty .> bigSum v (v +-> g v))   -- distributivity (semiring law)
==  f mempty .> deriv (bigSum v v +-> g v)     -- linearity of |deriv| \note{(needs lemma)}
==  f mempty .> deriv (F g)                    -- \lemref{decomp +->}
==  atEps (F f) .> deriv (F g)                 -- |atEps| on |b <-- a|
\end{code}
Second addend:
\begin{code}
    deriv (bigSumA (c',u',v) ((c':u') <> v +-> f (c':u') <.> g v))
==  bigSumA (c',u',v) deriv ((c':u') <> v +-> f (c':u') <.> g v)    -- additivity of |deriv|
==  bigSumA (c',u',v) deriv (c' : (u' <> v) +-> f (c':u') <.> g v)  -- |(<>)| on lists
==  \ c -> bigSum (u',v) u' <> v +-> f (c:u') <.> g v               -- \lemref{deriv +->} below
==  \ c -> bigSum (u',v) u' <> v +-> (\ cs -> f (c:cs)) u' <.> g v  -- $\beta$ expansion
==  \ c -> F (\ cs -> f (c:cs)) <.> F g                             -- |(<.>)| on |b <-- a|
==  \ c -> deriv (F f) c <.> F g                                    -- |deriv| on |b <-- a|
\end{code}
Combine addends, and let |p = F f| and |q = F g|:
\begin{code}
    deriv (p <.> q) c
==  deriv (F f <.> F g) c
==  ...
==  atEps (F f) .> deriv (F g) c <+> deriv (F f) c <.> F g
==  atEps p .> deriv q c <+> deriv p c <.> q
\end{code}    

\noindent
Next, closure:
\begin{code}
    deriv (star p) c
==  deriv (one <+> p <.> star p) c                        -- star semiring law
==  deriv one c <+> deriv (p <.> star p) c                -- additivity of |deriv|
==  deriv (p <.> star p) c                                -- |deriv one c == zero| (above)
==  atEps p .> deriv (star p) c <+> deriv p c <.> star p  -- |deriv (p * q)| above
\end{code}
Thus, by \lemref{affine over semiring},
\begin{code}
deriv (star p) c == star (atEps p) .> deriv p c <.> star p
\end{code}

\note{|deriv (s .> p) c == s .> deriv p c|}

\note{|deriv (single [d]) c == equal c d|}


\begin{lemma}\lemlabel{deriv +->}
Differentiation and |(+->)| satisfy the following relationships:
\begin{code}
deriv (mempty +-> b) c == zero

deriv (c' : w +-> b) c == if c' == c then w +-> b else zero
\end{code}
\end{lemma}
\begin{proof}~
\begin{code}
    deriv (mempty +-> b) c
==  deriv (F (\ w -> if w == mempty then b else zero)) c         -- |(+->)| defining
==  F (\ cs -> (\ w -> if w == mempty then b else zero) (c:cs))  -- |deriv| on |b <-- a|
==  F (\ cs -> if c:cs == mempty then b else zero)               -- $\beta$ reduction
==  F (\ cs -> if False then b else zero)                        -- |c:cs /== mempty|
==  F (\ cs -> zero)                                             -- |if-then-else| definition
==  zero                                                         -- |zero| on |b <-- a|
\end{code}
\begin{code}
    deriv (c' : w +-> b) c
==  deriv (F (\ a -> if a == c':w then b else zero)) c               -- |(+->)| definition
==  F (\ cs -> (\ a -> if a == c':w then b else zero) (c:cs))        -- |deriv| on |b <-- a|
==  F (\ cs -> if c:cs == c':w then b else zero)                     -- $\beta$ reduction
==  F (\ cs -> if c==c' && cs == w then b else zero)                 -- injectivity of |(:)|
==  if c==c' then F (\ cs -> if cs == w then b else zero) else zero  -- property of |if-then-else|
==  if c==c' then w +-> b else zero                                  -- |(+->)| on |b <-- a|
\end{code}
\end{proof}
\vspace{-2ex}

\subsection{\thmref{semiring decomp b <-- [c]}}\proofLabel{theorem:semiring decomp b <-- [c]}

\note{Maybe not worth spelling out.
I could say ``Proof: Immediate from \lemrefthree{decomp (b <-- [c])}{atEps b <-- [c]}{deriv b <-- [c]}''.}

\begin{code}
    zero
==  atEps zero <: deriv zero  -- \lemref{decomp (b <-- [c])}
==  zero <: \ c -> zero       -- \lemreftwo{atEps b <-- [c]}{deriv b <-- [c]}
==  zero <: zero              -- |zero| on functions
\end{code}

\begin{code}
    one
==  atEps one <: deriv one  -- \lemref{decomp (b <-- [c])}
==  one <: \ c -> zero      -- \lemreftwo{atEps b <-- [c]}{deriv b <-- [c]}
==  one <: zero             -- |zero| on functions
\end{code}

\begin{code}
    (a <: dp) <+> (b <: dp)
==  atEps ((a <: dp) <+> (b <: dq)) <: deriv ((a <: dp) <+> (b <: dq))  -- \lemref{decomp (b <-- [c])}
==  a <+> b <: dp <+> dq                                                -- \lemref{atEps and deriv via (<:)} below
\end{code}

%% (a  <:  dp)  <.>  q == a .> q <+> (zero <: (<.> NOP q) . dp)

\begin{code}
    (a <: dp) <.> (b <: dq)
==  atEps ((a <: dp) <.> (b <: dq)) <: deriv ((a <: dp) <.> (b <: dq))        -- \lemref{decomp (b <-- [c])}
==  a <.> b <: \ c -> a .> dq c <+> dp c <.> (b <: dq)                        -- \lemref{atEps and deriv via (<:)} below
==  (a <.> b <+> zero) <: (\ c -> a .> dq c) <+> (\ c -> dp c <.> (b <: dq))  -- additive identity; |(<+>)| on functions
==  (a <.> b <: \ c -> a .> dq c) <+> (zero <: \ c -> dp c <.> (b <: dq))     -- previous result
==  a .> (b <: dq) <+> (zero <: \ c -> dp c <.> (b <: dq))                    -- \lemref{atEps and deriv via (<:)} below
==  a .> (b <: dq) <+> (zero <: (<.> NOP (b <: dq)) . dp)                     -- |(.)| definition
==  a .> (b <: dq) <+> (zero <: fmap (<.> NOP (b <: dq)) dp)                  -- fmap on functions
\end{code}

%% \lemref{atEps and deriv via (<:)}

%% star (a <: dp) = q where q = star a .> (one <: (<.> NOP q) .  dp)

\begin{code}
    star (a <: dp)
==  atEps (star (a <: dp)) <: deriv (star (a <: dp))                     -- \lemref{decomp (b <-- [c])}
==  star a <: \ c -> star a .> dp c * star (a <: dp)                     -- \lemref{atEps and deriv via (<:)} below
==  star a .> (one <: \ c -> dp c * star (a <: dp))                      -- \lemref{atEps and deriv via (<:)} below
\end{code}

\workingHere

\begin{code}
    s .> p
==  ...
\end{code}

%% single w = product (map symbol w)
%%   where
%%      symbol d = zero <: equal d

\begin{code}
    |single w|
==  ...
\end{code}

\begin{lemma}\lemlabel{atEps and deriv via (<:)}
The |atEps| and |deriv| functions satisfy the following properties in terms of |(<:)|-decompositions:
\begin{spacing}{1.2}
\begin{code}
atEps ((a <: dp)  <+>  (b <: dq)) == a <+> b
atEps ((a <: dp)  <.>  (b <: dq)) == a <.> b
atEps (star (a <: dp)) == star a
atEps (s .> (a <: dp)) == s * a

\end{code}
\begin{code}
deriv ((a <: dp)  <+>  (b <: dq)) c == dp c <+> dq c
deriv ((a <: dp)  <.>  (b <: dq)) c == a .> dq c <+> dp c <.> (b <: dq)
deriv (star (a <: dp)) c == star a .> dp c * star (a <: dp)
deriv (s .> (a <: dp)) c == s .> dp c
\end{code}
\end{spacing}
\end{lemma}
\begin{proof}
Substitute into \lemreftwo{atEps b <-- [c]}{deriv b <-- [c]}, and simplify, using \lemref{decomp (b <-- [c])}.
\end{proof}

\subsection{\thmref{LTrie}}\proofLabel{theorem:LTrie}

\workingHere

\begin{code}

    trieAt (a :< dp) + trieAt (b :< dq)
==  \ w -> trieAt (a :< dp) w + trieAt (b :< dq) w
==  ...
==  \ w -> case { [] -> a + b ; c:cs -> trieAt (dp ! c) cs + trieAt (dq ! c) cs }

    trieAt (dp ! c) cs + trieAt (dq ! c) cs
==  (trieAt (dp ! c) + trieAt (dq ! c)) cs
==  (trieAt ((dp ! c) + (dq ! c))) cs
==  trieAt ((dp + dq) ! c) cs

    ...
==  \ w -> case { [] -> a + b ; c:cs -> trieAt (dp ! c) cs + trieAt (dq ! c) cs }
==  \ w -> case { [] -> a + b ; c:cs -> trieAt ((dp + dq) ! c) cs }
==  trieAt (a + b  :<  dp + dq)

\end{code}

\note{Coinduction?}

\subsection{\thmref{LTrie'}}\proofLabel{theorem:LTrie'}

\bibliography{bib}

\end{document}
