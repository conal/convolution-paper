% -*- latex -*-

%let short = not long

%% Temporary title
\def\tit{Generalized Convolution and Efficient Language Recognition
%if long
(Extended version)
%endif
}

%% Used in bib.bib
%if anonymous
\newcommand\auth{Anonymous}
%else
\newcommand\auth{Conal Elliott}
%endif

%if icfp

\documentclass[acmsmall=true,screen
%,authorversion
%if anonymous
,anonymous,review
%endif
]{acmart}
%% \settopmatter{printfolios=true,printccs=false,printacmref=false}

\author{Conal Elliott}
\email{conal@@conal.net}
\affiliation{%
  \institution{Target}
  % \city{Sunnyvale}
  % \state{California}
  \country{USA}
}

\bibliographystyle{ACM-Reference-Format}

%% Copyright information
%% Supplied to authors (based on authors' rights management selection;
%% see authors.acm.org) by publisher for camera-ready submission;
%% use 'none' for review submission.
\setcopyright{rightsretained}

%else

%% While editing/previewing, use 12pt and tiny margin.
\documentclass[hidelinks,twoside]{article}  % fleqn,

%if anonymous
\usepackage[margin=1in]{geometry}  % 0.12in, 0.9in, 1in
%else
\usepackage[margin=1in]{geometry}  % 0.12in, 0.9in, 1in

%% \geometry{paperwidth=6.5in,paperheight=8in}  % for iPad portrait preview
%% \geometry{paperwidth=5.2in,paperheight=6.5in}  % same but easier on the eyes
%% \geometry{paperheight=9.3in} % for 2-up on big monitor, larger text
%% \geometry{paperwidth=10in} % 2-up big monitor, smaller text

%endif

\usepackage[square]{natbib}
\bibliographystyle{plainnat}

\author{\auth \\[1.5ex]
%if anonymous
(supplement to ICFP 2019 submission)
%else
Target\\[1.5ex]conal@@conal.net
%endif
}

%% TODO: experiment with the anonymous acmart option. See template.

\usepackage{fancyhdr}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[LO]\tit
\fancyhead[RE]{%
\auth
}
\fancyhead[LE,RO]{\thepage}
% \rnc{\headrulewidth}{0pt}

%endif

%include polycode.fmt
%include forall.fmt
%include greek.fmt
%include formatting.fmt

\input{macros}

%if long
\nc\iflong[1]{#1}
%else
\nc\iflong[1]{}
%endif

%if not draft
\rnc\indraft[1]{}
%endif

\calculationcomments

%% % author-date form
%% \usepackage[]{natbib}
%% \bibpunct();A{},
\let\cite=\citep

\title\tit
%if draft
\date{Draft of \today{} \currenttime}
%endif

\setlength{\blanklineskip}{2ex} % blank lines in code environment

%if short
\newcommand\citeLong{\citep{Elliott2019-convolution-extended}}
%endif

\nc\prooflabel[1]{\label{proof:#1}}
%if long
\nc\proofref[1]{Appendix \ref{proof:#1}}
\nc\seeproof[1]{(details in \proofref{#1})}
%else
\nc\proofref[1]{\citep[Appendix A]{Elliott2019-convolution-extended}}
\nc\seeproof[1]{\proofref{#1}}
%endif
\nc\provedIn[1]{\textnormal{Proved in \proofref{#1}}}

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

%if not icfp
\maketitle
%endif

%% %let otherApps = not icfp

%let otherApps = True

\begin{abstract}

\emph{Convolution} is a broadly useful operation with applications including signal processing, machine learning, probability, optics, polynomial multiplication, and efficient parsing.
Usually, however, this operation is understood and implemented in more specialized forms, hiding commonalities and limiting usefulness.
This paper formulates convolution in the common algebraic framework of semirings and semimodules and populates that framework with various representation types.
One of those types is the grand abstract template and itself generalizes to the free semimodule monad.
Other representations serve varied uses and performance trade-offs, with implementations calculated from simple and regular specifications.

Of particular interest is Brzozowski's method for regular expression matching.
Uncovering the method's essence frees it from syntactic manipulations, while generalizing from boolean to weighted membership (such as multisets and probability distributions) and from sets to \emph{n}-ary relations.
The classic \emph{trie} data structure then provides an elegant and efficient alternative to syntax.

Pleasantly, polynomial arithmetic requires no additional implementation effort, works correctly with a variety of representations, and handles multivariate polynomials and power series with ease.
Image convolution also falls out as a special case.

\end{abstract}

%if icfp
\maketitle
%endif

%format <+> = +
%format <.> = *
%format zero = 0
%format one = 1
%% %format zero = "\mathbf{0}"
%% %format one = "\mathbf{1}"

%% experiment
%% %format * = "\times"

%format `elem` = "\mathbin{`\Varid{elem}`}"
%format <# = "\mathbin{\in}"
%format # = "\mid"

%% Sometimes formatting breaks without an infix separator.
%format @@ = "{\,}"

%% Now I realize that the issue is parsing by lhs2tex. A better solution would
%% be to parenthesize the second argument to bigSum & friends, and have
%% formatting hide the parens. I'd like to make this change when I have time to
%% check the results carefully.

%format (paren (e)) = "\left(" e "\right)"

%format N = "\mathbb N"
%format Z = "\mathbb Z"
%format Pow = "\Pow"
%format emptyset = "\emptyset"
%% %format (single (s)) = "\single{"s"}"
%format (set (e)) = "\set{"e"}"
%format bigunion (lim) (body) = "\bigunion_{" lim "}{" body "}"
%format `union` = "\cup"
%format union = (`union`)
%format `intersect` = "\cap"
%format intersect = (`intersect`)
%format star p = "\closure{"p"}"

%format ^ = "^"
%% Handy alternative for complex exponent
%format pow a (b) = a "^{" b "}"

%format bigUnion (lim) = "\bigOp\bigcup{" lim "}{0}"
%format bigSum (lim) = "\bigOp\sum{" lim "}{0}"
%format bigSumQ (lim) = "\bigOp\sum{" lim "}{1}"
%format bigSumKeys (lim) = "\bigOp\sum{" lim "}{2.5}"

%format bigOr (lim) = "\bigOp\bigvee{" lim "}{0}"
%format bigOrQ (lim) = "\bigOp\bigvee{" lim "}{1.5}"
%format BR = "\!\!\\\!\!"
%% %format BR = "\hspace{-5mu}\\\hspace{-5mu}"

%format (inverse x) = x "^{-1}"

%format <-- = "\leftarrow"


\sectionl{Introduction}

The mathematical operation of \emph{convolution} combines two functions into a third---often written ``|h = f * g|''---with each |h| value resulting from summing or integrating over the products of several pairs of |f| and |g| values according to a simple rule.
This operation is at the heart of many important and interesting applications in a variety of fields \citep{SnehaHL2017Conv}.
\begin{itemize}
\item In image processing, convolution provides operations like blurring, sharpening, and edge detection \citep{Young95FIP}.
  \note{Add something about more general signal processing \citep[Chapter 2]{Yarlagadda2010ADSS}.}
\item In machine learning convolutional neural networks (CNNs) allowed recognition of translation-independent image features \citep{Fukushima1988Neo, LeCun1998GBDR, Schmidhuber2015DL}.
  % Alom2018History
\item In probability, the convolution of the distributions of two independent random variables yields the distribution of their sum \citep{Grinstead2003IP}.
\item In acoustics, reverberation results from convolving sounds and their echos \citep{Pishdadian2017FRC}.
      Musical uses are known as ``convolution reverb'' \citep[Chapter 4]{HassICM1}.
%\item In optics, blurring is convolution with a lens or iris, and shadowing is convolution with an occluding object.
\item The coefficients of the product of polynomials is the convolution of their coefficients \citep{Dolan2013FunSemi}.
\item In formal languages, (generalized) convolution is language concatenation \citep{Dongol2016CUC}.
\end{itemize}
Usually, however, convolution is taught, applied, and implemented in more specialized forms, obscuring the underlying commonalities and unnecessarily limiting its usefulness.
For instance,
\begin{itemize}
\item
  Standard definitions rely on subtraction (which is unavailable in many useful settings) and are dimension-specific, while the more general form applies to any monoid \citep{Golan2005RecentSemi,Wilding2015LAS}.
\item
  Brzozowski's method of regular expression matching \citep{Brzozowski64} appears quite unlike other applications and is limited to \emph{sets} of strings (i.e., languages), leaving unclear how to generalize to variations like weighted membership (multisets and probability distributions) as well as \emph{n}-ary \emph{relations} between strings.
\item
  Image convolution is usually tied to arrays and involves somewhat arbitrary semantic choices at image boundaries, including replication, zero-padding, and mirroring.
\notefoot{Not really a good example.}
\end{itemize}

\note{Rework the rest of this section for better coherence.}

This paper formulates general convolution in the algebraic framework of semirings and semimodules, including a collection of types for which semiring multiplication is convolution.
One of those types is the grand abstract template, namely the \emph{monoid semiring}, i.e., functions from any monoid to any semiring.
Furthermore, convolution reveals itself as a special case of an even more general notion---the \emph{free semimodule monad}.
The other types are specific representations for various uses and performance trade-offs, relating to the monoid semiring by simple denotation functions (interpretations).
The corresponding semiring implementations are calculated from the requirement that these denotations be semiring homomorphisms, thus guaranteeing that the computationally efficient representations are consistent with their mathematically simple and general template.

An application of central interest in this paper is language specification and recognition, in which convolution specializes to language concatenation.
Here, we examine a method by \citet{Brzozowski64} for flexible and efficient regular expression matching, later extended to parsing context-free languages \citep{Might2010YaccID}.
We will see that the essential technique is much more general, namely functions from lists to an arbitrary semiring.
While Brzozowski's method involves repeated manipulation of syntactic representations (regular expressions or grammars), uncovering the method's essence frees us from such representations.
Thue's tries provide a compelling alternative in simplicity and efficiency, as well as a satisfying confluence of classic techniques from the second and seventh decades of the twentieth century, as well as a modern functional programming notion: the cofree comonad.

Concretely, this paper makes the following contributions:
\notefoot{Maybe add section references.}
\begin{itemize}
\item Generalization of Brzozowski's algorithm from regular expressions representing sets of strings, to various representations of |[c] -> b| where |c| is any type and |b| is any semiring, including $n$-ary functions and relations on lists (via currying).
\item Demonstration that the subtle aspect of Brzozowski's algorithm (matching of concatenated languages) is an instance of generalized convolution.
\item Specialization of the generalized algorithm to tries (rather than regular expressions), yielding a simple and apparently quite efficient implementation, requiring no construction or manipulation of syntactic representations.
\item Observation that Brzozowski's key operations on languages generalize to the comonad operations of the standard function-from-monoid comonad and its various representations (including generalized regular expressions).
      The trie representation is the cofree comonad, which memoizes functions from the free monoid (lists).
\item Application and evaluation of a simple memoization strategy encapsulated in a familiar functor, resulting in dramatic speed improvement.
%if False
\item Demonstration of a few type specializations that yield correct arithmetic on univariate and multivariate polynomials and power series, requiring no additional implementation effort and working correctly with a variety of representations.
\item Image convolution as another special case, shining light on otherwise arbitrary border behavior.
%endif
\end{itemize}

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
The monoid laws require that |(<>)|\iflong{ (sometimes pronounced ``mappend'')} be associative and that |mempty|\iflong{ (``mempty'')} is its left and right identity, i.e.,
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
These two monoids are related via the function |length :: [a] -> N|, which not only maps lists to natural numbers, but does so in a way that preserves monoid structure%
%if short
.
%else
:
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
%endif
This pattern is common and useful enough to have a name \citep{Yorgey2012Monoids}:
\begin{definition}\deflabel{monoid homomorphism}
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
%if long
The identity and associativity monoid laws follow from the identity and associativity category laws, so we can generalize to endomorphisms, i.e., morphisms from an object to itself in any category.
%endif
A modest generalization of Cayley's theorem states that every monoid is isomorphic to a monoid of endofunctions \citep{Boisseau2018YNK}.
This embedding is useful for turning quadratic-time algorithms linear \citep{Hughes1986NRL,Voigtlander2008AIC}.
% (The Yoneda embedding generalizes this theorem to categories and endomorphisms.)
\twocol{0.45}{
\begin{code}
toEndo :: Monoid a => a -> Endo a
toEndo a = Endo (\ z -> a <> z)
\end{code}}{0.45}{
\begin{code}
fromEndo :: Monoid a => Endo a -> a
fromEndo (Endo f) = f mempty
\end{code}}
The |toEndo| embedding provides another example of a monoid homomorphism%
%if short
~\citeLong.
%else
:
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
%endif short

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
The |Additive| laws are the same as for |Monoid| (translating |mempty| and |(<>)| to |zero| and |(+)|), together with commutativity:
\begin{code}
(u + v) + w == u + (v + w)
zero + v == v
u + zero == u
u + v == v + u
\end{code}
Unlike lists with append, natural numbers form a \emph{additive} monoid.
Another example is functions with pointwise addition, with any domain and with any \emph{additive} codomain:
\begin{code}
instance Additive b => Additive (a -> b) where
  zero = \ a -> zero
  f + g  = \ a -> f a + g a
\end{code}

\noindent
Additive monoids have their form of homomorphism:
\begin{definition}\deflabel{additive monoid homomorphism}
A function |h| from one additive monoid to another is an \emph{additive monoid homomorphism} if it satisfies the following properties:
\begin{code}
h zero == zero
h (u + v) == h u + h v
\end{code}
\end{definition}
\noindent
Curried function types of \emph{any number} of arguments (and additive result type) are additive, thanks to repeated application of this instance.
In fact,
\begin{theorem}[\provedIn{theorem:curry additive}]\thmlabel{curry additive}
Currying and uncurrying are additive monoid homomorphisms.
\end{theorem}

\subsectionl{Semirings}

The natural numbers form a monoid in two familiar ways: addition and zero, and multiplication and one.
Moreover, these monoids interact usefully in two ways: multiplication distributes over addition, and multiplication by zero (the additive identity) yields zero (i.e., ``annihilates'').
Similarly, \emph{linear} endofunctions and their various representations (e.g., square matrices) forms a monoid via addition and via composition, with composition distributing over addition, and composition with zero yielding zero.
In both examples, addition commutes; but while natural number multiplication commutes, composition does not.
The vocabulary and laws these examples share is called a \emph{semiring} (distinguished from a ring by dropping the requirement of additive inverses):
\begin{code}
class Additive b => Semiring b where
  one    :: b
  (<.>)  :: b -> b -> b
  infixl 7 <.>
\end{code}
The laws, in addition to those for |Additive| above, include multiplicative monoid, distribution, and annihilation:
\twocol{0.25}{
\begin{code}
u * zero == zero
zero * v == zero
one * v == v
u * one == u
\end{code}}{0.35}{
\begin{code}
(u * v) * w == u * (v * w)

p * (q + r) == p * q + p * r
(p + q) * r == p * r + q * r
\end{code}}

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
A simpler example is the semiring of booleans, with disjunction as addition and conjunction as multiplication (though we could reverse roles):
\twocol{0.4}{
\begin{code}
instance Additive Bool where
  zero   = False
  (<+>)  = (||)
\end{code}}{0.4}{
\begin{code}
instance Semiring Bool where
  one    = True
  (<.>)  = (&&)
\end{code}}
An example of a semiring homomorphism is testing natural numbers for positivity%
%if short
~\citeLong.
%else
:
\begin{code}
positive :: N -> Bool
positive n = n > 0
\end{code}
As required, the following properties hold for |m,n :: N|:%
\footnote{\emph{Exercise:} What goes wrong if we replace natural numbers by integers?}
\begin{spacing}{1.2}
\begin{code}
positive zero  ==  False  == zero
positive one   ==  True   == one
positive (m  +  n) == positive m  ||  positive n == positive m  +  positive n
positive (m  *  n) == positive m  &&  positive n == positive m  *  positive n
\end{code}
%% \vspace{-4ex}
\end{spacing}

\noindent
%endif
There is a more fundamental example we will have use for later:
\begin{theorem}[\provedIn{theorem:curry semiring}]\thmlabel{curry semiring}
Currying and uncurrying are semiring homomorphisms.
\end{theorem}


\subsectionl{Star Semirings}

The semiring operations allow all \emph{finite} combinations of addition, zero, multiplication, and one.
It's often useful, however, to form infinite combinations, particularly in the form of Kleene's ``star'' (or ``closure'') operation:
\begin{code}
star p = bigSum i @@ p^i -- where |p^0 = one|, and |pow p (n+1) = p * p^n|.
\end{code}
Another characterization is as a solution to either of the following semiring equations:
\twocol{0.35}{
\begin{code}
star p == one + p * star p
\end{code}}{0.35}{
\begin{code}
star p == one + star p * p
\end{code}}
which we will take as a laws for a new abstraction, as well as a default recursive implementation:
\begin{code}
class Semiring b => StarSemiring b  where
  star :: b -> b
  star p = one <+> p * star p
\end{code}
Sometimes there are more appealing alternative implementations.
For instance, when subtraction and division are available, we can instead define |star p = inverse (one - p)| \citep{Dolan2013FunSemi}.

Predictably, there is a notion of homomorphisms for star semirings:
\begin{definition} \deflabel{star semiring homomorphism}
A function |h| from one star semiring to another is a \emph{star semiring homomorphism} if it is a semiring homomorphism (\defref{semiring homomorphism}) and satisfies the additional property |h (star p) = star (h p)|.
\end{definition}

\noindent
One simple example of a star semiring (also known as a ``closed semiring'' \citep{Lehmann77,Dolan2013FunSemi}) is booleans:
\begin{code}
instance StarSemiring Bool where star b  = one -- |== one |||| (b && star b)|
\end{code}

A useful property of star semirings is that recursive affine equations have solutions
%if short
\citep{Dolan2013FunSemi,Elliott2019-convolution-extended}:
%else
\citep{Dolan2013FunSemi}:
%endif
\begin{lemma}\lemlabel{affine over semiring}
In a star semiring, the affine equation |p = b + m * p| has solution |p = star m * b|.
\end{lemma}
%if long
\begin{proof}~
\begin{code}
    b + m * (star m * b)
==  b + (m * star m) * b      -- associativity of |(*)|
==  one * b + m * star m * b  -- identity for |(*)|
==  (one + m * star m) * b    -- distributivity
==  star m * b                -- star semiring law
\end{code}
\end{proof}
%endif

\note{Mention tropical semirings, schedule algebra (max-plus), and optimization algebra (min-plus) \citep{Golan2005RecentSemi}. Maybe also polynomials.}

\subsectionl{Semimodules}

\note{I think I can remove semimodules from the discussion and use |fmap (s NOP *)| in place of |(scale s)|.
If so, do it.
One serious catch, however: when I introduce |b <-- a|, I'll no longer have a functor in |a|.}

%format .> = "\cdot"

%% Temporary deception. Later change scale's formatting back to the usual,
%% and introduce (.>).

As fields are to vector spaces, rings are to modules, and semirings are to \emph{semimodules}.
For any semiring |s|, a \emph{left |s|-semimodule} |b| is a additive monoid whose values can be multiplied by |s| values on the left.
Here, |s| plays the role of ``scalars'', while |b| plays the role of ``vectors''.
\notefoot{Perhaps say just ``semimodule'', and add a remark that I really mean ``left semimodule'' throughout.
Or start out with ``left'', then make the remark, and then perhaps add an occasional ``(left)''.}
\begin{code}
class (Semiring s, Additive b) => LeftSemimodule s b | b -> s where
  (.>) :: s -> b -> b
\end{code}
In addition to the laws for the additive monoid |b| and the semiring |s|, we have the following laws specific to left semimodules: \citep{Golan2005RecentSemi}:
\twocol{0.35}{
\begin{code}
(s * t) .> b == s .> (t .> b)
(s + t) .> b == s .> b + t .> b
s .> (b + c) == s .> b + s .> c
\end{code}
}{0.25}{
\begin{code}
one   .> b == b
zero  .> b == zero
\end{code}}
%if long
There is also a corresponding notion of \emph{right} |s|-semimodule (with multiplication on the right by |s| values), which we will not need in this paper.
(Rings also have left- and right-modules, and in \emph{commutative} rings and semirings (including vector spaces), the left and right variants coincide.)
%endif

As usual, we have a corresponding notion of homomorphism, which is more commonly referred to as ``linearity'':
\begin{definition} \deflabel{left semimodule homomorphism}
A function |h| from one left |s|-semimodule to another is a \emph{left |s|-semimodule homomorphism} if it is an additive monoid homomorphism (\defref{additive monoid homomorphism}) and satisfies the additional property |h (s .> b) == s .> h b|.
\end{definition}

Familiar |s|-semimodule examples include various containers of |s| values, including single- or multi-dimensional arrays, lists, infinite streams, sets, multisets, and trees.
Another, of particular interest in this paper, is functions from any type to any semiring:
\begin{code}
instance LeftSemimodule s (a -> s) where s .> f = \ a -> s * f a
\end{code}
If we think of |a -> s| as a ``vector'' of |s| values, indexed by |a|, then |s .> f| scales each component of the vector |f| by |s|.

%format `scale` = "\mathbin{\hat{".>"}}"
%format scale = "("`scale`")"
There is an important optimization to be made for scaling.
When |s == zero|, |s .> p == zero|, so we can discard |p| entirely.
This optimization applies quite often in practice, for instance with languages, which tend to be sparse.
Another optimization (though less dramatically helpful) is |one .> p == p|.
Rather than burden each |LeftSemimodule| instance with these two optimizations, let's define |(.>)| via a more primitive |scale| method:
%% Shorten the names for the code examples in the paper
%format DetectableZero = IsZero
%format DetectableOne  = IsOne
\begin{code}
class (Semiring s, Additive b) => LeftSemimodule s b | b -> s where
  scale :: s -> b -> b

infixr 7 .>
(.>) :: (Additive b, LeftSemimodule s b, DetectableZero s, DetectableOne s) => s -> b -> b
s .> b  | isZero s   = zero
        | isOne  s   = b
        | otherwise  = s `scale` b
\end{code}
The |DetectableZero| and |DetectableOne| classes:
\notefoot{Maybe use semiring-num again.}
\begin{code}
class Additive  b => DetectableZero  b where isZero  :: b -> Bool
class Semiring  b => DetectableOne   b where isOne   :: b -> Bool
\end{code}

As with star semirings (\lemref{affine over semiring}), recursive affine equations in semimodules \emph{over} star semirings also have solutions%
%if short
~\citeLong.
%else
:
%endif
\begin{lemma}\lemlabel{affine over semimodule}
In a left semimodule over a star semiring, the affine equation |p == b <+> m .> p| has solution |p = star m .> b|%
\end{lemma}
%if long
The proof closely resembles that of \lemref{affine over semiring}, using the left semimodule laws above:
\begin{proof}~
\begin{code}
    star s .> r
==  (one <+> s <.> star s) .> r         -- star semiring law
==  one .> r <+> (s <.> star s) .> r    -- distributivity
==  r <+> s .> (star s .> r)            -- multiplicative identity and associativity
\end{code}
\vspace{-4ex}
\end{proof}
%endif

\subsectionl{Function-like Types and Singletons}

Most of the representations used in this paper behave like functions, and it will be useful to use a standard vocabulary.
An ``indexable'' type |x| with domain |a| and codomain |b| represents |a -> b|:
Sometimes we will need to restrict |a| or |b|.
\begin{code}
class Indexable a b x | x -> a b where
  infixl 9 !
  (!) :: x -> a -> b

instance Indexable a b (a -> b) where
  f ! k = f k
\end{code}

\note{Add a law for |Indexable|: |(!)| must be natural?
Probably also that |h| maps |Additive| to |Additive| and that |(!)| is an |Additive| homomorphism.
Hm. It seems I can't even express those laws now that there's no functor.
}

\secrefs{Monoids}{Semimodules} provides a fair amount of vocabulary for combining values.
We'll also want an operation that constructs a ``vector'' (e.g., language or function) with a single nonzero component:
%format +-> = "\mapsto"
\begin{code}
class Indexable a b x => HasSingle a b x where
  infixr 2 +->
  (+->) :: a -> b -> x

instance (Eq a, Additive b) => HasSingle a b (a -> b) where
  a +-> b = \ a' -> if a == a' then b else zero
\end{code}
Two specializations of |a +-> b| will come in handy: one for |a = mempty|, and the other for |b = one|.
\begin{code}
single :: (HasSingle a b x, Semiring b) => a -> x
single a = a +-> one

value :: (HasSingle a b x, Monoid a) => b -> x
value b = mempty +-> b
\end{code}
In particular, |mempty +-> one == single mempty == value one|.

The |(+->)| operation gives a way to decompose arbitrary functions:
\begin{lemma}[\provedIn{lemma:decomp +->}]\lemlabel{decomp +->}
For all |f :: a -> b| where |b| is an additive monoid,
\begin{code}
f == bigSum a a +-> f a
\end{code}
\vspace{-3ex}
\end{lemma}
\noindent
For the uses in this paper, |f| is often ``sparse'', i.e., nonzero on a relatively small (e.g., finite or at least countable) subset of its domain.

Singletons also curry handily and provide another useful homomorphism:
\begin{lemma}[\provedIn{lemma:curry +->}]\lemlabel{curry +->}~
\begin{code}
(a +-> b +-> c) == curry ((a,b) +-> c)
\end{code}
\vspace{-4ex}
\end{lemma}
\begin{lemma} \lemlabel{+-> homomorphism}
For |(->) a|, partial applications |(a +->)| are left semi-module (and hence additive) homomorphisms.
Moreover, |single == (mempty +->)| is a semiring homomorphism.
\end{lemma}
\begin{proof}
Straightforward from the definition of |(+->)|.
\end{proof}

%if False
Just as we defined |single b = mempty +-> b|, we can sometimes also define |(+->)| via |single|:
\begin{lemma}\lemlabel{(+->) via single}
In a semimodule, |a +-> b == b .> single a|.
\end{lemma}
\begin{proof}
Immediate from the definitions of |(+->)| and |(.>)|.
\end{proof}
%endif

\sectionl{Calculating Instances from Homomorphisms}

So far, we've started with instance definitions and then noted and proved homomorphisms where they arise.
We can instead invert the process, taking homomorphisms as specifications and \emph{calculating} instance definitions that satisfy them.
This process of calculating instances from homomorphisms is the central guiding principle of this paper, so let's see how it works.

Consider a type ``|Pow a|'' of mathematical \emph{sets} of values of some type |a|.
Are there useful instances of the abstractions from \secref{Monoids, Semirings and Semimodules} for sets?
Rather than guessing at such instances and then trying to prove the required laws, let's consider how sets are related to a type for which we already know instances, namely functions.

Sets are closely related to functions-to-booleans (``predicates''):
%format setPred = pred
%% doesn't work
%format predSet = inverse setPred
%format predSet = setPred "^{-1}"
\twocol{0.4}{
\begin{code}
setPred :: Pow a -> (a -> Bool)
setPred as = \ a -> a <# as
\end{code}}{0.4}{
\begin{code}
predSet :: (a -> Bool) -> Pow a
predSet f = set (a | f a)
\end{code}}
This pair of functions forms an isomorphism, i.e., |predSet . setPred == id| and |setPred . predSet == id|, as can be checked by inlining definitions and simplifying.
Moreover, for sets |p| and |q|, |p == q <=> setPred p == setPred q|, by the \emph{extensionality} axiom of sets and of functions.
Now let's also require that |setPred| be an \emph{additive monoid homomorphism}.
The required homomorphism properties:
\begin{spacing}{1.2}
\begin{code}
setPred zero == zero
setPred (p + q) == setPred p + setPred q
\end{code}
\end{spacing}\noindent
We already know definitions of |setPred| as well as the function versions of |zero| and |(+)| (on the RHS) but not yet the set versions of |zero| and |(+)| (on the LHS).
We thus have two algebra problems in two unknowns.
Since only one unknown appears in each homomorphism equation, we can solve them independently.
The |setPred|/|predSet| isomorphism makes it easy to solve these equations, and removes all semantic choice, allowing only varying implementations of the same meaning.
\begin{code}
     setPred zero == zero
<=>  predSet (setPred zero) == predSet zero                        -- |predSet| injectivity
<=>  zero == predSet zero                                          -- |predSet . setPred == id|

     setPred (p + q) == setPred p + setPred q
<=>  predSet (setPred (p + q)) == predSet (setPred p + setPred q)  -- |predSet| injectivity
<=>  p + q == predSet (setPred p + setPred q)                      -- |predSet . setPred == id|
\end{code}
We thus have sufficient (and in this case semantically necessary) definitions for |zero| and |(+)| on sets.
Now let's simplify to get more direct definitions:
\begin{code}
    predSet zero
==  predSet (\ a -> zero)                        -- |zero| on functions
==  predSet (\ a -> False)                       -- |zero| on |Bool|
==  set (a # False)                              -- |predSet| definition
==  emptyset

    predSet (setPred p + setPred q)
==  predSet ((\ a -> a <# p) + (\ a -> a <# q))  -- |setPred| definition (twice)
==  predSet (\ a -> (a <# p) + (a <# q))         -- |(+)| on functions
==  predSet (\ a -> a <# p || a <# q)            -- |(+)| on |Bool|
==  set (a # a <# p || a <# q)                   -- |predSet| definition
==  p `union` q                                  -- |union| definition
\end{code}
Without applying any real creativity, we have discovered the desired |Semiring| instance for sets:
\begin{code}
instance Additive (Pow a) where
  zero  = emptyset
  (+)   = union
\end{code}

Next consider a |LeftSemimodule| instance for sets.
We might be tempted to define |s .> p| to multiply |s| by each value in |p|, i.e.,
\begin{code}
instance LeftSemimodule s (Pow s) where s `scale` p = set (s * x | x <# p)    -- \emph{wrong}
\end{code}
This definition, however, would violate the semimodule law that |zero .> p == zero|, since |zero .> p| would be |set zero|, but |zero| for sets is |emptyset|.
Both semimodule distributive laws fail as well.
There is an alternative choice, necessitated by requiring that |predSet| be a left |Bool|-semimodule homomorphism.
The choice of |Bool| is inevitable from the type of |predSet| and the fact that |a -> b| is a |b|-semimodule for all semirings |b|, so |a -> Bool| is a |Bool|-semimodule.
The necessary homomorphism property:
\begin{code}
setPred (s .> p) == s .> setPred p
\end{code}
%if short
Equivalently \citeLong,
%else
Equivalently,
\begin{spacing}{1.2}
\vspace{-1ex}
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
\end{spacing}
\noindent
Summarizing,
%endif
\begin{code}
instance LeftSemimodule Bool (Pow a) where
  s `scale` p = if s then p else zero
\end{code}
While perhaps obscure at first, this alternative will prove useful later on.

Note that the left |s|-semimodule laws specialized to |s=Bool| require |True| (|one|) to preserve and |False| (|zero|) to annihilate the second |(.>)| argument.
\emph{Every} left |Bool|-semimodule instance must therefore agree with this definition.
\out{Also note that |forall a. (a <# s .> p) <=> (s && a <# p)|, which resembles the |LeftSemimodule (a -> b)| instance given above.}

\note{Demonstrate that homomorphic specifications also guarantee that laws hold, assuming that equality is consistent with homomorphism.}

\sectionl{Languages and the Monoid Semiring}

A \emph{language} is a set of strings over some alphabet, so the |Additive| and |LeftSemimodule| instances for sets given above apply directly.
Conspicuously missing, however, are the usual notions of language concatenation and closure (Kleene star), which are defined as follows for languages |U| and |V|:
\begin{code}
U V = set (u <> v | u <# U && v <# V)

star U = bigUnion i @@ U^i -- where |U^0 = one|, and |pow U (n+1) = U @@ U^n|.
\end{code}
Intriguingly, this |star U| definition would satisfy the |StarSemiring| laws if |(*)| were language concatenation.
A bit of reasoning shows that all of the semiring laws would hold as well:
\begin{itemize}
\item Concatenation is associative and has as identity the language |set mempty|.
\item Concatenation distributes over union, both from the left and from the right.
\item The |zero| (empty) language annihilates (yields |zero|) under concatenation, both from the left and from the right.
\end{itemize}
All we needed from strings is that they form a monoid, so we may as well generalize:
\begin{code}
instance Monoid a => Semiring (P a) where
  one = set mempty -- |== mempty +-> one == single mempty == value one| (\secref{Function-like Types and Singletons})
  p * q = set (u <> v # u <# p && v <# q)

instance StarSemiring (Pow a) -- use default |star| definition (\secref{Star Semirings}).
\end{code}

\noindent
These new instances indeed satisfy the laws for additive monoids, semimodules, semirings, and star semirings.
They seem to spring from nothing, however, which is disappointing compared with the way the |Additive| and |LeftSemimodule| instances for sets follow inevitably from the requirement that |setPred| be a homomorphism for those classes (\secref{Calculating Instances from Homomorphisms}).
Let's not give up yet, however.
Perhaps there's a |Semiring| instance for |a -> b| that specializes with |b = Bool| to bear the same relationship to |Pow a| that the |Additive| and |LeftSemimodule| instances bear.
The least imaginative thing we can try is to require that |setPred| be a \emph{semiring} homomorphism.
If we apply the same sort of reasoning as in \secref{Calculating Instances from Homomorphisms} and then generalize from |Bool| to an arbitrary semiring, we get the definitions in \figrefdef{monoid semiring}{The monoid semiring}{
\begin{code}
instance (Semiring b, Monoid a) => Semiring (a -> b) where
  one = single mempty
  f * g  = bigSum (u,v) u <> v +-> f u <.> g v
         = \ w -> bigSumQ (u,v BR u <> v == w) f u <.> g v

instance (Semiring b, Monoid a)  => StarSemiring (a -> b)  -- default |star|
\end{code}
\vspace{-4ex}
}.
With this instance, |a -> b| type is known as the \emph{monoid semiring}, and its |(*)| operation as \emph{convolution} \citep{Golan2005RecentSemi,Wilding2015LAS}.

\begin{theorem}[\provedIn{theorem:semiring hom ->}]\thmlabel{semiring hom ->}
Given the instance definitions in \figref{monoid semiring}, |setPred| is a star semiring homomorphism.
\end{theorem}

%% %format splits = split
For some monoids, we can also express the product operation in a more clearly computable form via \emph{splittings}:
%format bigSumSplits (lim) = "\bigOp\sum{" lim "}{2.5}"
\begin{code}
  f <.> g = \ w -> bigSumSplits ((u,v) <# splits w) f u * g v
\end{code}
where |splits w| yields all pairs |(u,v)| such that |u <> v == w|:
% \notefoot{Maybe generalize from \emph{lists} of pairs to an associated |Foldable|.}
\begin{code}
class Monoid t => Splittable t where
  splits   :: t -> [(t,t)]  -- multi-valued inverse of |mappend|
\end{code}
Examples of splittable monoids include natural numbers and lists%
%if short
~\citeLong.
%else
:
\begin{code}
instance Splittable N where
  splits n = [(i, n-i) | i <- [0 .. n]]

instance Splittable [c] where
  splits []      = [([],[])]
  splits (c:cs)  = ([],c:cs) : [((c:l),r) | (l,r) <- splits cs]
\end{code}
%endif

While simple, general, and (assuming |Splittable| domain) computable, the definitions of |(<+>)| and |(<.>)| above for the monoid semiring make for quite inefficient implementations, primarily due to naive backtracking.
As a simple example, consider the language |single "pickles" + single "pickled"|, and suppose that we want to test the word ``pickling'' for membership.
The |(<+>)| definition from \secref{Additive Monoids} will first try ``pickles'', fail near the end, and then backtrack all the way to the beginning to try ``pickled''.
The second attempt redundantly discovers that the prefix ``pickl'' is also a prefix of the candidate word and that ``pickle'' is not.
Next consider the language |single "ca" <.> single "ts" <.> single "up"|, and suppose we want to test ``catsup'' for membership.
The |(<.>)| implementation above will try all possible three-way splittings of the test string.


\sectionl{Finite maps}

%% Tighten spacing after ``M'' in ``M.''
%format Mdot = M"\!."
%format M.keys = Mdot keys
%format M.findWithDefault = Mdot findWithDefault
%format M.singleton = Mdot singleton
%format M.unionWith = Mdot unionWith
%format M.empty = Mdot empty
%format M.null = Mdot null

\note{I don't think finite maps need their own section. Look for another home. Maybe with |Cofree| as a suggested functor.}

One representation of \emph{partial} functions is the type of finite maps, |Map a b| from keys of type |a| to values of type |b|, represented is a key-ordered balanced tree \citep{Adams1993Sets,Straka2012ATR,Nievergelt1973BST}.
To model \emph{total} functions instead, we can treat unassigned keys as denoting zero.
Conversely, merging two finite maps can yield a key collision, which can be resolved by addition.
Both interpretations require |b| to be an additive monoid.
Given the definitions in \figrefdef{Map}{Finite maps}{
\begin{code}
instance (Ord a, Additive b) => Indexable a b (Map a b) where
  m ! a = M.findWithDefault zero a m

instance (Ord a, Additive b) => HasSingle a b (Map a b) where
  (+->) = M.singleton

instance (Ord a, Additive b) => Additive (Map a b) where
  zero = M.empty
  (<+>) = M.unionWith (<+>)

instance (Ord a, Additive b) => DetectableZero (Map a b) where isZero = M.null

instance Semiring b => LeftSemimodule b (Map a b) where
  scale b = fmap (b NOP <.>)

instance (Ord a, Monoid a, Semiring b) => Semiring (Map a b) where
  one = mempty +-> one
  p <.> q = sum [u <> v +-> p!u <.> q!v | u <- M.keys p, v <- M.keys q]
\end{code}
\vspace{-4ex}
}, |(!)| is a homomorphism with respect to each instantiated class.
(The ``|M|.'' module qualifier indicates names coming from the finite map library \citep{Data.Map}.)
\notefoot{Do I want a theorem and proof here?
I think so, though I'll have to make a few assumptions about finite maps.
On the other hand, those assumptions don't differ much from the homomorphism properties I'm claiming to hold.}
The finiteness of finite maps prevents giving a useful |StarSemiring| instance.


\sectionl{Decomposing Functions from Lists}

%format <: = "\mathrel{\blacktriangleleft}"
%format <: = "\mathrel\triangleleft"
%format atEps = "\Varid{at}_\epsilon"
%format deriv = "\derivOp"

For functions from \emph{lists} specifically, we can decompose in a way that lays the groundwork for more efficient implementations than the ones in previous sections.
\begin{lemma}[\provedIn{lemma:decomp ([c] -> b)}]\lemlabel{decomp ([c] -> b)}
Any |f :: [c] -> b| can be decomposed as follows:
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
atEps :: ([c] -> b) -> b
atEps f = f mempty

deriv :: ([c] -> b) -> c -> ([c] -> b)
deriv f = \ c cs -> f (c:cs)

infix 1 <:
(<:) :: b -> (c -> ([c] -> b)) -> ([c] -> b)
b <: h = \ NOP case {NOP [] -> b NOP;NOP c:cs  -> h c cs NOP}
\end{code}
\vspace{-4ex}
\end{lemma}
\noindent
%format derivs = deriv "^{\ast}"
%format derivs' (w) = derivs "_{" w "}"
Considering the isomorphism |Pow [c] =~ [c] -> Bool|, this decomposition generalizes the |delta| and |deriv| operations used by \citet{Brzozowski64} mapping languages to languages (as sets of strings), the latter of which he referred to as the ``derivative''.\footnote{Brzozowski wrote ``|derivs' c p|'' instead of ``|deriv p c|'', but the latter will prove more convenient below.}
Brzozowski used differentiation with respect to single symbols to implement a more general form of language differentiation with respect to a \emph{string} of symbols, where the \emph{derivative} |derivs u p| of a language |p| with respect to a prefix string |u| is the set of |u|-suffixes of strings in |p|, i.e.,

> derivs p u = set (v | u <> v <# p)

so that

> u <# p <=> mempty <# derivs p u

Further, he noted that%
%if long
\footnote{Here, Brzozowski's notation makes for a prettier formulation:
\begin{code}
derivs' mempty p    == p
derivs' (u <> v) p  == derivs' v (derivs' u p)
\end{code}
Equivalently,
\begin{code}
derivs' mempty    == id
derivs' (u <> v)  == derivs' v . derivs' u
\end{code}
where |id| is the identity function.
In other words, |derivs'| is a contravariant monoid homomorphism (targeting the monoid of endofunctions).}
%endif long
\begin{code}
derivs p mempty    == p
derivs p (u <> v)  == derivs (derivs p u) v
\end{code}
Thanks to this decomposition property and the fact that |deriv p c == derivs p [c]|, one can successively differentiate with respect to single symbols.

Generalizing from sets to functions,
\begin{code}
derivs f u = \ v -> f (u <> v)
\end{code}
so that
\begin{code}
f  == \ u -> derivs f u mempty
   == \ u -> atEps (derivs f u)
   == atEps . derivs f
   == atEps . foldl deriv f
\end{code}
where |foldl| is the usual left fold on lists:
\notefoot{The choice of \emph{left} fold bothers me. Could we define |derivs| via a \emph{right} fold (the natural fold for lists), perhaps leading to a right-to-left string matching algorithm? Or maybe left vs right doesn't matter?}
\begin{code}
foldl :: (c -> b -> b) -> b -> [c] -> b
foldl h e []      = e
foldl h e (c:cs)  = foldl h (h e c) cs
\end{code}
Intriguingly, |atEps| and |derivs| correspond to |coreturn| and |cojoin| for the function-from-monoid comonad, also called the ``exponent comonad'' \citep{Uustalu2008CNC}.

Understanding how |atEps| and |deriv| relate to the semiring vocabulary will help us develop efficient implementations in later sections.

\begin{lemma}[\provedIn{lemma:atEps [c] -> b}]\lemlabel{atEps [c] -> b}
The |atEps| function is a star semiring and left semimodule homomorphism, i.e.,
\begin{spacing}{1.3}
\begin{code}
atEps zero         == zero
atEps one          == one
atEps (p  <+>  q)  == atEps p  <+>  atEps q 
atEps (p  <.>  q)  == atEps p  <.>  atEps q 
atEps (star p)     == star (atEps p)
\end{code}
\end{spacing}
\noindent
Moreover,\footnote{Mathematically, the |(.>)| equation says that |atEps| is a left |b|-semiring homomorphism as well, since every semiring is a (left and right) semimodule over itself.
Likewise, the |(+->)| equation might be written as ``|null w +-> b|'' or even ``|atEps w +-> b|''.
Unfortunately, these prettier formulations would lead to ambiguity during Haskell type inference.}
\begin{spacing}{1.3}
\begin{code}
atEps (s .> p)   == s * atEps p

atEps (   []     +-> b) == b
atEps (c  :  cs  +-> b) == zero
\end{code}
\end{spacing}
\vspace{-2ex}
\noindent
\end{lemma}
\begin{lemma}[\provedIn{lemma:deriv [c] -> b}, generalizing Lemma 3.1 of \citet{Brzozowski64}]\lemlabel{deriv [c] -> b}
Differentiation has the following properties:
\notefoot{If I replace application to |c| by indexing by |c| (i.e., |(! NOP c)|), will this lemma hold for all of the representations? I suspect so. Idea: Define $\derivOp_c\,p = \derivOp\,p\:!\:c$.}
\begin{spacing}{1.3}
\begin{code}
deriv zero   c       == zero
deriv one    c       == zero
deriv (p  <+>  q) c  == deriv p c <+> deriv q c
deriv (p  <.>  q) c  == atEps p .> deriv q c <+> deriv p c <.> q
deriv (star p) c     == star (atEps p) .> deriv p c * star p
deriv (s .> p) c     == s .> deriv p c

deriv (     []      +-> b) == \ c -> zero
deriv (c'   :  cs'  +-> b) == c' +-> cs' +-> b
\end{code}
\end{spacing}
\vspace{-2ex}
\end{lemma}
Although |deriv p| is defined as a \emph{function} from leading symbols, it could instead be another representation with function-like semantics, such as as |h b| for an appropriate functor |h|.
To relate |h| to the choice of alphabet |c|, introduce a type family:
\begin{code}
type family Key (h :: Type -> Type) :: Type

type instance Key ((->)  a) = a
type instance Key (Map   a) = a
\end{code}
Generalizing in this way (with functions as a special case) enables convenient memoization, which has been found to be quite useful in practice for derivative-based parsing \citep{Might2010YaccID}.
A few generalizations to the equations in \lemref{deriv [c] -> b} suffice to generalize from |c -> ([c] -> b)| to |h ([c] -> b)| \seeproof{lemma:deriv [c] -> b}.
We must assume that |Key h = c| and that |h| is an ``additive functor'', i.e., |forall b. Additive b => Additive (h b)| with |(!)| for |h| being an additive monoid homomorphism.
%if long
\begin{spacing}{1.3}
\begin{code}
deriv zero         == zero
deriv one          == zero
deriv (p  <+>  q)  == deriv p <+> deriv q
deriv (p  <.>  q)  == fmap (atEps p NOP .>) (deriv q) <+> fmap (<.> q) (deriv p)
deriv (star p)     == fmap (\ d -> star (atEps p) .> d <.> Star p) (deriv p)
deriv (s .> p)     == fmap (s NOP .>) (deriv p)
\end{code}
\vspace{-4ex}
\end{spacing}
%endif

\note{Consider reexpressing \lemref{deriv [c] -> b} in terms of |(!)|. Maybe even generalize |(<:)| to indexable functors.}

\begin{theorem}[\provedIn{theorem:semiring decomp [c] -> b}]\thmlabel{semiring decomp [c] -> b}
The following properties hold (in the generalized setting of a functor |h| with |Key h == c|):
\begin{spacing}{1.4}
\begin{code}
zero  == zero  <: zero
one   == one   <: zero
(a  <:  dp) <+> (b <: dq)  == a  <+>  b <: dp <+> dq
(a  <:  dp) <.> q == a .> q <+> (zero <: fmap (<.> NOP q) dp)
star (a <: dp) = q where q = star a .> (one <: fmap (<.> NOP q) dp)
s .> (a <: dp) = s <.> a <: fmap (s NOP .>) dp
w +-> b = foldr (\ c t -> zero <: c +-> t) (b <: zero) w
\end{code}
\vspace{-6ex}
\end{spacing}
\end{theorem}

\sectionl{Regular Expressions}

\lemreftwo{atEps [c] -> b}{deriv [c] -> b} generalize and were inspired by a technique of \citet{Brzozowski64} for recognizing regular languages.
\figrefdef{RegExp}{Semiring-generalized regular expressions denoting |[c] -> b|}{
%format :<+> = "\mathbin{:\!\!+}"
%format :<.> = "\mathbin{:\!\!\conv}"
%format D0 = DetectableZero
%format D1 = DetectableOne
\begin{code}
data RegExp h b           =  Char (Key h)
                          |  Value b
                          |  RegExp h b  :<+>  RegExp h b
                          |  RegExp h b  :<.>  RegExp h b
                          |  Star (RegExp h b)
  deriving Functor

instance Additive b => Additive (RegExp h b) where
  zero = Value zero
  (<+>) = (:<+>)

instance Semiring b => Semiring (RegExp h b) where
  scale b = fmap (b NOP <.>)

instance Semiring b => Semiring (RegExp h b) where
  one = Value one
  (<.>) = (:<.>)

instance Semiring b => StarSemiring (RegExp h b) where
  star e = Star e

type FR h b =  (  HasSingle (Key h) (RegExp h b) (h (RegExp h b))
               ,  Additive (h (RegExp h b)), Functor h, DetectableZero b, DetectableOne b )

instance (FR h b, StarSemiring b, c ~ Key h, Eq c) => Indexable [c] b (RegExp h b) where
  e ! w = atEps (foldl ((!) . deriv) e w)

instance (FR h b, StarSemiring b, c ~ Key h, Eq c) => HasSingle [c] b (RegExp h b) where
  w +-> b = b .> product (map Char w)

atEps :: StarSemiring b => RegExp h b -> b
atEps (Char _)       = zero
atEps (Value b)      = b
atEps (p  :<+>  q)   = atEps p <+> atEps q
atEps (p  :<.>  q)   = atEps p <.> atEps q
atEps (Star p)       = star (atEps p)

deriv :: (FR h b, StarSemiring b) => RegExp h b -> h (RegExp h b)
deriv  (Char c)       = single c
deriv  (Value _)      = zero
deriv  (p  :<+>  q)   = deriv p <+> deriv q
deriv  (p :<.> q)     = fmap (atEps p NOP .>) (deriv q) <+> fmap (<.> NOP q) (deriv p)
deriv  (Star p)       = fmap (\ d -> star (atEps p) .> d <.> Star p) (deriv p)

\end{code}
\vspace{-4ex}
} generalizes regular expressions in the same way that |a -> b| generalizes |Pow a|, to yield a value of type |b| (a star semiring).
The constructor |Value b| generalizes |zero| and |one| to yield a semiring value.
\begin{theorem}\thmlabel{RegExp}
Given the definitions in \figref{RegExp}, |(!)| is a homomorphism with respect to each instantiated class.
\end{theorem}
The implementation in \figref{RegExp} generalizes the regular expression matching algorithm of \citet{Brzozowski64}, adding customizable memoization, depending on choice of the indexable functor |h|.
Note that the definition of |e ! w| is exactly |atEps (derivs e w)| generalized to indexable |h|, performing syntactic differentiation with respect to successive characters in |w| and applying |atEps| to the final resulting regular expression.

For efficiency, and sometimes even termination (with recursively defined languages), we will need to add some optimizations to the |Additive| and |Semiring| instances for |RegExp| in \figref{RegExp}:
\twocol{0.4}{
\begin{code}
  p <+> q  | isZero p   = q
           | isZero q   = p
           | otherwise  = p :<+> q
\end{code}}{0.45}{
\begin{code}
  p <.> q  | isZero p   = zero
           | isOne  p   = q
           | otherwise  = p :<.> q
\end{code}}
For |p <.> q|, we might also check whether |q| is |zero| or |one|, but doing so itself leads to non-termination in right-recursive grammars.

As an alternative to repeated syntactic differentiation, we can reinterpret the original (syntactic) regular expression in another semiring as follows:
\begin{code}
regexp :: (StarSemiring x, HasSingle [Key h] b x, Semiring b) => RegExp h b -> x
regexp (Char c)      = single [c]
regexp (Value b)     = value b
regexp (u  :<+>  v)  = regexp u  <+>  regexp v
regexp (u  :<.>  v)  = regexp u  <.>  regexp v
regexp (Star u)      = star (regexp u)
\end{code}
Next, we will see a choice of |f| that eliminates the syntactic overhead.


\sectionl{Tries}

\secref{Languages and the Monoid Semiring} provided an implementation of language recognition and its generalization to the monoid semiring (|a -> b| for monoid |a| and semiring |b|), packaged as instances of a few common algebraic abstractions (|Additive|, |Semiring| etc).
While simple and correct, these implementations are quite inefficient, primarily due to naive backtracking and redundant comparison.
\secref{Decomposing Functions from Lists} explored the nature of functions on lists, identifying a decomposition principle and its relationship to the vocabulary of semirings and related algebraic abstractions.
Applying this principle to a generalized form of regular expressions led to Brzozowski's algorithm, generalized from sets to functions in \secref{Regular Expressions}, providing an alternative to naive backtracking but still involving repeated syntactic manipulation as each candidate string is matched.
Nevertheless, with some syntactic optimizations and memoization, recognition speed with this technique can be fairly good \citep{Might2010YaccID,Adams2016CPP}.

As an alternative to regular expression differentiation, note that the problem of redundant comparison is solved elegantly by the classic trie (``prefix tree'') data structure introduced by Thue in 1912 \citep[Section 6.3]{Knuth1998ACP3}.
This data structure was later generalized to arbitrary (regular) algebraic data types \citep{Connelly1995GenTrie} and then from sets to functions \citep{Hinze2000GGT}.
\out{We'll explore the data type generalization later.\notefoot{Add a forward pointer, or remove the promise.}}
Restricting our attention to functions of \emph{lists} (``strings'' over some alphabet), we can formulate a simple trie data type along the lines of |(<:)| from \secref{Decomposing Functions from Lists}, with an entry for |mempty| and a sub-trie for each possible character:
%format :< = "\mathrel{\Varid{:\!\!\triangleleft}}"
\begin{code}
data LTrie c b = b :< c -> LTrie c b  -- first guess
\end{code}
While this definition would work, we can get much better efficiency if we memoize the functions of |c|, e.g., as a generalized trie or a finite map.
Rather than commit to a particular representation for subtrie collections, let's replace the type parameter |c| with a functor |h| whose associated key type is |c|.
The functor-parametrized list trie is also known as the ``cofree comonad'' \citep{Uustalu2005EDP,Uustalu2008CNC,Uustalu2011RS,Hinze2013USR,Kmett2015MfL,Penner2017RSTT}.
\begin{code}
data Cofree h b = b :< h (Cofree h b)
\end{code}

The similarity between |Cofree h b| and the function decomposition from \secref{Decomposing Functions from Lists} (motivating the constructor name ``|:<|'') makes for easy instance calculation.
As with |Pow a| and |Map a b|, we can define a trie counterpart to the free monoid semiring |[c] -> b|.
\begin{theorem}[\provedIn{theorem:Cofree}]\thmlabel{Cofree}
Given the definitions in \figrefdef{Cofree}{List tries denoting |[c] -> b|}{
%format :<: = "\mathrel{\Varid{:\!\!\triangleleft\!:}}"
\begin{code}
infix 1 :<
data Cofree h b = b :< h (Cofree h b) deriving Functor

instance Indexable c (Cofree h b) (h (Cofree h b)) => Indexable [c] b (Cofree h b) where
  (!) (b :< dp) = b <: (!) . (!) dp -- |(b :< dp) ! w = case w of { [] -> b ; c:cs -> dp ! c ! cs }|

instance (Additive (h (Cofree h b)), Additive b) => Additive (Cofree h b) where
  zero = zero :< zero
  (a :< dp) <+> (b :< dq) = a <+> b :< dp <+> dq

instance (Functor h, Semiring b) => LeftSemimodule b (Cofree h b) where
  scale s = fmap (s NOP <.>)

instance  (Functor h, Additive (h (Cofree h b)), Semiring b, DetectableZero b) =>
          Semiring (Cofree h b) where
  one = one :< zero
  (a :< dp) <.> q = a .> q <+> (zero :< fmap (<.> NOP q) dp)

instance  (Functor h, Additive (h (Cofree h b)), StarSemiring b, DetectableZero b) =>
          StarSemiring (Cofree h b) where
  star (a :< dp) = q where q = star a .> (one :< fmap (<.> NOP q) dp)

instance  (HasSingle (Cofree h b) h, Additive (h (Cofree h b)), Additive b) =>
          HasSingle b (Cofree h) where
  w +-> b = foldr (\ c t -> zero :< c +-> t) (b :< zero) w

instance  (Additive (h (Cofree h b)), DetectableZero (h (Cofree h b)), DetectableZero b) =>
          DetectableZero (Cofree h b) where
  isZero (a :< dp) = isZero a && isZero dp

instance  (Functor h, Additive (h (Cofree h b)), DetectableZero b, DetectableZero (h (Cofree h b)), DetectableOne b) =>
          DetectableOne (Cofree h b) where
  isOne (a :< dp) = isOne a && isZero dp

\end{code}
\vspace{-4ex}
}, |(!)| is a homomorphism with respect to each instantiated class.
\end{theorem}

Although the |(<:)| decomposition in \secref{Decomposing Functions from Lists} was inspired by wanting to understand the essence of regular expression derivatives, the application to tries is in retrospect more straightforward, since the representation directly mirrors the decomposition.
\out{Pleasantly, this trie data structure is a classic, though perhaps not in its lazy infinite form for use as a language representation.}
Applying the |(<:)| decomposition to tries also appears to be more streamlined than the application to regular expressions.
During matching, the next character in the candidate string is used to directly index to the relevant derivative (sub-trie), efficiently bypassing all other paths.
As one might hope,
%if short
|(!)| is a comonad homomorphism from |Cofree h| to |(->) (Key h)| \seeproof{theorem:Cofree hom}.
%else
|(!)| on |Cofree h| is another homomorphism:
\begin{theorem}[\provedIn{theorem:Cofree hom}]\thmlabel{Cofree hom}
Given the definitions in \figreftwo{Cofree}{Cofree hom}, if |(!)| on |h| behaves like\notefoot{Come up with a better phrasing of this condition, and use it consistently} |(->) (Key h)|, then |Cofree h| is a comonad homomorphism from |Cofree h| to |(->) (Key h)|.
\end{theorem}
\figdef{Cofree hom}{|Comonad| and instances}{
\begin{code}
instance Functor w => Comonad w where
  coreturn  :: w b -> b
  cojoin    :: w b -> w (w b)

instance Monoid a => Comonad ((->) a) where
  coreturn  f = f mempty
  cojoin    f = \ u -> \ v -> f (u <> v)

instance Functor h => Functor (Cofree h) where
  fmap f (a :< ds) = f a :< fmap (fmap f) ds

instance Functor h => Comonad (Cofree h) where
  coreturn   (a :< _)   = a
  cojoin t@  (_ :< ds)  = t :< fmap cojoin ds
\end{code}
}
%endif


\sectionl{Performance}

%format a1 = a
%format b1 = b
%format letter = atoz

%format RegExpF = RegExp"_"->
%format RegExpM = RegExp"_"Map
%format CofreeF = Cofree"_"->
%format CofreeM = Cofree"_"Map

\nc\stat[6]{#1 & #2 & #3 & #4 & #5 \\ \hline}
\nc\incstat[1]{\input{test/stats/#1.txt}}

% For examples that don't run
\nc\hang{\ensuremath{\infty}}

While the implementation has had no performance tuning and only rudimentary benchmarking, we can at least get a sanity check on performance and functionality.
\figrefdef{examples}{Examples}{
\begin{code}

a1  = single "a"
b1  = single "b"

letter = sum [single [c] | c <- ['a' .. 'z']]

fishy = star letter <.> single "fish" <.> star letter

anbn = one <+> a1 <.> anbn <.> b1

dyck = star (single "[" <.> dyck <.> single "]")

\end{code}
} shows the source code for a collection of examples, all polymorphic in the choice of semiring.
The |letter| language contains single letters from `a' to `z'.
The examples |anbn| and |dyck| are two classic, non-regular, context-free languages: |set (a^n@@b^n # n <# N)| and the Dyck language of balanced brackets.

\figrefdef{stats}{Running times for examples in \figref{examples}}{
\begin{center}
\begin{tabular}{||c||c||c||c||c||}
\hline
\stat{Example}{|RegExpF|}{|RegExpM|}{|CofreeF|}{|CofreeM|}{} \hline
\hline
%include test/stats/star-a.txt
%include test/stats/letters.txt
%include test/stats/asas.txt
%include test/stats/asbs.txt
%include test/stats/asbas.txt
%include test/stats/fishy.txt
%include test/stats/anbn.txt
%include test/stats/dyck.txt
\end{tabular}
\end{center}
} gives some execution times for these examples measured with the \emph{criterion} library \citep{criterion}, compiled with GHC 8.6.3, and running on a late 2013 MacBook Pro.
(Note milliseconds vs microseconds---``ms'' vs ``$\mu{}$s''.)
Each example is interpreted in four semirings: |RegExp ((->) Char) N|, |RegExp (Map Char) N|, |Cofree ((->) Char N)|, and |Cofree (Map Char) N|.
Each interpretation of each language is given a matching input string of length 100; and matches are counted, thanks to use of the |N| semiring.
(The |star a * star a| example matches in 101 ways, while the others match uniquely.)
As the figure shows, memoization (via |Map|) is only moderately helpful (and occasionally harmful) for |RegExp|.
|Cofree|, on the other hand, performs terribly without memoization and (in these examples) 2K to 230K times faster with memoization.
Here, memoized |Cofree| performs between 8.5 and 485 times faster than memoized |RegExp| and between 11.5 and 1075 times faster than nonmemoized |RegExp|.
The two recursively defined examples fail to terminate with |RegExp Map|, perhaps because the implementation (\secref{Regular Expressions}) lacks one more crucial tricks \citep{Might2010YaccID}.
Other |RegExp| improvements \citep{Might2010YaccID,Adams2016CPP} might narrow the gap further, and careful study and optimization of the |Cofree| implementation (\figref{Cofree}) might widen it.

%% \note{Replace the |RegExpM| ns times with \hang.}

\sectionl{Convolution}

Consider again the definition of multiplication in the monoid semiring, on |f,g :: a -> b| from \figref{monoid semiring}.
\begin{code}
f * g  = bigSum (u,v) u <> v +-> f u <.> g v
\end{code}
As in \secref{Languages and the Monoid Semiring}, specializing the \emph{codomain} to |Bool|%
%if short
~and using
%else
, we get
\begin{code}
f <.> g = bigOr (u,v) u <> v +-> f u && g v
\end{code}
Using
%endif
the set/predicate isomorphism from \secref{Calculating Instances from Homomorphisms}, we can translate this definition from predicates to ``languages'' (sets of values in some monoid):
\begin{code}
f <.> g = set (u <> v | u <# f && v <# g)
\end{code}
which is the definition of the concatenation of two languages from  \secref{Languages and the Monoid Semiring}.
Likewise, by specializing the \emph{domain} of the functions to sequences (from general monoids), we got efficient matching of semiring-generalized ``languages'', as in \secreftwo{Decomposing Functions from Lists}{Tries}, which translated to regular expressions (\secref{Regular Expressions}), generalizing work of \citet{Brzozowski64}.

%format R = "\mathbb R"
%format C = "\mathbb C"

%if icfp
%format bigSumPlus (lim) = "\bigOp\sum{" lim "}{0.7}"
%else
%format bigSumPlus (lim) = "\bigOp\sum{" lim "}{1.4}"
%endif
Let's now consider specializing the functions' domains to \emph{integers} rather than sequences, recalling that integers (and numeric types in general) form a monoid under addition.
\vspace{-2ex}
\begin{spacing}{1.5}
\begin{code}
f <.> g  == bigSum (u,v) u + v +-> f u <.> g v                              -- \figref{monoid semiring} with |(<>) = (+)|
         == \ w -> bigSumPlus (u,v BR u + v == w) f u <.> g v               -- equivalent definition
         == \ w -> bigSumPlus (u,v BR v == w - u) f u <.> g v               -- solve |u + v == w| for |v|
         == \ w -> bigSum u f u <.> g (w - u)                               -- substitute |w - u| for |v|
\end{code}
\end{spacing}
\vspace{-3ex}
\noindent
This last form is the standard definition of one-dimensional, discrete \emph{convolution} \citep[Chapter 6]{Smith1997SEG}.\footnote{Note that this reasoning applies to \emph{any} group (monoid with inverses).}
Therefore, just as monoid semiring multiplication generalizes language concatenation (via the predicate/set isomorphism), it also generalizes the usual notion of discrete convolution.
Moreover, if the domain is a continuous type such as |R| or |C|, we can reinterpret summation as integration, resulting in \emph{continuous} convolution.
Additionally, for multi-dimensional (discrete or continuous) convolution, we can simply use tuples of scalar indices for |w| and |u|, defining tuple addition and subtraction componentwise.
\notefoot{More generally, cartesian products of monoids are also monoids.
Consider multi-dimensional convolution in which different dimensions have different types, even mixing discrete and continuous, and maybe even sequences and numbers.
At the least, it's useful to combine finite dimensions of different sizes.}
Alternatively, curry, convolve, and uncurry, exploiting the fact that |curry| is a semiring homomorphism (\thmref{curry semiring}).
\notefoot{Mention the connection between generalized tries and currying.}

\note{Maybe give some convolution examples.}

%format Unit = "\mathbb 1"
%format Unit = ()
What if we use functions from |N| rather than from |Z|?
Because |N =~ [Unit]| (essentially, Peano numbers), we can directly use the definitions in \secref{Decomposing Functions from Lists} for domain |[c]|, specialized to |c = Unit|.
As a suitable indexable functor, we can simply use the identity functor:
%% %format Identity = Id
%format Id = Identity
\begin{code}
newtype Id b = Id b deriving
  (Functor, Additive, DetectableZero, DetectableOne, LeftSemimodule s, Semiring)

instance Indexable  () b (Id b) where Id a ! () = a
instance HasSingle  () b (Id b) where () +-> b = Id b
\end{code}
The type |Cofree Identity| is isomorphic to \emph{streams} (infinite-only lists).
Inlining and simplification during compilation might eliminate all of the run-time overhead of introducing the identity functor.

Just as |Cofree Identity| gives (necessarily infinite) streams, |Cofree Maybe| gives (possibly finite) \emph{nonempty lists} \citep{Uustalu2008CNC, Maguire2016}.
As with finite maps, we can interpret absence (|Nothing|) as |zero|%
%if short
~\citeLong.
%else
:
\begin{code}
instance Additive b => Indexable () b (Maybe b) where
  Nothing  ! () = zero
  Just b   ! () = b

instance (DetectableZero b, Additive b) => HasSingle () b (Maybe b) where 
  () +-> b  | isZero b   = Nothing
            | otherwise  = Just b
\end{code}

%endif
Alternatively, define instances directly for lists, specified by a denotation of |[b]| as |N -> b|.
The instances resemble those in \figref{Cofree}, but have an extra case for the empty list and no |fmap|:
\begin{code}
instance Additive b => Indexable N b [b] where
  [] ! _ = zero
  (b  :  _   ) ! 0  = b
  (_  :  bs  ) ! n  = bs ! (n-1)

instance Additive b => Additive [b] where
  zero = []
  [] <+> bs = bs
  as <+> [] = as
  (a : as) <+> (b : bs) = a <+> b : as <+> bs

instance (Semiring b, DetectableZero b, DetectableOne b) => Semiring [b] where
  one = one : zero
  []        <.> _  = [] NOP -- |0 * q == 0|
  (a : dp)  <.> q  = a .> q <+> (zero : dp <.> q)
\end{code}
This last definition is reminiscent of long multiplication, which is convolution in disguise.

\sectionl{Beyond Convolution}

%format Fin (m) = Fin "_{" m "}"
%format Array (m) = Array "_{" m "}"

Many uses of discrete convolution (including convolutional neural networks \citep[Chapter 9]{LecunBengioHinton2015DLNature}) involve functions having finite support, i.e., nonzero on only a finite subset of their domains.
\notefoot{First suggest finite maps, using instances from \figref{Map}. Then intervals/arrays.}
In many cases, these domain subsets may be defined by finite \emph{intervals}.
For instance, such a 2D operation would be given by intervals in each dimension, together specifying lower left and upper right corners of a 2D interval (rectangle) outside of which the functions are guaranteed to be zero.
The two input intervals needn't have the same size, and the result's interval of support is typically larger than both inputs, with size equaling the sum of the sizes in each dimension (minus one for the discrete case).
\notefoot{Show an example as a picture.}
Since the result's support size is entirely predictable and based only on the arguments' sizes, it is appealing to track sizes statically via types.
For instance, a 1D convolution might have the following type:
\notefoot{To do: More clearly distinguish between functions with finite support vs functions with finite domains. I think I started this paragraph with the former mindset but switched to the latter.}
\begin{code}
(*) :: Semiring s => Array (m+1) s -> Array (n+1) s -> Array (m+n+1) s
\end{code}
Unfortunately, this signature is incompatible with semiring multiplication, in which arguments and result all have the same type.

From the perspective of functions, an array of size |n| is a memoized function from |Fin n|, a type representing the finite set |set (0, ..., n-1)|.
We can still define convolution in the customary sense in terms of index addition:
\begin{code}
f <.> g = bigSum (u,v) u + v +-> f u <.> g v
\end{code}
where now
\begin{code}
(+) :: Fin (m+1) -> Fin (n+1) -> Fin (m+n+1)
\end{code}
Indices can no longer form a monoid under addition, however, due to the nonuniformity of types.

%format lift0
%format lift1
%format lift2
%format liftn = lift "_n"

The inability to support convolution on statically sized arrays (or other memoized forms of functions over finite domains) as semiring multiplication came from the expectation that indices/arguments combine via a monoid.
Fortunately, this expectation can be dropped by generalizing from monoidal combination to an \emph{arbitrary} binary operation |h :: a -> b -> c|.
For now, let's call this more general operation ``|lift2 h|''.
\begin{code}
lift2 :: Semiring s => (a -> b -> c) -> (a -> s) -> (b -> s) -> (c -> s)
lift2 h f g = bigSum (u,v) h u v +-> f u <.> g v
\end{code}
We can similarly lift functions of \emph{any} arity:
%format a1
%format an = a "_n"
%format f1
%format fn = f "_n"
%format u1
%format un = u "_n"
\begin{code}
liftn :: Semiring s => (a1 -> ...^ -> an -> b) -> (a1 -> s) -> ...^ -> (an -> s) -> (b -> s)
liftn h f1 ...^ fn = bigSumQ (u1, ..., un) h u1 ...^ un +-> f1 u1 <.> ...^ <.> fn un
\end{code}
Here we are summing over the set-valued \emph{preimage} of |w| under |h|.
Now consider two specific instances of |liftn|:
\begin{code}
lift1 :: Semiring s => (a -> b) -> (a -> s) -> (b -> s)
lift1 h f = bigSum u h u +-> f u

lift0 :: Semiring s => b -> (b -> s)
lift0 b  = b +-> one
         = single b
\end{code}

%format FunctorC = Functor
%format ApplicativeC = Applicative
%format MonadC = Monad
%format fmapC = fmap
%format pureC = pure
%format liftA2C = liftA2
%format >>== = >>=
%% %format keys p = p
\noindent
The signatures of |lift2|, |lift1|, and |lift0| \emph{almost} generalize to those of |liftA2|, |fmap|, and |pure| from the |Functor| and |Applicative| type classes \citep{McBride2008APE,Typeclassopedia}.
In type systems like Haskell's, however, |a -> s| is the functor |(a ->)| applied to |s|, while we would need it to be |(-> s)| applied to |a|.
To fix this problem, define a type wrapper that swaps domain and codomain type parameters:
\begin{code}
newtype s <-- a = F (a -> s)
\end{code}
The use of |s <-- a| as an alternative to |a -> s| allows us to give instances for both and to stay within Haskell's type system (and ability to infer types via first-order unification).

With this change, we can replace the specialized |liftn| operations with standard ones.
An enhanced version of the |Functor|, |Applicative|, and |Monad| classes (similar to those by \citet{Kidney2017CA}) appear in \figrefdef{FunApp}{|Functor| and |Applicative| classes and some instances}{
\begin{code}
class FunctorC f where
  type Ok f a :: Constraint
  type Ok f a = ()  -- default
  fmapC :: (Ok f a, Ok f b) => (a -> b) -> f a -> f b

class FunctorC f => ApplicativeC f where
  pureC :: Ok f a => a -> f a
  liftA2C :: (Ok f a, Ok f b, Ok f c) => (a -> b -> c) -> f a -> f b -> f c

infixl 1 >>==
class ApplicativeC f => MonadC f where
  (>>==) :: (Ok f a, Ok f b) => f a -> (a -> f b) -> f b
NOP

instance Functor ((->) a) where                instance Semiring b => Functor ((<--) b) where                              
                                                 type Ok ((<--) b) a = Eq a                                                
  fmap h f = \ a -> h (f a)                      fmap h (F f)  = bigSum u h u +-> f u                                      
                                                               = F (\ z -> bigSumQ (u BR h u == z) f u)                    
                                                                                                                           
instance Applicative ((->) a) where     SPC8   instance Semiring b => Applicative ((<--) b) where                          
  pure b = \ a -> b                              pure a = single a                                                         
  liftA2 h f g = \ a -> h (f a) (g a)            liftA2 h (F f) (F g)  = bigSum (u,v) h u v +-> f u <.> g v                
                                                                       = F (\ z -> bigSumQ (u,v BR h u v == z) f u <.> g v)

instance Monad ((->) a) where
  m >>= f = \ a -> f (m a) a

instance Ord a => Functor      (Map a) where ...
instance Ord a => Applicative  (Map a) where ...

newtype Map' b a = M (Map a b)

instance DetectableZero b => FunctorC (Map' b) where
  type Ok (Map' b) a = Ord a
  fmapC h (M p) = bigSumKeys (a <# M.keys p) h a +-> p ! a

instance DetectableZero b => ApplicativeC (Map' b) where
  pureC a = single a
  liftA2C h (M p) (M q) = bigSumKeys (a <# M.keys p BR b <# M.keys q) h a b +-> (p!a) <.> (q!b)
\end{code}

  %% f * g  = bigSum (u,v) u <> v +-> f u <.> g v
  %%        = \ w -> bigSumQ (u,v BR u <> v == w) f u <.> g v
\vspace{-3ex}
}, along with instances for functions and finite maps.
Other representations would need similar reversal of type arguments.
\footnote{The enhancement is the associated constraint \citep{Bolingbroke2011CK} |Ok|, limiting the types that the class methods must support. The line ``|type Ok f a = ()|'' means that the constraint on |a| defaults to |()|, which holds vacuously for all |a|.}%
\footnote{Originally, |Applicative| had a |(<*>)| method from which one can easily define |liftA2|. Since the base library version 4.10, |liftA2| was added as a method (along with a default definition of |(<*>)|) to allow for more efficient implementation \citep[Section 3.2.2]{GHC821}.}
Higher-arity liftings can be defined via these three.
\out{(Exercise.)}
For |b <-- a|, these definitions are not really executable code, since they involve potentially infinite summations, but they serve as specifications for other representations such as finite maps, regular expressions, and tries.
\begin{theorem}
For each instance defined in \figref{FunApp}, |one = pure mempty|, and |(*) = liftA2 (<>)|.
\notefoot{Probe more into the pattern of |single = pure|, |one = single mempty| and |(*) = liftA2 (<>)|.
Also the relationship between forward and reverse functions and maps.}
\end{theorem}
\begin{proof}
Immediate from the instance definitions.
\end{proof}

Given the type distinction between |a -> b| and |b <-- a|, let's now reconsider the |Semiring| instances for functions in \figref{monoid semiring} and for sets in \secref{Languages and the Monoid Semiring}.
Each has an alternative choice that is in some ways more compelling, as shown in \figrefdef{-> and <-- semirings}{The |a -> b| and |b <-- a| semirings}{
%format Pow'
\begin{code}
instance Semiring b => Semiring (a -> b) where
  one = pure one    -- i.e., |one = \ a -> one|
  (*) = liftA2 (*)  -- i.e., |f * g = \ a -> f a * g a|

newtype b <-- a = F (a -> b) deriving (Additive, HasSingle b, LeftSemimodule b, Indexable a b)

instance (Semiring b, Monoid a) => Semiring (b <-- a) where
  one = pure mempty
  (*) = liftA2 (<>)

instance Semiring (Pow a) where
  one = set (a | True)
  (*) = `intersect`

newtype Pow' a = P (Pow a) deriving (Additive, HasSingle b, LeftSemimodule b, Indexable a Bool)

instance Semiring (Pow' a) where
  one = pure mempty  -- |one = set mempty = single empty = value 1|
  (*) = liftA2 (<>)  -- |p * q = set (u <> v # u <# p && v <# q)|
\end{code}
\vspace{-4ex}
}, along with a the old |a -> b| instance reexpressed and reassigned to |b <-- a|.
Just as the |Additive| and |Semiring| instances for |Bool <-- a| give us four important languages operations (union, concatenation and their identities), now the |Semiring (a -> Bool)| gives us two more: the \emph{intersection} of languages and its identity (the set of all ``strings'').
These two semirings share several instances in common, expressed in \figref{-> and <-- semirings} via GHC-Haskell's \verb|GeneralizedNewtypeDeriving| language extension (present since GHC 6.8.1 and later made safe by \citet{Breitner2016SZC}).
All six of these operations are also useful in their generalized form (i.e., for |a -> b| and |b <-- a| for semirings |b|).
As with |Additive|, this |Semiring (a -> b)| instance implies that curried functions (of any number and type of arguments and with semiring result type) are semirings, with |curry| and |uncurry| being semiring homomorphisms.
(The proof is very similar to that of \thmref{curry additive}.)

The |a -> b| and |b <-- a| semirings have another deep relationship:
%format Fourier = "\mathcal F"
\begin{theorem}\thmlabel{Fourier}
The Fourier transform is a semiring and left semimodule homomorphism from |b <- a| to |a -> b|.
\end{theorem}
This theorem is more often expressed by saying that (a) the Fourier transform is linear (i.e., an additive-monoid and left-semimodule homomorphism), and (b) the Fourier transform of a convolution (i.e., |(*)| on |b <-- a|) of two functions is the pointwise product (i.e., |(*)| on |a -> b|) of the Fourier transforms of the two functions.
The latter property is known as ``the convolution theorem'' \citep[Chapter 6]{Bracewell2000Fourier}.

There is also an important relationship between |a -> b| and |Pow a <-- b|.
Given a function |f :: a -> b|, the \emph{preimage} under \emph{f} of a codomain value |b| is the set of all values that get mapped to |b|:
\begin{code}
pre :: (a -> b) -> (Pow a <-- b)
pre f = F (\ b -> set (a | f a == b))
\end{code}
\begin{theorem}[\provedIn{theorem:pre hom}]\thmlabel{pre hom}
The |pre| operation is a |Functor| and |Applicative| homomorphism.
\end{theorem}

\sectionl{The Free Semimodule Monad}

Where there's an applicative, there's often a compatible monad.
For |b <-- a|, the monad is known as the ``free semimodule monad'' (or sometimes the ``free \emph{vector space} monad'') \citep{Piponi2007MonadVS,Kmett2011FreeModules,Gehrke2017Q}.
The semimodule's dimension is the cardinality of |a|.
Basis vectors have the form |single u = u +-> one| for |u :: a| (mapping |u| to |one| and every other value to |zero| as in \figref{monoid semiring}).

The monad instances for |(<--) b| and |Map' b| are defined as follows:\footnote{The |return| method does not appear here, since it is equivalent to |pure| from |Applicative|.}
\begin{code}
instance Semiring s => Monad ((<--) s) where
  (>>=) :: (s <-- a) -> (a -> (s <-- b))) -> (s <-- b)
  F f >>== h = bigSum a f a .> h a

instance (Semiring b, DetectableZero b) => MonadC (Map' b) where
  M m >>== h = bigSumKeys (a <# M.keys m) m!a .> h a
\end{code}
\vspace{-2ex}
\begin{theorem}[\provedIn{theorem:standard FunApp}]\thmlabel{standard FunApp}
The definitions of |fmap| and |liftA2| on |(<--) b| in \figref{FunApp} satisfy the following standard equations for monads:
\begin{code}
fmap h p = p >>= pure . h

liftA2 h p q  = p >>= \ u -> fmap (h u) q
              = p >>= \ u -> q >>= \ v -> pure (h u v)
\end{code}
\end{theorem}

%if otherApps

\sectionl{Other Applications}

\subsectionl{Polynomials}

%format N = "\mathbb{N}"
%format (Sum a) = a

As is well known, univariate polynomials form a semiring and can be multiplied by convolving their coefficients.
Perhaps less known is that this trick extends naturally to power series and to multivariate polynomials.

%format ^^ = "\string^"
%format pows a (b) = a "\!{\string^}^{\hspace{-1pt}" b "}"
%% %format pows a (b) = pow a (^b)

%format sub u (v) = u "_" v
%format (psub u (v)) = u "_" v
%format bigProd (lim) = "\bigOp\prod{" lim "}{0}"
%% %format bigProdQ (lim) = "\bigOp\prod{" lim "}{1}"
%format poly1
%format Integer = Z
%format >>> = "\lambda\rangle\ "

Looking more closely, univariate polynomials (and even power series) can be represented by a collection of coefficients indexed by exponents, or conversely as a collection of exponents weighted by coefficients.
For a polynomial in a variable |x|, an association |i +-> c| of coefficient |c| with exponent |i| represents the monomial (polynomial term) |c * x^i|.
One can use a variety of representations for these indexed collections.
We'll consider efficient representations below, but let's begin as |b <-- N| along with a denotation as a (polynomial) function of type |b -> b|:
\begin{code}
poly1 :: Semiring b => (b <-- N) -> (b -> b)
poly1 (F f) = \ x -> bigSum i  f i * x^i
\end{code}
%if True
Polynomial multiplication via convolution follows from the following property:
\begin{theorem}[\provedIn{theorem:poly hom}]\thmlabel{poly hom}
The function |poly1| is a semiring homomorphism when multiplication on |b| commutes.
\end{theorem}
Pragmatically, \thmref{poly hom} says that the |b <-- N| semiring (in which |(*)| is convolution) correctly implements arithmetic on univariate polynomials.
More usefully, we can adopt other representations of |b <-- N|, such as |Map N b|.
For viewing results, wrap these representations in a new type, and provide a |Show| instance:
%format Poly1
\begin{code}
newtype Poly1 z = Poly1 z deriving (Additive, Semiring, Indexable n b, HasSingle n b)

instance (...) => Show (Poly1 z) where NOP ...
\end{code}
Try it out (with prompts indicated by ``|>>>|''):
%{
%format * = "{}"
%subst blankline = "\\[1.5ex]"
\begin{code}

>>> let p = single 1 <+> value 3 :: Poly1 (Map N Z)
>>> p
x + 3

>>> p^3
x^3 + 9 * x^2 + 27 * x + 27

>>> p^7
2187 + 5103 * x + 5103 * x^2 + 2835 * x^3 + 945 * x^4 + 189 * x^5 + 21 * x^6 + x^7

>>> poly1 (p^5) 17 == (poly1 p 17)^5
True

\end{code}
%}
%endif

We can also use |[]| in place of |Map N|.
The example above yields identical results.
Since lists are potentially infinite (unlike finite maps), however, this simple change enables power series%
%if short
~\citep{McIlroy1999PSPS,McIlroy2001MS,Elliott2019-convolution-extended}.
%else
.
Following \citet{McIlroy1999PSPS,McIlroy2001MS}, define integration and differentiation as follows:
%format integralL = integral
%format derivativeL = derivative
%format sinL = sin"_{\hspace{-1pt}p}"
%format cosL = cos"_{\hspace{-1pt}p}"
%format expL = exp"_{\hspace{-1pt}p}"
%format bs0
\begin{code}
integralL :: Fractional b => Poly1 [b] -> Poly1 [b]
integralL (Poly1 bs0) = Poly1 (0 : go 1 bs0)
  where
    go _ []       = []
    go n (b : d)  = b/n : go (n+1) d

derivativeL :: (Additive b, Fractional b) => Poly1 [b] -> Poly1 [b]
derivativeL (Poly1     []        ) = zero
derivativeL (Poly1 (_  :   bs0)  ) = Poly1 (go 1 bs0)
  where
    go _ []        = []
    go n (b : bs)  = n * b : go (n+1) bs
\end{code}
%if False
\begin{theorem}
The |integralL| and |derivativeL| definitions above correctly implement integration and differentiation, i.e.,
\begin{code}
poly1 (integralL p) == integral (poly1 p)
poly1 (derivativeL p) == derivative (poly1 p)
\end{code}
\end{theorem}
\begin{proof}~
\workingHere
\end{proof}
%endif
Then define |sin|, |cos|, and |exp| via simple ordinary differential equations (ODEs):
\begin{code}
sinL, cosL, expL :: Poly1 [Rational]
sinL = integralL cosL
cosL = 1 - integralL sinL
expL = 1 + integralL expL
\end{code}
Try it out:
%format lop (e) = e
%{
%format % = "/"
\begin{code}

>>> lop sinL
x + (-1) % 6 * x^3 + 1 % 120 * x^5 + (-1) % 5040 * x^7 + 1 % 362880 * x^9 + (-1) % 39916800 * x^11 + 1 ...^
>>> lop cosL
1 % 1 + (-1) % 2 * x^2 + 1 % 24 * x^4 + (-1) % 720 * x^6 + 1 % 40320 * x^8 + (-1) % 3628800 * x^10 + 1 ...^
>>> lop expL
1 % 1 + x + 1 % 2 * x^2 + 1 % 6 * x^3 + 1 % 24 * x^4 + 1 % 120 * x^5 + 1 % 720 * x^6 + 1 % 5040 * x^7 ...^
\end{code}
As expected, |derivativeL sinL == cosL|, |derivativeL cosL == - sinL|, and |derivativeL expL == expL|:
\begin{code}

>>> lop (derivativeL sinL)
1 % 1 + (-1) % 2 * x^2 + 1 % 24 * x^4 + (-1) % 720 * x^6 + 1 % 40320 * x^8 + (-1) % 3628800 * x^10 + 1 ...^
>>> lop (derivativeL cosL)
(-1) % 1 * x + 1 % 6 * x^3 + (-1) % 120 * x^5 + 1 % 5040 * x^7 + (-1) % 362880 * x^9 + 1 % 39916800 * ...^
>>> lop (derivativeL expL)
1 % 1 + x + 1 % 2 * x^2 + 1 % 6 * x^3 + 1 % 24 * x^4 + 1 % 120 * x^5 + 1 % 720 * x^6 + 1 % 5040 * x^7 ...^

\end{code}
%}
Crucially for termination of ODEs such as these, |integralL| is nonstrict, yielding its result's first coefficient before examining its argument.
In particular, the definition of |integralL| does \emph{not} optimize for |Poly1 []|.

\vspace{2ex}
%endif short


What about multivariate polynomials, i.e., polynomial functions over higher-dimensional domains?
%if long
Consider a 2D domain:
%format poly2
\begin{code}
poly2 :: Semiring b => (b <-- N :* N) -> (b * b -> b)
poly2 (F f) = \ (x,y) -> bigSum (i,j) f (i,j) * x^i * y^j
\end{code}
Then
\begin{code}
    poly2 (F f) (x,y)
==  bigSum (i,j) f (i,j) * x^i * y^j             -- |poly2| definition
==  bigSum (i,j) curry f i j * x^i * y^j         -- |curry| definition
==  bigSum i (bigSum j curry f i j * y^j) * x^i  -- linearity and commutativity assumption
==  bigSum i poly (curry f i) y * x^i            -- |poly| definition
==  poly (\ i -> poly (curry f i) y) x           -- |poly| definition
\end{code}
The essential idea here is that a polynomial with a pair-valued domain can be viewed as a polynomial over polynomials.

We can do much better, however, generalizing from two dimensions to |n| dimensions for any |n|:
%else
Generalize to |n| dimensions:
%endif long
\twocol{0.5}{
\begin{code}
poly :: (b <-- N^n) -> (b^n -> b)
poly (F f) (x :: b^n) = bigSum (p :: N^n)  f p * pows x p
\end{code}}{0.45}{
\begin{code}
infixr 8 NOP ^^
(^^) :: b^n -> N^n -> b
pows x p = bigProd (i < n) @@ pow (psub x i) (sub p i)
\end{code}}

\noindent
For instance, for |n=3|, |pows (x,y,z) ((i,j,k)) = x^i * y^j * z^k|.
Generalizing further,\out{ rather than taking |n| here to be a natural number,} let |n| be any type\out{ with countable cardinality}, and interpret |b^n| and |N^n| as |n -> b| and |n -> N|:
\twocol{0.5}{
\begin{code}
poly :: (b <-- (n -> N)) -> ((n -> b) -> b)
poly (F f) (x :: n -> b) = bigSumQ (p :: n -> N)  f p * pows x p
\end{code}}{0.45}{
\begin{code}
infixr 8 NOP ^
(^^) :: (n -> b) -> (n -> N) -> b
pows x p = bigProd i @@ pow (x i) ((p i))
\end{code}}

%if long
\begin{lemma}[\provedIn{lemma:pows hom}]\lemlabel{pows hom}
When |(*)| commutes, |(^^)| satisfies the following exponentiation laws:
\notefoot{Maybe also |pows (pows x p) q == pows x (p * q)|. Hunch: I'd have to generalize regular exponentiation and make |(^^)| a special case.
Handily, I could then drop the carrot symbol.
I think I'll also need the |Listable| class (preferably with a better name).}
\begin{code}
pows x zero == one
pows x (p + q) == pows x p * pows x q
\end{code}
%if long
In other words, |pows x| is a (commutative) monoid homomorphism from the sum monoid to the product monoid.
%endif
\end{lemma}
%endif

\begin{theorem}%
%if short
[\provedIn{foo}]%
%endif
\thmlabel{generalized poly hom}
The generalized |poly| function is a semiring homomorphism when multiplication on |b| commutes.
\end{theorem}
%if long
\begin{proof}
Just like the proof of \thmref{poly hom}, given \lemref{pows hom}.
\end{proof}
%endif
\thmref{generalized poly hom} says that the |b <-- (n -> N)| semiring (in which |(*)| is higher-dimensional convolution) correctly implements arithmetic on multivariate polynomials.
We can instead use |Map (f N) b| to denote |b <-- (n -> N)|, where |f| is indexable with |Key f = n|.
One convenient choice is to let |n = String| for variable names, and |f = Map String|.\footnote{Unfortunately, the |Monoid| instance for the standard |Map| type defines |m <> m'| so that keys present in |m'| \emph{replace} those in |m|.
This behavior is problematic for our use (and many others), so we must use a |Map| variant that wraps the standard type, changing the |Monoid| instance so that |m <> m'| \emph{combines} values (via |(<>)|) associated with the same keys in |m| and |m'|.}
As with |Poly1|, wrap this representation in a new type, and add a |Show| instance:
%format PolyM = Poly "_{\!M}"
%format varM = var "_{\!M}"
%format varM = var
%format Name = String
\begin{code}
newtype PolyM b = PolyM (Map (Map Name N) b)
  deriving (Additive, Semiring, Indexable n, HasSingle n, Functor)

instance (...) => Show (PolyM b) where ...

varM :: Semiring b => Name -> PolyM b
varM = single . single
\end{code}
Try it out:
%{
%% %format @ = "\mathbin{@}"
%format @ = "\,@"
%format * = "{}"
%subst blankline = "\\[1.5ex]"
\begin{code}

>>> let p = varM "x" <+> varM "y" <+> varM "z" :: PolyM Z
>>> p
x + y + z

>>> p^2
x^2 + 2 * x * y + 2 * x * z + y^2 + 2 * y * z + z^2

>>> p^3
x^3 + 3 * x^2 * y + 3 * x * y^2 + 6 * x * y * z + 3 * x^2 * z + 3 * x * z^2 + y^3 + 3 * y^2 * z + 3 * y * z^2 + z^3

\end{code}
%}

\note{Next:
\begin{itemize}
\item Generalize |a^b| and |(a^^b)| via a class, as in the implementation.
\item Maybe generalize |Poly1| from the start.
\item Power series (infinite polynomials).
      Maybe also |[a]|, representing |a <-- N|.
\item Should I move multidimensional convolution to \secref{Convolution}?
\item References on multivariate polynomial multiplication \href{https://www.google.com/search?q=algorithm+for+multiplying+multivariate+polynomials}{(starting here)}
\item Generalize to $m$-dimensional codomains (and maybe swap roles of $m$ and $n$)
\item Finite maps
\end{itemize}
}

\subsectionl{Image Convolution}

\nc\figO[1]{
\begin{minipage}[t]{0.23\textwidth}
\centering
\includegraphics[width=\textwidth]{test/wizard-#1.png}
\\\textit{#1}
\end{minipage}
}

\figrefdef{wizard}{Image convolution}{
\figO{original}\figO{blur}\figO{sharpen}\figO{edge-detect}
\vspace{-3ex}
} shows examples of image convolution with some commonly used kernels \citep{Petrick2016Kernels,Young95FIP}.
The source image (left) and convolution kernels are all represented as lists of lists of floating point grayscale values.
Because (semiring) multiplication on |[b]| is defined via multiplication on |b|, one can nest representations arbitrarily.
Other more efficient representations can work similarly.

%endif

\sectionl{Related Work}

This paper began with a desire to understand regular expression matching via ``derivatives'' by \citet{Brzozowski64} more fundamentally and generally.
Brzozowski's method spurred much follow-up investigation in recent years.
\citet{Owens2009RE} dusted off regular expression derivatives after years of neglect with a new exposition and experience report.
\citet{Might2010YaccID} considerably extended expressiveness to context-free grammars\iflong{ (recursively defined regular expressions)} as well as addressing some efficiency issues, including memoization, with further performance analysis given later \citep{Adams2016CPP}.
\citet{Fischer2010PRE} also extended regular language membership from boolean to ``weighted'' by an arbitrary semiring, relating them to weighted finite automata.
\citet{Piponi2015PF} investigated regular expressions and their relationship to the semiring of polynomial functors, as well as data type derivatives and dissections.
\citet{Radanne2018RLG} explored regular expressions extended to include intersection and complement (as did Brzozowski) with an emphasis on testing.

\citet{McIlroy1999PSPS,McIlroy2001MS} formulated power series as a small and beautiful collection of operations on infinite coefficient streams, including not only the arithmetic operations, but also inversion and composition, as well as differentiation and integration.
He also defined transcendental operations by simple recursion and integration, such as |sin = integral cos| and |cos = 1 - integral sin|.

\citet{Dongol2016CUC} investigated convolution in a general algebraic setting that includes formal language concatenation.
\citet{Kmett2015MfL} observed that Moore machines are a special case of the cofree comonad.
The connections between parsing and semirings have been explored deeply by \citet{Goodman1998PIO,Goodman1999SP} and by \citet{Liu2004}, building on the foundational work of \citet{Chomsky1959CFL}.
\citet{Kmett2011FreeModules} also explored some issues similar to those in the present paper, building on semirings and free semimodules, pointing out that the classic continuation monad can neatly represent linear functionals.

\citet{Kidney2016Semi,semiring-num} implemented a Haskell semiring library that helped with early implementations leading to the present paper, with a particular leaning toward convolution \citep{Kidney2017CS}.
Several of the class instances given above, though independently encountered, also appear in that library.

\note{To do: More fully describe connections between this paper and the work cited above.}

%if False
\workingHere
\note{
\begin{itemize}
\item Derivatives for language matching and parsing
\item Applications of semirings, including parsing
\item Polynomials and power series, including Doug McIlroy's work
\item Automata, including weighted.
      The cofree comonad is a Moore machine \citep{Kmett2015MfL}.
      Hm. Maybe my trie idea is direct construction of Moore automata.
\end{itemize}
}
%endif


%% \sectionl{Conclusions and Future Work}

\note{
\begin{itemize}
\item More careful performance testing, analysis, and optimization.
\item Explore Brzozowski derivatives as actual derivatives of residual functions, as in my journal notes from 2019-02-08.
\item Generalization from lists to other data types.
\item Comonadic animation and imagery.
\end{itemize}
}


%if False
\sectionl{Miscellaneous Notes}

\begin{itemize}
\item From sets to relations via currying or the pair monoid.
\item |single| as a monoid homomorphism (targeting the product monoid).
\item Require that |(!)| be natural (a functor homomorphism) so that its |Functor| instance is consistent with functions.
      Ditto for |Applicative|?
\item
  Homomorphisms:
  \begin{itemize}
  \item
    Homomorphisms as specifications
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
    \end{itemize}
  \end{itemize}
\item
  Unsorted:
  \begin{itemize}
  \item
    Relate Brzozowski derivatives to the derivatives of residual functions, as in the notes below.
  \item
    The trie perspective naturally leads to generalizing from lists to arbitrary (regular?) algebraic data types.
    I'm less confident about this generalization claim, since I think we need a suitable monoid.
    I think there's an underlying generic monad that specializes to lists and other algebraic data types, with monadic bind specializing to |mappend|.
    On the other hand, with multiple substitution sites, inverting |mappend| seems tricky.
    Does it give a useful form of constrained or context-sensitive grammars?
  \end{itemize}
\end{itemize}

%endif

%if long

\appendix


\sectionl{Proofs}

\subsection{\thmref{curry additive}}\prooflabel{theorem:curry additive}

\begin{code}
    curry zero
==  curry (\ (x,y) -> zero)                       -- |zero| on functions
==  \ x -> \ y -> zero                            -- |curry| definition
==  \ x -> zero                                   -- |zero| on functions
==  zero                                          -- |zero| on functions

    curry (f + g)
==  curry (\ (x,y) -> f (x,y) + g (x,y))          -- |(+)| on functions
==  \ x -> \ y -> f (x,y) + g (x,y)               -- |curry| definition
==  \ x -> \ y -> curry f x y + curry g x y       -- |curry| definition (twice)
==  \ x -> curry f x + curry g x                  -- |(+)| on functions
==  curry f + curry g                             -- |(+)| on functions
\end{code}
Likewise for |uncurry|, or because |curry| and |uncurry| are inverses.

\subsection{\thmref{curry semiring}}\prooflabel{theorem:curry semiring}

For |one :: u :* v -> b|,
\begin{code}
    curry one
==  curry (mempty +-> one)           -- |one| on functions
==  curry ((mempty,mempty) +-> one)  -- |mempty| on pairs
==  mempty +-> mempty +-> one        -- \lemref{curry +->}
==  mempty +-> one                   -- |one| on functions
==  one                              -- |one| on functions
\end{code}

\noindent
For |f, g :: u :* v -> b|,
\begin{code}
    curry (f * g)
==  curry (bigSumPlus ((u,v),(s,t)) (u,s) <> (v,t) +-> f (u,s) <.> g (v,t))      -- |(*)| on functions (monoid semiring)
==  curry (bigSumPlus ((u,v),(s,t)) (u <> v,s <> t) +-> f (u,s) <.> g (v,t))     -- |(<>)| on pairs
==  bigSumPlus ((u,v),(s,t)) u <> v +-> s <> t +-> f (u,s) <.> g (v,t)           -- \lemref{curry +->}
==  bigSum (u,v) @@ bigSum (s,t) u <> v +-> s <> t +-> f (u,s) <.> g (v,t)       -- summation mechanics
==  bigSum (u,v) u <> v +-> bigSum (s,t) s <> t +-> f (u,s) <.> g (v,t)          -- \lemref{+-> homomorphism}
==  bigSum (u,v) u <> v +-> bigSum (s,t) s <> t +-> curry f u s <.> curry g v t  -- |curry| definition
==  bigSum (u,v) u <> v +-> curry f u <.> curry g v                              -- |(+->)| on functions
==  curry f * curry g                                                            -- |(+->)| on functions
\end{code}

\subsection{\lemref{decomp +->}}\prooflabel{lemma:decomp +->}

\begin{code}
    bigSum a a +-> f a
==  bigSum a (\ a' -> if a' == a then f a else zero)  -- |(+->)| on |a -> b|
==  \ a' -> bigSum a if a' == a then f a else zero    -- |(<+>)| on |a -> b|
==  \ a' -> f a'                                      -- other addends vanish
==  f                                                 -- $\eta$ reduction
\end{code}

\subsection{\lemref{curry +->}}\prooflabel{lemma:curry +->}

\begin{code}
    curry ((a,b) +-> c)
==  curry (\ (u,v) -> if (u,v) == (a,b) then c else zero)                -- |(+->)| on functions
==  curry (\ (u,v) -> if u == a && v == b then c else zero)              -- pairing is injective
==  \ u -> \ v -> if u == a && v == b then c else zero                   -- |curry| definition
==  \ u -> \ v -> if u == a then (if v == b then c else zero) else zero  -- property of |if| and |(&&)|
==  \ u -> if u == a then (\ v -> if v == b then c else zero) else zero  -- |(u == a)| is independent of |v|
==  \ u -> if u == a then b +-> c else zero                              -- |(+->)| on functions
==  a +-> b +-> c                                                        -- |(+->)| on functions
\end{code}

\subsection{\thmref{semiring hom ->}}\prooflabel{theorem:semiring hom ->}

\begin{code}
    setPred one
==  setPred (set mempty)                        -- |one| on sets
==  \ w -> w <# set mempty                      -- |setPred| definition
==  \ w -> w == mempty                          -- property of sets
==  \ w -> if w == mempty then True else False  -- property of |if|
==  \ w -> if w == mempty then one else zero    -- |one| and |zero| on |Bool|
==  mempty +-> one                              -- |(+->)| definition
==  one                                         -- |one| on functions
\end{code}

%if True

\begin{code}
    predSet (setPred p * setPred q)
==  predSet (\ w -> bigSumQ (u,v BR w == u <> v) setPred p u * setPred q v)  -- |(*)| on functions
==  predSet (\ w -> bigSumQ (u,v BR w == u <> v) (u <# p) * (v <# q))        -- |setPred| definition (twice)
==  predSet (\ w -> bigOrQ (u,v BR w == u <> v) u <# p && v <# q)            -- |(+)| and |(*)| on |Bool|
==  set (w # bigOr (u,v) w == u <> v && u <# p && v <# q)                    -- |predSet| definition
==  set (u <> v # u <# p && v <# q)                                          -- set notation
==  p * q                                                                    -- |(*)| on sets
\end{code}

%else

%% Try again in a different style:

\begin{code}
    predSet (setPred p * setPred q)
==  predSet (bigSum (u,v) u <> v +-> setPred p u * setPred q v)  -- |(*)| on functions
==  predSet (bigUnion (u,v) u <> v +-> u <# p && v <# q)         -- |setPred| definition
==  set (u <> v # u <# p && v <# q)                              -- |predSet| definition and simplification
==  p * q
\end{code}

%endif

For |StarSemiring| the default recursive definition embodies the star semiring law.
\note{Hm. Assuming not bottom?}

%% \subsection{\thmref{Map}}\prooflabel{theorem:Map}

\subsection{\lemref{decomp ([c] -> b)}}\prooflabel{lemma:decomp ([c] -> b)}

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
==  atEps (\ NOP case {NOP [] -> b NOP ; NOP c:cs -> h c cs NOP})  -- |(<:)| definition
==  (\ NOP case {NOP [] -> b NOP ; NOP c:cs -> h c cs NOP}) []     -- |atEps| definition
==  b                                                              -- semantics of |case|
\end{code}
\vspace{-4ex}
\begin{code}
    deriv (b <: h)
==  deriv (\ NOP case {NOP [] -> b NOP ; NOP c:cs -> h c cs NOP})                  -- |(<:)| definition
==  \ c -> \ cs -> (\ NOP case {NOP [] -> b NOP ; NOP c:cs -> h c cs NOP}) (c:cs)  -- |deriv| definition
==  \ c -> \ cs -> h c cs                                                          -- semantics of |case|
==  h                                                                              -- $\eta$ reduction (twice)
\end{code}

\subsection{\lemref{atEps [c] -> b}}\prooflabel{lemma:atEps [c] -> b}

\begin{code}
    atEps zero
==  atEps (\ a -> zero)  -- |zero| on functions
==  (\ a -> zero) []     -- |atEps| definition
==  zero                 -- $\beta$ reduction
\end{code}

\begin{code}
    atEps one
==  atEps (mempty +-> one)                              -- |one| on functions
==  atEps (\ b -> if b == mempty then one else zero)    -- |(+->)| on functions
==  atEps (\ b -> if b == mempty then True else False)  -- |one| and |zero| on |Bool|
==  atEps (\ b -> b == mempty)                          -- property of |if|
==  mempty == mempty                                    -- |atEps| definition            
==  one
\end{code}

\begin{code}
    atEps (f <+> g)
==  atEps (\ a -> f a <+> g a)  -- |(<+>)| on functions
==  (\ a -> f a <+> g a) []     -- |atEps| definition
==  f [] <+> g []               -- $\beta$ reduction
==  atEps f <+> atEps g         -- |atEps| definition
\end{code}

\begin{code}
    atEps (f <.> g)
==  atEps (bigSum (u,v) u <> v +-> f u <.> g v)               -- |(<.>)| on functions
==  atEps (\ w -> bigSumQ (u,v BR u <> v == []) f u <.> g v)  -- alternative definition from \figref{monoid semiring}
==  bigSumKeys (u,v BR u == [] && v == []) NOP f u <.> g v    -- |u <> v == [] <=> u == [] && v == []| 
==  f [] <.> g []                                             -- singleton sum
==  atEps f <.> atEps g                                       -- |atEps| definition
\end{code}

%if False

\begin{code}
    atEps (star p)
==  atEps (one <+> p <.> star p)        -- defining property of |star|
==  one <+> atEps p <.> atEps (star p)  -- |atEps| is a semiring homomorphism (above)
==  one <+> atEps p <.> star (atEps p)  -- \note{coinduction?}
==  star (atEps p)                      -- defining property of |star|
\end{code}

%else
%% \note{For the |star p| proof, maybe instead show inductively that |atEps (p^n) == (atEps p)^n| for all |n >= 0|, and then appeal to the summation definition of |star p|.}

\begin{code}
    atEps (star p)
==  atEps (bigSum i @@ p^i)  -- alternative |star p| formulation
==  bigSum i @@ (atEps p)^i  -- |atEps| is a semiring homomorphism (above)
==  star (atEps p)           -- defining property of |star|
\end{code}

%endif

\begin{code}
    atEps (s .> f)
==  atEps (\ a -> s * f a)  -- |(.>)| on functions
==  (\ a -> s * f a) []     -- |atEps| definition
==  s * f []                -- $\beta$ reduction
==  s * atEps f             -- |atEps| definition
\end{code}

%if False
\begin{code}
    atEps (w +-> b)
==  atEps (\ w' -> if w' == w then b else zero)  -- |(+->)| on |[c] -> b|
==  (\ w' -> if w' == w then b else zero) []     -- |atEps| definition
==  if [] == w then b else zero                  -- $\beta$ reduction
==  if null w then b else zero                   -- |null| definition
\end{code}
%else

\begin{code}
    atEps ([] +-> b)
==  atEps (\ w -> if w == [] then b else zero)      -- |(+->)| on |[c] -> b|
==  (\ w -> if w == [] then b else zero) []         -- |atEps| definition
==  if [] == [] then b else zero                    -- $\beta$ reduction
==  b                                               -- |if True|
    
    atEps (c':cs' +-> b)
==  atEps (\ w -> if w == c':cs' then b else zero)  -- |(+->)| on |[c] -> b|
==  (\ w -> if w == c':cs' then b else zero) []     -- |atEps| definition
==  if [] == c':cs' then b else zero                -- $\beta$ reduction
==  zero                                            -- |if False|
\end{code}

%endif

\subsection{\lemref{deriv [c] -> b}}\prooflabel{lemma:deriv [c] -> b}

\begin{code}
    deriv zero
==  deriv (\ w -> zero)                  -- |zero| on functions
==  \ c -> \ cs -> (\ w -> zero) (c:cs)  -- |deriv| on functions
==  \ c -> \ cs -> zero                  -- $\beta$ reduction
==  \ c -> zero                          -- |zero| on functions
==  zero                                 -- |zero| on |a -> b|
\end{code}
\vspace{-3ex}

\begin{code}
    deriv one
==  deriv (single mempty)                -- |one| on functions
==  \ c -> \ cs -> single mempty (c:cs)  -- |deriv| on functions
==  \ c -> \ cs -> zero                  -- |c:cs /= mempty|
==  \ c -> zero                          -- |zero| on functions
==  zero                                 -- |zero| on |a -> b|
\end{code}
\vspace{-3ex}

\begin{code}
    deriv (f <+> g)
==  deriv (\ w -> f w <+> g w)                        -- |(<+>)| on functions
==  \ c -> \ cs -> (\ w -> f w <+> g w) (c:cs)        -- |deriv| on functions
==  \ c -> \ cs -> f (c:cs) <+> g (c:cs)              -- $\beta$ reduction
==  \ c -> (\ cs -> f (c:cs)) <+> (\ cs -> g (c:cs))  -- |(<+>)| on functions
==  \ c -> deriv f c <+> deriv g c                    -- |deriv| on functions
==  deriv f <+> deriv g                               -- |(<+>)| on |a -> b|
\end{code}

%format bigSumA (lim) = "\bigOp\sum{" lim "}{1}"
\begin{code}
    deriv (f <.> g)
==  deriv (bigSum (u,v) u <> v +-> f u <.> g v)                                                                             -- |(<.>)| on functions
==  deriv (bigSum v (mempty <> v +-> f mempty <.> g v) <+> bigSumQ (c',u',v) ((c':u') <> v +-> f (c':u') <.> g v))          -- empty vs nonempty |u|
==  deriv (bigSum v (mempty <> v +-> f mempty <.> g v)) <+> deriv (bigSumA (c',u',v) ((c':u') <> v +-> f (c':u') <.> g v))  -- additivity of |deriv| (above)
\end{code}
First addend:
\begin{code}
    deriv (bigSum v (mempty <> v +-> f mempty <.> g v))
==  deriv (bigSum v (v +-> f mempty <.> g v))          -- monoid law
==  deriv (f mempty .> bigSum v (v +-> g v))           -- distributivity (semiring law)
==  \ c -> deriv (f mempty .> bigSum v (v +-> g v)) c  -- $\eta$ expansion
==  \ c -> f mempty .> deriv (bigSum v v +-> g v) c    -- additivity of |deriv| (above)
==  \ c -> f mempty .> deriv g c                       -- \lemref{decomp +->}
==  \ c -> atEps f .> deriv g                          -- |atEps| on functions
==  fmap (atEps f NOP .>) (deriv g c)                  -- |fmap| on functions
\end{code}
Second addend:
\begin{code}
    deriv (bigSumA (c',u',v) ((c':u') <> v +-> f (c':u') <.> g v))
==  bigSumA (c',u',v) deriv ((c':u') <> v +-> f (c':u') <.> g v)    -- additivity of |deriv|
==  bigSumA (c',u',v) deriv (c' : (u' <> v) +-> f (c':u') <.> g v)  -- |(<>)| on lists
==  \ c -> bigSum (u',v) u' <> v +-> f (c:u') <.> g v               -- |deriv| on |(+->)| below
==  \ c -> bigSum (u',v) u' <> v +-> (\ cs -> f (c:cs)) u' <.> g v  -- $\beta$ expansion
==  \ c -> \ cs -> f (c:cs) <.> g                                   -- |(<.>)| on functions
==  \ c -> deriv f c <.> g                                          -- |deriv| on functions
==  fmap (<.> NOP g) (deriv f)                                      -- |fmap| on functions
\end{code}
Combining addends,
\begin{code}
deriv (f <.> g) == fmap (atEps f NOP) (deriv g) <+> fmap (<.> NOP g) (deriv f)
\end{code}
\noindent
Continuing with the other equations in \lemref{deriv [c] -> b},
\begin{code}
    deriv (star p)
==  deriv (one <+> p <.> star p)                                 -- star semiring law
==  deriv one <+> deriv (p <.> star p)                           -- additivity of |deriv| (above)
==  deriv (p <.> star p)                                         -- |deriv one == zero| (above)
==  \ c -> atEps p .> deriv (star p) c <+> deriv p c <.> star p  -- |deriv (p * q)| above
==  \ c -> star (atEps p) .> deriv p c <.> star p                -- \lemref{affine over semimodule}
==  fmap (\ d -> star (atEps p) .> d <.> Star p) (deriv p)       -- |fmap| on functions
\end{code}

\begin{code}
    deriv (s .> f)
==  deriv (\ w -> s * f w)                  -- |(.>)| on functions
==  \ c -> \ cs -> (\ w -> s * f w) (c:cs)  -- |deriv| definition
==  \ c -> \ cs -> s * f (c:cs)             -- $\beta$ reduction
==  \ c -> s .> (\ cs -> f (c:cs))          -- |(.>)| on functions
==  \ c -> s .> deriv f c                   -- |deriv| definition
==  fmap (s NOP .>) (deriv f)               -- |fmap| on functions
\end{code}

\begin{code}
    deriv ([] +-> b) c
==  deriv (\ w -> if w == [] then b else zero)           -- |(+->)| on functions
==  \ cs -> (\ w -> if w == [] then b else zero) (c:cs)  -- |deriv| definition
==  \ cs -> if c:cs == [] then b else zero               -- $\beta$ reduction
==  \ cs -> zero                                         -- |c:cs /= []|
==  zero                                                 -- |zero| on functions

    deriv (c':cs' +-> b)
==  deriv (\ w -> if w == c':cs' then b else zero)                            -- |(+->)| on functions
==  \ c -> \ cs -> (\ w -> if w == c':cs' then b else zero) (c:cs)            -- |(+->)| on functions
==  \ c -> \ cs -> if c:cs == c':cs' then b else zero                         -- $\beta$ reduction
==  \ c -> \ cs -> if c == c' && cs == cs' then b else zero                   -- |(:)| injectivity
==  \ c -> \ cs -> if c == c' then (if cs == cs' then b else zero) else zero  -- property of |if| and |(&&)|
==  \ c -> if c == c' then (\ cs -> if cs == cs' then b else zero else zero)  -- property of |if|
==  \ c -> if c == c' then cs' +-> b else zero                                -- |(+->)| on functions
==  c' +-> cs' +-> b                                                          -- |(+->)| on |s -> t|

\end{code}

\subsection{\thmref{semiring decomp [c] -> b}}\prooflabel{theorem:semiring decomp [c] -> b}

\begin{code}
    zero
==  atEps zero <: deriv zero  -- \lemref{decomp ([c] -> b)}
==  zero <: \ c -> zero       -- \lemreftwo{atEps [c] -> b}{deriv [c] -> b}
==  zero <: zero              -- |zero| on functions
\end{code}

\begin{code}
    one
==  atEps one <: deriv one  -- \lemref{decomp ([c] -> b)}
==  one <: \ c -> zero      -- \lemreftwo{atEps [c] -> b}{deriv [c] -> b}
==  one <: zero             -- |zero| on functions
\end{code}

\begin{code}
    (a <: dp) <+> (b <: dp)
==  atEps ((a <: dp) <+> (b <: dq)) <: deriv ((a <: dp) <+> (b <: dq))  -- \lemref{decomp ([c] -> b)}
==  a <+> b <: dp <+> dq                                                -- \lemref{atEps and deriv via (<:)} below
\end{code}

%% (a  <:  dp)  <.>  q == a .> q <+> (zero <: (<.> NOP q) . dp)

\begin{code}
    (a <: dp) <.> (b <: dq)
==  atEps ((a <: dp) <.> (b <: dq)) <: deriv ((a <: dp) <.> (b <: dq))        -- \lemref{decomp ([c] -> b)}
==  a <.> b <: \ c -> a .> dq c <+> dp c <.> (b <: dq)                        -- \lemref{atEps and deriv via (<:)} below
==  (a <.> b <+> zero) <: (\ c -> a .> dq c) <+> (\ c -> dp c <.> (b <: dq))  -- additive identity; |(<+>)| on functions
==  (a <.> b <: \ c -> a .> dq c) <+> (zero <: \ c -> dp c <.> (b <: dq))     -- previous result
==  a .> (b <: dq) <+> (zero <: \ c -> dp c <.> (b <: dq))                    -- |(.>)| case below
==  a .> (b <: dq) <+> (zero <: (<.> NOP (b <: dq)) . dp)                     -- |(.)| definition
==  a .> (b <: dq) <+> (zero <: fmap (<.> NOP (b <: dq)) dp)                  -- fmap on functions
\end{code}

%% \lemref{atEps and deriv via (<:)}

%% star (a <: dp) = q where q = star a .> (one <: (<.> NOP q) .  dp)

%% deriv (star p) c == star (atEps p) .> deriv p c <.> star p

%% deriv (star (a <: dp)) c == star a .> dp c * star (a <: dp)  -- {atEps and deriv via (<:)}

\begin{code}
    star (a <: dp)
==  atEps (star (a <: dp)) <: deriv (star (a <: dp))      -- \lemref{decomp ([c] -> b)}
==  star a <: \ c -> star a .> dp c * star (a <: dp)      -- \lemref{atEps and deriv via (<:)} below
==  star a .> (one <: \ c -> dp c * star (a <: dp))       -- |(.>)| case below
==  star a .> (one <: fmap (* NOP @@ star (a <: dp)) dp)  -- |fmap| on functions
\end{code}

\begin{code}
    s .> (b <: h)
==  atEps (s .> (b <: h)) <: deriv (s .> (b <: h))  -- \lemref{decomp ([c] -> b)}
==  s * b <: \ c -> s .> dp c                       -- \lemref{atEps and deriv via (<:)} below
==  s * b <: (s .>) . dp                            -- |(.)| definition
==  s * b <: fmap (s NOP .>) dp                     -- |fmap| on functions
\end{code}

\begin{code}
    [] +-> b
==  atEps ([] +-> b) <: deriv ([] +-> b)               -- \lemref{decomp ([c] -> b)}
==  b <: \ c -> zero                                   -- \lemreftwo{atEps [c] -> b}{deriv [c] -> b}
==  b <: zero                                          -- |zero| on functions

    c':cs' +-> b
==  atEps (c':cs' +-> b) <: deriv (c':cs' +-> b)       -- \lemref{decomp ([c] -> b)}
==  zero <: \ c -> if c = c' then cs' +-> b else zero  -- \lemreftwo{atEps [c] -> b}{deriv [c] -> b}
==  zero <: c' +-> cs' +-> b                           -- |(+->)| on functions
\end{code}
Expressed via |foldr|,

> w +-> b = foldr (\ c t -> zero <: c +-> t) (b <: zero) w

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
\vspace{-2ex}
\end{lemma}
\begin{proof}
Substitute into \lemreftwo{atEps [c] -> b}{deriv [c] -> b}, and simplify, using \lemref{decomp ([c] -> b)}.
\end{proof}

%% \subsection{\thmref{semiring decomp generalized}}\prooflabel{theorem:semiring decomp generalized}

\subsection{\thmref{Cofree}}\prooflabel{theorem:Cofree}

The theorem follows from \thmref{semiring decomp [c] -> b}.
A few details:

\begin{spacing}{1.2}

\begin{code}
    (!) zero 
==  (!) (zero :< zero)      -- |zero| for |Cofree c b|
==  zero <: (!) . (!) zero  -- |(!)| for |Cofree c b|
==  zero <: (!) . zero      -- Additive functor assumption
==  zero <: zero            -- coinduction
==  zero                    -- \thmref{semiring decomp [c] -> b}
\end{code}

\begin{code}
    (!) ((a :< dp) + (b :< dq))
==  (!) (a + b :< dp + dq)                                  -- |(+)| on |Cofree c b|
==  a + b <: (!) . (!) (dp + dq)                            -- |(!)| on |Cofree c b|
==  a + b <: (!) . ((!) dp + (!) dq)                        -- |Indexable| law
==  a + b <: (!) . (\ cs -> dp ! cs + dq ! cs)              -- |(+)| on functions
==  a + b <: \ cs -> (!) (dp ! cs + dq ! cs)                -- |(.)| definition
==  a + b <: \ cs -> (!) (dp ! cs) + (!) (dq ! cs)          -- |Indexable| law
==  a + b <: \ cs -> ((!) . (!) dp) cs + ((!) . (!) dq) cs  -- |(.)| definition
==  a + b <: ((!) . (!) dp) + ((!) . (!) dq)                -- |(+)| on functions
==  (a :< (!) . (!) dp) + (b :< (!) . (!) dq)               -- |(+)| on |Cofree c b|
==  (!) (a :< dp) + (!) (b :< dq)                           -- |(!)| on |Cofree c b|
\end{code}

%if True

Similarly for the other

%else


\note{Fill in from journal notes of 2019-02-14. It's a straightforward application of \thmref{semiring decomp [c] -> b}.}

\note{Coinduction?}

\workingHere


\begin{code}
    (!) (s .> (a :< dp))
==  (!) (s * a :< fmap (s NOP .>) dp)        -- |(.>)| and |Functor| (derived) on |Cofree|
==  s * a <: (!) . (!) (fmap (s NOP .>) dp)  -- |(!)| on |Cofree c b|
==  s * a <: (!) . (s NOP .>) . (!) dp       -- |Indexable| law
==  ...



==  s * a <: (s NOP .>) . ((!) (a <: dp))
==  s * a <: fmap (s NOP .>) ((!) (a <: dp))
==  s .> (!) (a <: dp)
\end{code}

\begin{code}
    (!) ((a :< dp) * (b :< dq))
==  (!) (a .> q + (zero :< fmap (<.> NOP q) dp))
==  (!) (a .> q) + (!) (zero :< fmap (<.> NOP q) dp)
==  (!) (a .> q) + (zero <: (!) . (!) (fmap (<.> NOP q) dp))
==  (!) (a .> q) + (zero <: (!) . (<.> NOP q) . (!) dp)

==  ...
==  (!) (a :< dp) * (!) (b :< dq)
\end{code}

%endif

\end{spacing}

\subsection{\thmref{Cofree hom}}\prooflabel{theorem:Cofree hom}

First show that |(!)| is natural (a functor homomorphism):

> (!) (fmap f (a :< ds)) = fmap f ((!) (a :< ds))

i.e.,

> fmap f (a :< ds) ! cs = fmap f ((!) (a :< ds)) cs

Consider cases for |cs|:

\begin{code}

    fmap f (a :< ds) ! []
==  f a :< (fmap (fmap f) ds) ! []  -- |fmap| on |Cofree h|
==  f a                             -- |(!)| on |Cofree h|

    fmap f ((!) (a :< ds)) []
==  (f . (!) (a :< ds)) []          -- |fmap| on functions
==  f ((a :< ds) ! [])              -- |(.)| definition
==  f a                             -- |(!)| on |Cofree h|

    fmap f (a :< ds) ! (c:cs')
==  f a :< fmap (fmap f) ds ! (c:cs')  -- |fmap| on |Cofree h|
==  fmap (fmap f) ds ! c ! cs          -- |(!)| on |Cofree h|
==  fmap f (ds ! c) ! cs               -- |(!)| on |h| is natural
==  f (ds ! c ! cs)                    -- |(!)| on |h| is natural

    fmap f ((!) (a :< ds)) (c:cs')
==  (f . (!) (a :< ds)) (c:cs')        -- |fmap| on functions
==  f ((a :< ds) ! (c:cs'))            -- |(.)| definition
==  f (ds ! c ! cs')                   -- |(!)| on |Cofree h|

\end{code}
Next show that

> coreturn (a :< ds) == coreturn ((!) (a :< ds))

\begin{code}

    coreturn ((!) (a :< ds))
==  ((!) (a :< ds)) mempty
==  (a :< ds) ! mempty
==  a
==  coreturn (a :< ds)

\end{code}
Finally,

> (!) . fmap (!) . cojoin == cojoin . (!)

i.e.,

> fmap (!) (cojoin (a :< ds)) ! cs == cojoin ((!) (a :< ds)) cs

\begin{code}

    fmap (!) (cojoin (a :< ds)) ! []
==  fmap (!) ((a :< ds) :< fmap cojoin ds) ! []               -- |cojoin| on |Cofree h|
==  ((!) (a :< ds) :< fmap (fmap (!)) (fmap cojoin ds)) ! []  -- |fmap| on |Cofree h|
==  (!) (a :< ds)                                             -- |(!)| on |Cofree h|

    cojoin ((!) (a :< ds)) []
==  (\ u -> \ v -> (a :< ds) ! (u <> v)) []  -- |cojoin| on functions
==  \ v -> (a :< ds) ! (mempty <> v)         -- $\beta$ reduction
==  \ v -> (a :< ds) ! v                     -- |Monoid| law
==  (!) (a :< ds)                            -- $\eta$ reduction


    fmap (!) (cojoin (a :< ds)) ! (c:cs')
==  fmap (!) ((a :< ds) :< fmap cojoin ds) ! (c:cs')               -- |cojoin| on |Cofree h|
==  ((!) (a :< ds) :< fmap (fmap (!)) (fmap cojoin ds)) ! (c:cs')  -- |fmap| on |Cofree h|
==  fmap (fmap (!)) (fmap cojoin ds) ! c ! cs'                     -- |(!)| on |Cofree h|
==  fmap (fmap (!) . cojoin) ds ! c ! cs'                          -- |Functor| law
==  ...                                                            -- \note{working here}
==  cojoin ((!) (a :< ds)) (c:cs')
==  (\ u -> \ v -> (a :< ds) ! (u <> v)) (c:cs')                   -- |cojoin| on functions
==  \ v -> (a :< ds) ! ((c:cs') <> v)                              -- $\beta$ reduction
==  \ v -> (a :< ds) ! (c : (cs' <> v))                            -- |(<>)| on |[c]|
==  \ v -> ds ! c ! (cs' <> v)                                     -- |(!)| on |Cofree h|

\end{code}

\subsection{\thmref{pre hom}}\prooflabel{theorem:pre hom}

\begin{spacing}{1.2}
\begin{code}

    pre (pure b)
==  pre (\ a -> b)                                                               -- |pure| on |a -> b|
==  F (\ b' -> set (a # b == b'))                                                -- |pre| definition
==  F (\ b' -> if b' == b then set (a # True) else set (a # False))              -- case split
==  F (\ b' -> if b' == b then one else zero)                                    -- |one| and |zero| for |Pow a| (revised in \figref{-> and <-- semirings})
==  b +-> 1                                                                      -- |(+->)| definition
==  pure b                                                                       -- |pure| for |Pow a <-- b|

    pre (fmap h f)
==  pre (\ a -> h (f a))                                                         -- |fmap| on |a -> b|
==  F (\ c -> set (a # h (f a) == c))                                            -- |pre| definition
==  F (\ c -> set (a # exists b. f a == b && h b == c))                          -- intermediate variable
==  F (\ c -> bigUnion (b BR h b == c) @@ set (a # f a == b))                    -- logic/sets
==  F (\ c -> bigUnion (b BR h b == c) @@ pre f b)                               -- |pre| definition
==  F (\ c -> bigSum (b BR h b == c) @@ pre f b)                                 -- |(+)| on |Pow a|
==  fmap h (pre f)                                                               -- |fmap| on |Pow a <-- b|

    pre (liftA2 h f g)
==  pre (\ a -> h (f a) (g a))                                                   -- |liftA2| on |a -> b|
==  \ c -> { a | h (f a) (g a) == c }                                            -- |pre| definition
==  \ c -> { a | exists x y. x == f a && y == g a && h x y == c }                -- intermediate variables
==  \ c -> { a | exists x y. a <# pre f x && a <# pre g y && h x y == c }        -- |pre| definition (twice)
==  \ c -> { a | exists x y. a <# (pre f x `intersect` pre g y) && h x y == c }  -- |`intersect`| definition
==  bigUnion (x,y) h x y +-> pre f x `intersect` pre g y                         -- logic/sets
==  bigUnion (x,y) h x y +-> pre f x * pre g y                                   -- |(*)| on |Pow a| (revised in \figref{-> and <-- semirings})
==  bigSum (x,y) h x y +-> pre f x * pre g y                                     -- |(+)| on |Pow a <-- b|
==  liftA2 h (pre f) (pre g)

\end{code}
\end{spacing}


\subsection{\thmref{standard FunApp}}\prooflabel{theorem:standard FunApp}

First consider |fmap|, as defined in \figref{FunApp}.
\begin{code}
    fmap h (F f)
==  bigSum u h u +-> f u          -- definition of |fmap| on |(<--) b|
==  bigSum u h u +-> f u * one    -- multiplicative identity
==  bigSum u f u .> (h u +-> one) -- \lemref{+-> homomorphism}
==  bigSum u f u .> single (h u)  -- definition of |single|
==  bigSum u f u .> pure (h u)    -- |single = pure|
==  F f >>= pure . h              -- definition of |(>>=)|
\end{code}
\noindent
Similarly for |liftA2|:
\vspace{-1ex}
\begin{spacing}{1.5}
\begin{code}
    liftA2 h (F f) (F g)
==  bigSum (u,v) h u v +-> f u <.> g v              -- definition of |liftA2|
==  bigSum (u,v) (f u * g v) .> single (h u v)      -- as above
==  bigSum (u,v) f u .> (g v .> single (h u v))     -- associativity
==  bigSum u f u .> bigSum v g v .> single (h u v)  -- linearity
==  bigSum u f u .> bigSum v h u v +-> g v          -- as above
==  bigSum u f u .> fmap (h u) (F g)                -- definition of |fmap|
==  F f >>= \ u -> fmap (h u) (F g)                 -- definition of |(>>=)|
==  F f >>= \ u -> F g >>= \ v -> pure (h u v)      -- above
\end{code}
\end{spacing}

%if otherApps

\subsection{\thmref{poly hom}}\prooflabel{theorem:poly hom}

\begin{code}
    poly zero
==  poly (F (\ i -> zero))         -- |zero| on |b <-- a| (derived)
==  \ x -> bigSum i  zero <.> x^i  -- |poly| definition
==  \ x -> bigSum i  zero          -- |zero| as annihilator
==  \ x -> zero                    -- |zero| as additive identity
==  zero                           -- |zero| on functions
\end{code}

\begin{code}
    poly one
==  poly (pure mempty)                                          -- |one| on |b <-- a|
==  poly (F (\ i -> if i == mempty then one else zero))         -- |pure| on |(<--) b|
==  poly (F (\ i -> if i == Sum 0 then one else zero))          -- |mempty| on |N|
==  \ x -> bigSum i (if i == Sum 0 then one else zero) <.> x^i  -- |poly| definition
==  \ x -> bigSum i (if i == Sum 0 then x^i else zero)          -- simplify
==  \ x -> x^0                                                  -- other terms vanish
==  \ x -> one                                                  -- multiplicative identity
==  one                                                         -- |one| on |a -> b|
\end{code}

\begin{code}
    poly (F f <+> F g)
==  poly (F (\ i -> f i <+> g i))                               -- |(<+>)| on |b <-- a| (derived)
==  \ x -> bigSum i  (f i <+> g i) <.> x^i                      -- |poly| definition
==  \ x -> bigSum i  f i <.> x^i <+> g i <.> x^i                -- distributivity
==  \ x -> (bigSum i  f i <.> x^i) <+> (bigSum i  g i <.> x^i)  -- summation property
==  \ x -> poly (F f) x <+> poly (F g) x                        -- |poly| definition
==  poly (F f) <+> poly (F g)                                   -- |(<+>)| on |a -> b|
\end{code}

\begin{code}
    poly (F f <.> F g)
==  poly (liftA2 (<>) (F f) (F g))                              -- |(<.>)| on |b <-- a|
==  poly (bigSum (i,j)  i <> j +-> f i <.> g j)                 -- |liftA2| on |b <-- a|
==  poly (bigSum (i,j)  i + j +-> f i <.> g j)                  -- |(<>)| on |N|
==  bigSum (i,j)  poly (i + j +-> f i <.> g j)                  -- additivity of |poly| (previous property)
==  bigSum (i,j) (\ x -> (f i <.> g j) <.> pow x (i + j))       -- \lemref{poly +->} below
==  \ x -> bigSum (i,j) (f i <.> g j) <.> pow x (i + j)         -- |(<+>)| on functions
==  \ x -> bigSum (i,j) (f i <.> g j) <.> (x^i <.> x^j)         -- exponentiation property
==  \ x -> bigSum (i,j) (f i <.> x^i) <.> (g j <.> x^j)         -- commutativity assumption
==  \ x -> (bigSum i  f i <.> x^i) <.> (bigSum j  g j <.> x^j)  -- summation property
==  \ x -> poly (F f) x <.> poly F g) x                         -- |poly| definition
==  poly (F f) <.> poly F g)                                    -- |(<.>)| on functions
\end{code}

%% \note{The sum and product derivations might read more easily in reverse.}

\begin{lemma}\lemlabel{poly +->}~
\begin{code}
poly (n +-> b) = \ x -> b * x^n
\end{code}
\end{lemma}
\begin{proof}~
\begin{code}
poly (n +-> b)
poly (F (\ i -> if i == n then b else zero))          -- |(+->)| on |b <-- a| (derived)
\ x -> bigSum i (if i == n then b else zero) <.> x^n  -- |poly| definition
\ x -> b * x^n                                        -- other terms vanish
\end{code}
\end{proof}

\subsection{\lemref{pows hom}}\prooflabel{lemma:pows hom}

\begin{code}
    pows x zero
==  bigProd i @@ pow (x i) (zero i)  -- |(^^)| definition
==  bigProd i @@ pow (x i) zero      -- |zero| on functions
==  bigProd i one                    -- exponentiation law
==  one                              -- multiplicative identity
\end{code}

\begin{code}
    pows x (p + q)
==  bigProd i @@ pow (x i) ((p + q) i)                                           -- |(^^)| definition
==  bigProd i @@ pow (x i) (p i + q i)                                           -- |(+)| on functions
==  bigProd i @@ (pow (x i) (p i)) * (pow (x i) (q i))                           -- exponentiation law (with commutative |(*)|)
==  paren (bigProd i @@ pow (x i) (p i)) * paren (bigProd i @@ pow (x i) (q i))  -- product property (with commutative |(*)|)
==  pows x p * pows x q                                                          -- |(^^)| definition
\end{code}

%endif otherApps

%endif long

\bibliography{bib}

\end{document}
