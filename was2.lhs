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
Using the perspective of semirings and free semimodules, this paper explores formal languages and derives algorithms for language recognition (matching) that correspond to a method of Brzozowski, while generalizing this method to a broader setting, including counted and weighted ``languages''.

Although Brzozowski formulated his method in terms of regular expressions, free semimodules appear to be a more natural and general setting.
Regular expressions become a special case, while \emph{tries} offer a natural alternative that appears to be simpler and more efficient.
Rather than constructing a grammatical representation that gets successively ``differentiated'' in Brzozowski's method, the standard notion of trie already has derivatives built in, saving much redundant work without the need for explicit memoization.
Since tries generalize elegantly from sets to functions and from strings to algebraic data types, the essential theory and algorithms extend far beyond languages in the sense of sets of strings.
Underlying these variations is a notion of generalized convolution, which itself (along with probabilistic computation) generalizes to the free semimodule monad.
This paper shows how to perform (generalized) convolution efficiently and easily, in one dimension or many, on time or space and on languages.
Aside from applications in image processing and machine learning, a simple and direct application of convolution is multiplication of polynomials, again in one or many dimensions (i.e., univariate or multivariate).
All of the algorithms in the paper follow from very simple specifications in the form of semiring homomorphisms that relate different representations.

\end{abstract}

\sectionl{Introduction}

%format <+> = +
%format <.> = *
%% %format zero = 0
%% %format one = 1
%format zero = "\mathbf{0}"
%format one = "\mathbf{1}"

%format `elem` = "\mathbin{`\Varid{elem}`}"
%format <# = "\mathop{\in}"
%format # = "\mid"

%format (paren (e)) = "\left(" e "\right)"

%format Pow = "\Pow"
%format emptyset = "\emptyset"
%format (single (s)) = "\single{"s"}"
%format (set (e)) = "\set{"e"}"
%format bigunion (lim) (body) = "\bigunion_{" lim "}{" body "}"
%format pow a (b) = a "^{" b "}"
%format `union` = "\cup"
%format star p = "\closure{"p"}"

\sectionl{Languages}

A \emph{language} is a set of strings, where a string is a sequence of values of some given type (``symbols'' from an ``alphabet'').
Languages are commonly built up via a few simple operations:
\notefoot{Maybe use the standard terminology |zero|, |(<+>)|, |(<.>)|, and |star| here.}
\begin{itemize}
\item The \emph{empty} language |zero = set ()|.
\item For a string |s|, the \emph{singleton} language |single s = set s|.
\item For two languages |p| and |q|, the \emph{union} |p <+> q = set (u # u <# p || u <# q)|.
\item For two languages |p| and |q|, the element-wise \emph{concatenation} |p <.> q = set (u <> v # u <# p && v <# q)|, where ``|<>|'' denotes string concatenation.
\item For a language |p|, the \emph{closure} |star p = bigunion (n > 0) (pow p n)|, where |pow p n| is |p| concatenated with itself |n| times.
\end{itemize}
These operations suffice to describe all \emph{regular} languages.
The language specifications (language-denoting \emph{expressions} rather than languages themselves) finitely constructed from these operations are called \emph{regular expressions}.
%(If we allow \emph{recursive} definitions, we get \emph{context-free} languages.)

Some observations:
\begin{itemize}
\item Union is associative, with |zero| as its identity.
      \notefoot{Maybe state equations for this observations and the next two.}
\item Element-wise concatenation is associative and commutative, with |single mempty| as its identity, where |mempty| is the empty string.
\item Left- and right-concatenation distribute over union.
\item The empty language annihilates under concatenation, i.e., |p <.> zero = zero <.> q = zero|.
\item The closure operation satisfies the equation |star p = mempty <+> p <.> star p|.\footnote{Syntactically, we'll take ``|<.>|'' to bind more tightly than ``|<+>|'', so the RHS of this definition is equivalent to |mempty <+> (p <.> star p)|}
\end{itemize}
These observations are the defining properties of a \emph{star semiring} (also called a \emph{closed semiring}) \needcite{}.
\figrefdef{classes}{Abstract interface for languages (and later generalizations)}{
\begin{code}
class Semiring a where
  infixl 7 <.>
  infixl 6 <+>
  zero    , one    :: a
  (<+>)   , (<.>)  :: a -> a -> a

class Semiring a => StarSemiring a where
  star :: a -> a
  star p = q where q = one <+> p <.> q  -- default

class HasSingle a w | a -> w where
  single :: w -> a
\end{code}
\vspace{-4ex}
} shows Haskell classes for representations of languages (and later generalizations), combining the star semiring vocabulary (from the semiring-num library \citep{semiring-num}) with an operation for singletons.
\notefoot{Consider replacing |HasSingle| with |Pointed| (and |single| with |point|).}
The singleton-forming operation must satisfy the following properties:
\begin{align*}
\single \mempty &= \one \\
\single {u \mappend v} &= \single u \conv \single v
\end{align*}
i.e., |single| is a monoid homomorphism (targeting the product monoid).

The semiring and star semiring interfaces have corresponding notions of structure preservation:
\begin{definition}
A function |h| from one semiring to another is called \emph{semiring homomorphism} when the following conditions hold:
\begin{code}
h zero == zero
h one == one
forall a b NOP . NOP h (a  <+>  b) == h a  <+>  h b
forall a b NOP . NOP h (a  <.>  b) == h a  <.>  h b
\end{code}
\end{definition}
\begin{definition}
A function |h| from one \emph{star} semiring to another is called \emph{star semiring homomorphism} when |h| is a semiring homomorphism and the following additional condition holds:
\begin{code}
forall a NOP . NOP h (star a) == star (h a)
\end{code}
\end{definition}
\note{Explain the value of homomorphisms to the methodology of this paper: simple and consistent specification style, non-leaky abstraction, guarantee that the laws hold. Refer to my TCM and AD papers.}

Languages as sets fulfill this combined interface as described above and again in the pseudocode in \figrefdef{set}{Mathematical sets as a ``language'' (pseudocode)}{
\begin{code}
instance Monoid s => Semiring (Pow s) where
  zero  = emptyset
  one   = single mempty
  p  <+>  q  = p `union` q
             = set (u | u <# p || u <# q)
  p  <.>  q  = set (u <> v | u <# p && v <# q)

instance StarSemiring (Pow s) where star p = bigunion (n >= 0) (pow p n)

instance HasSingle (Pow s) s where single s = set s
\end{code}
\vspace{-4ex}
}, which generalizes from strings to any monoid.\footnote{The |Monoid| class defines |mempty| and |mappend|.}
\notefoot{Perhaps postpone generalization from lists to monoids later.}
%% Data.Semiring defines instances for lists, so I'm using a newtype.
%% Hide the distinction for now at least. To do: discuss with Donnacha.
%% %format (List a) = [a]
%% %format L (as) = as
More concretely, we might instead use a type of (possibly infinite) lists, as in \figrefdef{list}{Lists as a language representation}{
\begin{code}
newtype List a = L [a]

instance Monoid a => Semiring (List a) where
  zero = L []
  one = L [mempty]
  L u  <+>  L v = L (u ++ v)
  L u  <.>  L v = L (liftA2 (<>) u v)

instance Monoid a => StarSemiring (List a)  -- default |closure a|

instance HasSingle (List a) a where single a = L [a]
\end{code}
\vspace{-4ex}
}.
Rather than using lists directly, \figref{list} defines |List a|, freeing regular lists for another interpretation.
\notefoot{Refer to a later section that treats a list as a function from |Nat|, with finite lists getting padded with |zero|.}
Lists relate to sets and other semirings as follows:
%format bigUnion (lim) = "\bigOp\bigcup{" lim "}{0}"
%format bigSum (lim) = "\bigOp\sum{" lim "}{0}"
%format bigSumQ (lim) = "\bigOp\sum{" lim "}{1.5}"
\begin{code}
elems :: (Semiring p, HasSingle p a) => [a] -> p
elems as = bigSum (a <# as) (single a)
\end{code}
%% elems (L as) = foldr insert emptyset as
%%   where insert a s = single a <+> s
The instance definitions in \figreftwo{set}{list} bear a family resemblance to each other, which we can readily make precise:
\begin{theorem}[\provedIn{theorem:list}]\thmlabel{list}
Given the definitions in \figref{list}, |elems| is a homomorphism with respect to each instantiated class.
\end{theorem}
%% Further, one can take this homomorphism property as an algebraic \emph{specifications} and \emph{calculate} the instance definitions in \figref{list}, explaining the resemblances.

\sectionl{Matching}

Now consider how we can computably \emph{match} a string for membership in a language described in the vocabulary given in the previous section.
Aside from closure, which introduces infinite languages, we could test membership in sets or lists.%
\footnote{For infinite lists, if we defined |(<+>)| via interleaving instead of concatenation, we could detect members, but not non-members.}
\out{
The set-based language definition does not lead directly to effective string matching, because the sets may be infinite.
The list and finite set types do have computable membership testing so we could use them instead.
\notefoot{Finite sets \needcite{} would not support closure, due to finiteness.}
}%
Another option is to use membership predicates \emph{as} language implementation, noting the set/predicate isomorphism:
\begin{code}
newtype Pred a = Pred (a -> Bool)

setPred :: Pow a -> Pred a
setPred as = Pred (\ a -> a <# as)

predSet :: Pred a -> Pow a
predSet (Pred f) = set (a | f a)
\end{code}
It's easy to show that |setPred . predSet == id| and |predSet . setPred == id|.
% See 2018-12-10 notes.
%format exists = "\exists"
%format bigOr (lim) = "\bigOp\bigvee{" lim "}{0}"
%format bigOrQ (lim) = "\bigOp\bigvee{" lim "}{1.5}"
%format BR = "\!\!\\\!\!"
%% %format BR = "\hspace{-5mu}\\\hspace{-5mu}"
We can require that |predSet| (and thus |setPred|) is semiring homomorphism and solve the required homomorphism equations to yield a |Semiring| instance, as shown in \figrefdef{pred}{Membership predicate as semiring (language representation)}{
\begin{code}
newtype Pred a = Pred (a -> Bool)

instance (Monoid a, Eq a) => Semiring (Pred a) where
  zero = Pred (\ w -> False)
  one = single mempty
  Pred f  <+>  Pred g = Pred (\ w -> f w || g w)
  Pred f  <.>  Pred g = Pred (\ w -> bigOr (u,v) f u && g v && u <> v == w)

instance (Monoid a, Eq a) => StarSemiring (Pred a)  -- default |closure a|

instance Eq a => HasSingle (Pred a) a where
  single w = Pred (\ w' -> w' == w)
\end{code}
\vspace{-4ex}
}.
%% %format isEmpty = "\Varid{is}_\epsilon"
%% %format splits = split
For some monoids, including lists, we can also express the product operation in a more clearly computable form via \emph{splittings}:
%format bigOrSplits (lim) = "\bigOp\bigvee{" lim "}{2.5}"
\begin{code}
  Pred f <.> Pred g = Pred (\ w -> bigOrSplits ((u,v) <# splits w) f u && g v)
\end{code}
where |splits w| yields all pairs |(u,v)| such that |u <> v == w|:
\notefoot{Maybe generalize from \emph{lists} of pairs to an associated |Foldable|.}
% \notefoot{If I don't end up using |isEmpty|, drop it here. I think it's good for avoiding unnecessary equality tests and hence |Eq| constraints.}
\begin{code}
class Monoid t => Splittable t where
  splits   :: t -> [(t,t)]  -- the inverse of |mappend|

instance Splittable [a] where
  splits []      = [([],[])]
  splits (a:as)  = ([],a:as) : [((a:l),r) | (l,r) <- splits as]
\end{code}
%%   isEmpty  :: t -> Bool     -- whether equal to |mempty|
%%   isEmpty = null
Sets and predicates have the same sort of relationship as between sets and lists (\thmref{list}), though symmetrically:
\begin{theorem}[\provedIn{theorem:pred}]\thmlabel{pred}
Given the definitions in \figref{pred}, |setPred| and |predSet| are homomorphisms (and together form an isomorphism) with respect to each instantiated class.
\end{theorem}

\sectionl{Booleans and Beyond}

For examples other than numbers and languages, \figrefdef{bool and function}{Booleans and functions as semirings}{
\begin{code}
instance Semiring Bool where
  zero  = False
  one   = True
  (<+>)  = (||)
  (<.>)  = (&&)

instance StarSemiring Bool where
  star b   = one <+> b <.> star b
           = True || (b && star b)
           = True

instance Semiring b => Semiring (a -> b) where
  zero  = \ a -> zero
  one   = \ a -> one
  f  <+>  g  = \ a -> f a <+> g a
  f  <.>  g  = \ a -> f a <.> g a

instance StarSemiring b => StarSemiring (a -> b) where
  star f = \ a -> star (f a)
\end{code}
\vspace{-4ex}
} shows instances for |Bool| and |a -> b|.
\notefoot{Maybe a theorem here saying that these instances satisfy the necessary laws. Otherwise suggest that the reader verify. I'm unsure how to prove the closure property. Perhaps coinduction. See journal notes for 2019-01-16.}
\out{We will use the |a -> b| semiring in \secref{Convolution}.\notefoot{Check that we did.}}

%format bigSumKeys (lim) = "\bigOp\sum{" lim "}{2}"
%format <-- = "\leftarrow"
%format .> = "\cdot"
%format +-> = "\mapsto"

The instances for predicates in \figref{pred} involve uses of |False|, |(||||)|, and |(&&)|, as well as an equality test (for |single w|), which yields |False| or |True|.
We can therefore easily generalize the codomain of ``predicates'' from booleans to \emph{any} semiring.
It will also be useful to generalize |single a| to |a +-> s|, mapping |a| to |s| (instead of to |one|) and everything else to zero.
We can build |a +-> s| from |single a| and a new ``scaling'' operation |s .> p|, which multiplies each codomain value in |p| by |s|:\footnote{
For sets, lists, and predicates, |s| will be |Bool|, e.g.,
\begin{code}
instance Monoid a => Scalable (List a) Bool where
  s .> as = if s then as else zero
\end{code}
\note{Maybe it's not worth bothering with |Scalable| and |(+->)| for sets, lists and predicates.}
}
\notefoot{Consider changing both |HasSingle| and |Scalable| to type \emph{constructor} classes.}
\begin{code}
class Scalable b s | b -> s where
  infixl 7 .>
  (.>) :: s -> b -> b

infix 1 +->
(+->) :: (Semiring x, Scalable x s, HasSingle x a) => a -> s -> x
a +-> s = s .> single a
\end{code}

\noindent
Laws:
\notefoot{Can I point to a more standard development of these notion and laws? For instance, I might start with semimodules (generalizing vector spaces) instead of semirings.}
\begin{code}
s .> (t  .>   p)  == (s  <.>  t)  .>   p
s .> (p  <.>  q)  == (s  .>   p)  <.>  q
\end{code}

\noindent
The |(+->)| operation gives a way to decompose arbitrary functions:
\begin{lemma}[\provedIn{lemma:decomp +->}]\lemlabel{decomp +->}
For all |f :: a -> b| where |b| is a semiring,
\begin{code}
F f == bigSum a a +-> f a
\end{code}
\end{lemma}

Since we already have a semiring of functions (\figref{bool and function}), let's refer to the generalized |Pred a| as ``|b <-- a|'', as in \figrefdef{<--}{|b <-- a| as generalized language representation}{
\begin{code}
infixl 1 <--
newtype b <-- a = F { unF :: a -> b }

instance (Semiring b, Monoid a, Eq a) => Semiring (b <-- a) where
  zero = F (\ w -> zero)
  one = single mempty
  F f  <+>  F g  = F (\ a -> f a <+> g a)
  F f  <.>  F g  = F (\ w -> bigSumQ (u,v BR u <> v == w) f u <.> g v)
                 = bigSum (u,v) (u <> v +-> f u <.> g v)

instance (Monoid a, Eq a) => StarSemiring (b <-- a)

instance (Semiring b, Eq a) => HasSingle (b <-- a) a where
  single a = F (equal a)

equal :: (Eq a, Semiring s) => a -> a -> s
equal a a' = if a == a' then one else zero

instance Semiring s => Scalable (s <-- a) s where
  s .> F f = F (\ a -> s <.> f a) 
\end{code}
\vspace{-4ex}
}.
\notefoot{If I change |HasSingle| and |Scalable| to type constructor classes, the reversal of parameters will be necessary, as it already is for |Functor|, |Applicative|, and |Monad| instances.}

\begin{theorem}[\provedIn{theorem:<--}]\thmlabel{<--}
Given the instance definitions in \figref{<--}, |b <-- a| satisfies the laws of the instantiated classes whenever |a| is a monoid and |b| is a semiring.
\end{theorem}
\noindent
When the monoid |a| is a list or other splittable type, we can again express the product operation from \figref{<--} in a more clearly computable form:
%format bigSumSplits (lim) = "\bigOp\sum{" lim "}{2.5}"
\begin{code}
  F f <.> F g  = F (\ w -> bigSumSplits ((u,v) <# splits w) f u <.> g v)
\end{code}

%format :<-- = "\leftarrowtriangle"

Another representation of functions from |a| to |b| is |Map a b|, where |Map| is an efficient representation of finite maps, i.e., partial functions defined on finite subsets of their domains \needcite{}.
Although we can think of |Map a b| as denoting partial functions from |a| to |b|, if we further require |b| to be semiring, we can treat missing entries as being implicitly zero, yielding a \emph{total} function.
\notefoot{Describe finite maps and |findWithDefault|.}
As with functions, it will be helpful later to flip the order of type parameters to |Map|.
\begin{theorem}[\provedIn{theorem::<--}]\thmlabel{:<--}
Given the definitions in \figrefdef{:<--}{Finite maps as a language representation}{
\begin{code}
newtype b :<-- a = M (Map a b) deriving Show

mapTo :: (Ord a, Semiring b) => (b :<-- a) -> (b <-- a)
mapTo (M m) = F (m NOP !)

(!) :: Map a b -> a -> b
m ! k = findWithDefault zero k m

instance (Monoid a, Ord a, Semiring b) => Semiring (b :<-- a) where
  zero = M empty
  one = single mempty
  M p  <+>  M q = M (unionWith (<+>) p q)
  M p <.> M q = bigSumKeys (a <# keys p BR b <# keys q) h a b +-> (p!a) <.> (q!b)

instance Semiring b => HasSingle (b :<-- a) a s where
  single a = M (singleton a one)

instance Semiring s => Scalable (s :<-- a) s where
  s .> M m = M (fmap (s NOP <.>) m)
\end{code}
\vspace{-4ex}
}, |mapTo| is a homomorphism with respect to each instantiated class.
\notefoot{Describe the |Map| operations used in \figref{:<--}.}
\notefoot{Look for a better name than ``|mapTo|''.}
\end{theorem}
The finiteness of finite maps interferes with giving a useful |StarSemiring| instance.

\note{Define another wrapper for |[a]| that represents |a <-- Sum Nat|.
Maybe also multidimensional arrays.
Probably save for later when I discuss spatial convolution and polynomials.
In any case, introduce streams first since they're simpler than lists; then map lists to streams, and optimize.}

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
%if False
First, however, we'll need to generalize to representations other than |b <-- a|:
\begin{code}
class Decomposable a h s | a -> h s where
  infix 1 <:
  (<:)   :: s -> h a -> a
  atEps  :: a -> s
  deriv  :: a -> h a

instance Semiring b => Decomposable ([c] -> b) ((->) c) b where
  (b <: _) []      = b
  (_ <: h) (c:cs)  = h c cs
  atEps  f = f []
  deriv  f = \ c cs -> f (c : cs)
\end{code}
We'll need a way to index into |h|:
\notefoot{Perhaps introduce |Indexable| earlier and use in defining |mapTo| in \figref{:<--}.}
\begin{code}
class Indexable p k v | p -> k v  where (!) :: p -> k -> v

instance Indexable (k -> v) k v   where f ! k = f k

instance (Ord k, Semiring v) => Indexable (Map k v) k v where
  m ! k = findWithDefault zero k m
\end{code}

\noindent
Now adapt the |[c] -> b| instance of |Decomposable| to |b <-- [c]|:
\begin{code}
instance Semiring b => Decomposable (b <-- [c]) ((->) c) b where
  b <: h = F (b <: unF . h)
  atEps  (F f) = f mempty
  deriv  (F f) = \ c -> F (\ cs -> f (c:cs))
\end{code}
%% \begin{code}
%%   b <: h = F (\ NOP case  []    -> b
%%                           c:cs  -> unF (h c) cs)
%% \end{code}

%endif

\begin{lemma}[\provedIn{lemma:atEps b <-- [c]}]\lemlabel{atEps b <-- [c]}
The |atEps| function is a star semiring homomorphism, i.e.,
\notefoot{Also a semimodule homomorphism, i.e., ``linear''. I may want to say so here if I reorganize the paper so as to introduce semimodules sooner.}
\begin{code}
atEps zero         == zero
atEps one          == one
atEps (p  <+>  q)  == atEps p  <+>  atEps q 
atEps (p  <.>  q)  == atEps p  <.>  atEps q 

atEps (star p)     == star (atEps p)

atEps (s .> p)     == s * atEps p
\end{code}
Moreover, |atEps (single [d]) == zero|.
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
(a  <:  dp) <.> q == a .> q <+> (zero <: (<.> NOP q) . dp)
star (a <: dp) = q where q = star a .> (one <: (<.> NOP q) .  dp)

single w = product (map symbol w) where symbol d = zero <: equal d

s .> (a <: dp) = s <.> a <: (s NOP .>) . dp
\end{code}
\vspace{-6ex}
\end{spacing}
\end{theorem}

To make use of these insights, it will be convenient to generalize the decomposition to other representations:
\begin{code}
class Semiring a => Decomposable a h s | a -> h s where
  infix 1 <:
  (<:)   :: s -> h a -> a
  atEps  :: a -> s
  deriv  :: a -> h a
\end{code}
The definitions given above correspond to an instance |Semiring b => Decomposable (b <-- [c]) ((->) c) b|.
\notefoot{Use an associated pattern synonym instead.}

%format `scale` = "\mathbin{\hat{" .> "}}"
%format scale = ( `scale` )
Returning to scaling, there's a very important optimization to be made.
When |s == zero|, |s .> p == zero|, so we can discard |p| entirely.
Rather than burden each |Scalable| instance with this optimization, let's define |(.>)| to apply this optimization on top of a more primitive |scale| method:
\begin{code}
class Scalable b s | b -> s where
  scale :: s -> b -> b

(.>) :: (Semiring b, Scalable b s, DetectableZero s) => s -> b -> b
s .> b  | isZero s   = zero
        | otherwise  = s `scale` b
\end{code}
The |DetectableZero| class \citep{semiring-num}:
\begin{code}
class Semiring a => DetectableZero a where isZero :: a -> Bool
\end{code}

\sectionl{Regular Expressions}

\note{A sort of ``free'' variant of functions. Easy to derive homomorphically. Corresponds to \citet{Brzozowski64} and other work on recognizing and parsing by derivatives.}

\sectionl{Tries}

%format :< = "\mathrel{\Varid{:\!\!\triangleleft}}"

Since a language is a set of strings, we have considered representations of such sets as lists, predicates, and regular expressions.
Another choice of language representation is the \emph{trie}, as introduced by Thue in 1912, according to Knuth \needcite{}.
As shown by Hinze \needcite{}, tries can be extended to represent not just sets but partial functions, as well as defined generically for partial functions from types other than strings.
Putting genericity aside\notefoot{Re-raise later?} and restricting our attention to functions of lists (``strings''), we can formulate a simple trie data type as follows:

> data Trie c s = s :< Map c (Trie c s)

The similarity between the |Trie| type and the function decomposition from \secref{Decomposing Functions from Lists} (motivating the constructor's name) makes the denotation of tries quite simple to express:\footnote{Recall |(!)| from \figref{:<--} as zero-defaulted finite map indexing. Equivalently, |trieFun (e :< d) = e <: \ c cs -> trieFun (d ! c) cs|.}
%format OD c s = Ord SPC c
%format OD c s = (Ord SPC c, DetectableZero SPC s)
\begin{code}
trieFun :: OD c => Trie c s -> ([c] -> s)
trieFun (e :< d) = e <: trieFun . (d NOP !)
\end{code}
Likewise, the properties from section \secref{Decomposing Functions from Lists} make it fairly easy to calculate instances for |Trie|.
\begin{theorem}[\provedIn{theorem:Trie}]\thmlabel{Trie}
Given the definitions in \figrefdef{Trie}{Tries as a language representation}{
\begin{code}
infix 1 :<
data Trie c s = s :< Map c (Trie c s)

instance OD c s => Decomposable (Trie c s) (Map c) s where
  a <: d = a :< d
  atEps  (a  :<  d) = a
  deriv  (a  :<  d) = d

instance OD c s => Semiring (Trie c s) where
  zero = zero :< empty
  one  = one  :< empty
  (a :< dp) <+> (b :< dq) = (a <+> b) :< unionWith (<+>) dp dq
  (a :< dp) <.> q = a .> q <+> (zero :< fmap (<.> q) dp)

instance OD c s => StarSemiring (Trie c s) where
  star (a :< dp) = q where q = star a .> (one :< fmap (<.> NOP q) dp)

instance OD c s => HasSingle (Trie c s) [c] where
  single w = product (map symbol w) where symbol c = zero <: singleton c one

instance OD c s => Scalable (Trie c s) s where
  s `scale` (b :< dq) = (s <.> b) :< fmap (s NOP `scale`) dq
\end{code}
\vspace{-4ex}
}, |trieFun| is a homomorphism with respect to each instantiated class.
\notefoot{I think we could exploit a |Semiring b => Semiring (Map c b)| instance and so replace |unionWith (<+>)| by |(<+>)| and |empty| by |zero| here.
Similarly for |single w|.
Wait until I factor out an |Additive| superclass.
% I might want to use \emph{total maps} \citep{Elliott-2009-tcm}, especially in \secref{Beyond Convolution}.
Going further, I think I can write one body of code that works exactly as is for both |b <-- [c]| and |Trie b c|, by making |(<:)| be an associated pattern synonym and defining a general |atEps| and |deriv| in terms of it. Try it!}
\end{theorem}
Note again the important optimization for |zero .> t = zero|, eliminating the entire, possibly infinite trie |t|.
This optimization applies quite often in practice, since languages tend to be sparse.

\sectionl{Convolution}

%format bar (x) = "\bar{"x"}"
%format blam = "\bar{\lambda}"

Consider again the definition of semiring ``multiplication'' on functions |f,g :: b <-- a| from \figref{<--}, temporarily eliding the |F| constructors:
\notefoot{To do: try \emph{with} all of the required |F| constructors. Try also with lighter-weight notation for |F|. For instance, replace ``|F f|'' by ``|bar f|'' and ``|\ w -> cdots|'' by ``|blam w -> cdots|''.}
\begin{equation}\eqnlabel{convolution}
f * g = \sum_{u,v} u \mappend v \mapsto f\,u * g\,v
\end{equation}
If we specialize the functions' codomains to |Bool|, we get a definition equivalent to one in \figref{pred}:

>   f <.> g = bigOr (u,v) u <> v +-> f u && g v

Using the set/predicate isomorphism from \secref{Matching}, we can translate this definition from predicates to sets, as in \figref{set}:

>   f <.> g = set (u <> v | u <# f && v <# g)

which is the definition of the concatenation of two languages from \secref{Languages}.

By specializing the \emph{domain} of the functions to sequences (from general monoids), we can get efficient matching of semiring-generalized ``languages'', as in \secreftwo{Decomposing Functions from Lists}{Tries}, which translates to regular expressions (\secref{Regular Expressions}), generalizing work of \citet{Brzozowski64}\note{, while apparently improving performance.
\notefoot{Measure and compare in \secref{Regular Expressions}.}}

%format R = "\mathbb R"
%format C = "\mathbb C"

%format bigSumPlus (lim) = "\bigOp\sum{" lim "}{1.5}"
Let's now consider specializing the functions' domains to \emph{integers} rather than sequences, recalling that integers (and numeric types in general) form a monoid under addition.
\vspace{-2ex}
\begin{spacing}{1.5}
\begin{code}
f <.> g  == bigSum (u,v) u <> v +-> f u <.> g v
         == bigSum (u,v) u + v +-> f u <.> g v                              -- monoid under addition
         == bigSum (u,v) (\ w -> if w == u + v then f u <.> g v else zero)  -- |(+->)| definition
         == \ w -> bigSum (u,v) (if w == u + v then f u <.> g v else zero)  -- |(<+>)| on functions
         == \ w -> bigSumPlus (u,v BR u + v == w) f u <.> g v               -- skip zeros (additive identity)
         == \ w -> bigSumPlus (u,v BR v == w - u) f u <.> g v               -- solve |u + v == w| for |v|
         == \ w -> bigSum u f u <.> g (w - u)                               -- substitute |w - u| for |v|
\end{code}
\end{spacing}
\vspace{-3ex}
\noindent
This last form is the standard definition of one-dimensional, discrete \emph{convolution} \needcite{}.\footnote{Note that this reasoning applies to \emph{any} group (monoid with inverses)}
Therefore, just as \eqnref{convolution} generalizes language concatenation (via the predicate/set isomorphism), it also generalizes the usual notion of discrete convolution.
Moreover, if the domain is a continuous type such as |R| or |C|, we can reinterpret summation as integration, resulting in \emph{continuous} convolution \needcite{}.
Additionally, for multi-dimensional (discrete or continuous) convolution, we can simply use tuples of scalar indices for |w| and |u|, defining tuple addition and subtraction componentwise.
\notefoot{More generally, cartesian products of monoids are also monoids.
Consider multi-dimensional convolution in which different dimensions have different types, even mixing discrete and continuous, and maybe even sequences and numbers.
At the least, it's useful to combine finite dimensions of different sizes.}
\begin{theorem}[\provedIn{theorem:Fourier}]\thmlabel{Fourier}
The Fourier transform is a semiring homomorphism from |b <- a| to |a -> b|.
\end{theorem}

\note{Maybe give some convolution examples.}

%format Identity = I
Let's now consider functions from |N| rather than from |Z|.
As in \secref{Decomposing Functions from Lists}, we can define a decomposition on functions from |N|:
\notefoot{I suspect that the |Decomposable| interface isn't quite the right generalization. Try some additional monoids, and examine via more generic constructions for underlying monoids, including general sums and products. Relate to generalized tries \citep{Hinze2000GGT}.}
\begin{code}
newtype Identity a = Identity a  -- identity functor

instance Semiring b => Decomposable (b <-- N) Identity b where
  b <: Identity (F f) = F (\ i -> if i == 0 then b else f (i - 1))
  atEps  (F f)  = f 0
  deriv  (F f)  = Identity (F (f . (1 NOP +)))
\end{code}
\begin{theorem}[\provedIn{theorem:decomp (b <-- N)}]\thmlabel{decomp (b <-- N)}
For all |p :: b <-- N|, |p == atEps p <: deriv p|.
\end{theorem}

Differentiation is much as in \lemref{deriv b <-- [c]}:
\notefoot{I'm leaning toward inverting the organization of this paper, starting with convolution, then semimodule function/applicative/monad, and languages later still.
That way, I can introduce |b <-- N| before the somewhat more complicated |b <-- [c]|.}
\begin{lemma}[\provedIn{lemma:deriv (b <-- N)}]\lemlabel{deriv (b <-- N)}
Differentiation on |b <-- N|, has the following properties (eliding |Identity| constructors):
\notefoot{If I give a |Semiring| instance for |Identity b| (for semirings |b|), then I think these equations hold as written. I bet I can do the same for |b <-- [c]|, and maybe for all domains |a| for which |Decomposable a|. Try it!}
\notefoot{What about |single i|? Important?}
\begin{code}
deriv zero  == zero
deriv one   == zero
deriv (p  <+>  q) == deriv p <+> deriv q
deriv (p  <.>  q) == atEps p .> deriv q <+> deriv p <.> q

deriv (star p) == star (atEps p) .> deriv p <.> star p
\end{code}
%% deriv (single [d]) c == equal c d
\end{lemma}
\begin{corollary}\corlabel{decomp b <-- N}
The following properties hold for |b <-- N|:
\notefoot{Work out |single n| or |n +-> b|, probably as a simple generalization of |one|.}
\begin{code}
zero  = zero  <: zero
one   = one   <: zero
(a  <:  dp)  <+>  (b <: dq) = (a  <+>  b) <: (dp <+> dq)
(a  <:  dp)  <.>  (b <: dq) = (a  <.>  b) <: (a .> dq <+> dp <.> (b <: dq))

star (a <: as) = q where q = star a .> (one <: as <.> q)
\end{code}
%% single w = product (map symbol w)
%%   where
%%      symbol d = zero <: equal d
\end{corollary}

\note{Remark that |N =~ [()]|, so this decomposition is a special case of  \secref{Decomposing Functions from Lists}. On the other hand, I think I'll move the whole language discussion to \emph{after} this decomposition.}

%format :# = "\mathbin{:\!\!\#}"
While the |b <-- N| representation makes for simple semantics and reasoning, there are more efficient alternatives.
For instance, consider streams, as shown in \figrefdef{Stream}{Streams}{
\begin{code}
infixr 1 :#
data Stream b = b :# Stream b

instance Indexable (Stream b) N b where
  (b :# bs) ! n = if n == 0 then b else bs ! (n-1)

streamF :: Stream b -> (b <-- N)
streamF bs = F (bs NOP !)

instance DetectableZero b => Decomposable (Stream b) Identity b where
  b <: Identity bs = b :# bs
  atEps  (b  :# _   )  = b
  deriv  (_  :# bs  )  = Identity bs

instance DetectableZero b => Semiring (Stream b) where
  zero = q where q = zero :# q
  one = one :# zero
  (u :# us') <+> (v :# vs') = u <+> v :# us' <+> vs'
  (u :# us') <.> vs@(v :# vs') = u <.> v :# u .> vs' <+> us' <.> vs

instance (StarSemiring b, DetectableZero b) => StarSemiring (Stream b) where
  star (a :# as) = q where q = star a .> (one :# as <.> q)

instance DetectableZero s => Scalable (Stream s) s where
  s `scale` (b :# bs) = (s <.> b) :# (s `scale` bs)
\end{code}
\vspace{-6ex}
}.
\begin{theorem}\thmlabel{Stream}
Given the definitions in \figref{Stream}, |streamF| is a homomorphism with respect to each instantiated class.
\end{theorem}
\begin{proof}
Immediate from \corref{decomp b <-- N}.
\end{proof}

\workingHere

\noindent
\note{Next:
\begin{itemize}
\item Discuss how |Stream b| is much more efficient than |b <-- N|.
\item Somewhere I think I should be showing and using the |Splittable N| instance. See previous note.
\item Lists (finite) instead of streams (infinite), with a semantic function that zero-pads.
\item Non-scalar domains as in notes from 2019-01-\{28,29\}.
\end{itemize}
}

\sectionl{Beyond Convolution}

%format Fin (m) = Fin "_{" m "}"
%format Array (m) = Array "_{" m "}"

Some uses of convolution (including convolutional neural networks \needcite{}) involve functions having finite support, i.e., non-zero on only a finite subset of their domains.
\notefoot{First suggest finite maps, using instances from \figref{:<--}. Then intervals/arrays.}
In many cases, these domain subsets may be defined by finite \emph{intervals}.
For instance, such a 2D operation would be given by intervals in each dimension, together specifying lower left and upper right corners of a 2D interval (rectangle) outside of which the functions are guaranteed to be zero.
The two input intervals needn't have the same size, and the result's interval of support is larger than both inputs, with size equaling the sum of the sizes in each dimension (minus one for the discrete case).
\notefoot{Show an example as a picture.}
Since the result's support size is entirely predictable and based only on the arguments' sizes, it is appealing to track sizes statically via types.
For instance, a 1D convolution might have the following type:
\notefoot{To do: More clearly distinguish between functions with finite support vs functions with finite domains. I think I started this paragraph with the former mindset but switched to the latter.}
\begin{code}
(*) :: Semiring s => Array (m+1) s -> Array (n+1) s -> Array (m+n+1) s
\end{code}
Unfortunately, this signature is incompatible with the general type of |(*)|, in which arguments and result all have the same type.

From the perspective of functions, an array of size |n| is a memoized function from |Fin n|, which represents the finite set |set (0, ..., n-1)|.
Although we can still define a convolution-like operation in terms of index addition, indices no longer form a monoid, simply due to the non-uniformity of types.
%format lift0
%format lift1
%format lift2
%format liftn = lift "_n"
%if False

The inability to support convolution on statically sized arrays (or other memoized forms of functions over finite domains) as semiring multiplication came from the expectation that index/argument combination is via a monoid.
%endif
This limitation is a shame, since convolution still makes sense:
\begin{code}
f <.> g = bigSum (u,v) u + v +-> f u <.> g v
\end{code}
where now
\begin{code}
(+) :: Fin (m+1) -> Fin (n+1) -> Fin (m+n+1)
\end{code}
(As in \secref{Convolution}, we're continuing to elide the |F| constructors for |b <-- a| of \figref{<--}.)
Fortunately, this monoid expectation can be dropped by generalizing from monoidal combination to an \emph{arbitrary} binary operation |h :: a -> b -> c|.
For now, let's call this more general operation ``|lift2 h|''.
\notefoot{Maybe remark on the mixture of ``|->|'' and ``|<--|''.}
\begin{code}
lift2 :: Semiring s => (a -> b -> c) -> (s <-- a) -> (s <-- b) -> (s <-- c)
lift2 h f g = \ w -> bigSum (u,v) h u v +-> f u <.> g v
\end{code}
We can similarly lift functions of \emph{any} arity:
%format a1
%format an = a "_n"
%format f1
%format fn = f "_n"
%format u1
%format un = u "_n"
\begin{code}
liftn :: Semiring s => (a1 -> ... -> an -> b) -> (s <-- a1) -> ... -> (s <-- an) -> (s <-- b)
liftn h f1 ... fn = bigSumQ (u1, ..., un) h u1 cdots un +-> f1 u1 <.> cdots <.> fn un
\end{code}
Here we are summing over the set-valued \emph{preimage} of |w| under |h|.
Now consider two specific cases of |liftn|:
\begin{code}
lift1 :: Semiring s => (a -> b) -> (s <-- a) -> (s <-- b)
lift1 h f = bigSum u h u +-> f u

lift0 :: Semiring s => b -> (s <-- b)
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
%format SRM = DetectableZero
%% %format keys p = p
\noindent
The signatures of |lift2|, |lift1|, and |lift0| generalize to those of |liftA2|, |fmap|, and |pure| from the |Functor| and |Applicative| type classes \needcite, so let's replace the specialized operations with standard ones.
An enhanced version of these classes appear in \figrefdef{FunApp}{|Functor| and |Applicative| classes and some instances}{
\begin{code}
class FunctorC f where
  type Ok f a :: Constraint
  type Ok f a = ()
  fmapC :: (Ok f a, Ok f b) => (a -> b) -> f a -> f b

class FunctorC f => ApplicativeC f where
  pureC :: Ok f a => a -> f a
  liftA2C :: (Ok f a, Ok f b, Ok f c) => (a -> b -> c) -> f a -> f b -> f c

infixl 1 >>==
class ApplicativeC f => MonadC f where
  (>>==) :: (Ok f a, Ok f b) => f a -> (a -> f b) -> f b

instance Functor Pow where
  fmap h p = set (h a | a <# p)

instance Applicative Pow where
  pure b = single b
  liftA2 h p q = set (h a b | a <# p && b <# q)

instance Functor [] where
  fmap h as = [h a | a <- as]

instance Applicative [] where
  pure a = single a
  liftA2 h p q = [h u v | u <- p, v <- q]

instance SRM b => FunctorC ((:<--) b) where
  type Ok ((:<--) b) a = (Ord a, Monoid a)
  fmapC h (M p) = bigSumKeys (a <# keys p) h a +-> p ! a

instance SRM b => ApplicativeC ((:<--) b) where
  pureC a = single a
  liftA2C h (M p) (M q) = bigSumKeys (a <# keys p BR b <# keys q) h a b +-> (p!a) <.> (q!b)

instance Semiring b => Functor ((<--) b) where
  type Ok ((<--) b) a = (Eq a, Monoid a)
  fmap h (F f) = bigSum u h u +-> f u

instance Semiring b => Applicative ((<--) b) where
  pure a = single a
  liftA2 h (F f) (F g) = bigSum (u,v) h u v +-> f u <.> g v
\end{code}
\vspace{-3ex}
}, along with instances for some of the language representations we've considered so far.%
\footnote{The enhancement is the associated constraint \citep{Bolingbroke2011CK} |Ok|, limiting the types that the class methods must support. The line ``|type Ok f a = ()|'' means that the constraint on |a| defaults to |()|, which holds vacuously for all |a|.}%
\footnote{Originally, |Applicative| had a |(<*>)| method from which one can easily define |liftA2|. Since the base library version 4.10 \needcite, |liftA2| was added as a method (along with a default definition of |(<*>)|) to allow for more efficient implementation. \note{Cite \href{https://ghc.haskell.org/trac/ghc/ticket/13191}{GHC ticket 13191} if I can't find a better reference.}}%
%if False
\footnote{The methods on |(:<--) b| (finite maps to |b|) are written in straight Haskell as follows:
\vspace{-0.5ex}
\begin{code}
  fmapC h (M p) = sum [ h a +-> s | (a,s) <- toList p ]

  liftA2C h (M p) (M q) = sum [ h a b +-> s <.> t | (a,s) <- toList p, (b,t) <- toList q]
\end{code}
\vspace{-3ex}
}%
%endif
\notefoot{The |Monoid a| requirement for |(:<--) b| and |(<--) b| is due to the corresponding |Semiring| instances, but really just for
|one| and |(<.>)|, which we're not using. To do: factor |Additive| out of |Semiring|, and drop the |Monoid a| requirements here. I'll have to return to defining my own classes. If I make this change, then give an |Additive| instance for |Map| and use it for |(:<--)|. Similarly for lists and streams consistently with their denotation as |N -> b|. Wrap for |b <-- N|.}
Higher-arity liftings can be defined via these three.
(Exercise.)
The use of |s <-- t| as an alternative to |t -> s| allows us to give instances for both and to stay within Haskell's type system (and ability to infer types via first-order unification).
For |b <-- a|, these definitions are not really executable code, since they involve summations are over potentially infinite ranges (as with our semiring instances for |b <-- a| in \figref{<--}).
\begin{theorem}
For each instance defined in \figref{FunApp}, the following equalities hold:
\notefoot{Probe more into the pattern of |single = pure|, |one = single mempty| and |(*) = liftA2 (<>)|.
Also the relationship between forward and reverse functions and maps.}
\begin{code}
one  = pure mempty
(*)  = liftA2 (<>)
\end{code}
\end{theorem}
\begin{proof}
Immediate from the instance definitions.
\end{proof}

\sectionl{The free semimodule monad}

Where there's an applicative, there's often a compatible monad.
For |b <-- a|, the monad is known as the ``free semimodule monad'' (or sometimes the ``free \emph{vector space} monad'') \needcite{}.
(A semimodule is like a vector space but relaxes the requirement of a \emph{field} of scalars to a semiring.)
One can think of a free semimodule over a semiring |b| as |b <-- a| for some set |a| of ``indices'' and semiring |b| of ``scalars''.
The dimension of the semimodule is the cardinality of |a|.
Basis vectors have the form |single u| for some |u :: a|, mapping |u| to |one| and everything else to |zero| as in \figref{<--}.
%if False
\begin{theorem}[\provedIn{theorem:decompose liftA2}]\thmlabel{decompose liftA2}
Every function |f :: b <-- a| can be decomposed into this basis as follows:
\notefoot{I'm not assuming finite support, which is part of the usual definition but problematic for the applications in this paper. Is nthere a problem with dropping finite support and finiteness of linear combinations?}
\begin{code}
F f = bigSum u (f u .> single u)
\end{code}
\vspace{-4ex}
\end{theorem}
%endif

The monad instance is defined as follows:\footnote{The |return| method does not appear here, since it is equivalent to |pure| from |Applicative|.}
\begin{code}
instance Semiring s => Monad ((<--) s) where
  (>>=) :: (s <-- a) -> (a -> (s <-- b))) -> (s <-- b)
  F f >>= h = bigSum a f a .> h a
\end{code}
\vspace{-4ex}
\begin{theorem}[\provedIn{theorem:standard FunApp}]\thmlabel{standard FunApp}
The definitions of |fmap| and |liftA2| on |((<--) b)| in \figref{FunApp} satisfy the following standard equations for monads:
\begin{code}
fmap h p = p >>= pure . h

liftA2 h p q  = p >>= \ u -> fmap (h u) q
              = p >>= \ u -> q >>= \ v -> pure (h u v)
\end{code}
\end{theorem}

\note{This form looks a lot like a Brzozowski-style language convolution implementation I've used, with |h = (<>)| and |fmap (u NOP <>) q| implemented carefully. Use it to derive an efficient |(*)| for tries. Compare with \figref{Trie} and \thmref{Trie}.}

\sectionl{More applications}

\subsectionl{Polynomials}

%format N = "\mathbb{N}"
%format (Sum a) = a

As is well known, univariate polynomials form a semiring and can be multiplied by \emph{convolving} their coefficients.
Perhaps less known is that this trick extends naturally to multivariate polynomials and to (univariate and multivariate) power series.

Looking more closely, univariate polynomials (and even power series) can be represented by a collection of coefficients indexed by exponents.
For a polynomial in a variable |x|, an association of exponent |i| to coefficient |c| represents the polynomial term |c * pow x i|.
One can use a variety of representations for these indexed collections.
We'll consider efficient representations below, but let's begin as |b <-- N| along with a denotation as |b -> b|, where |N| is the additive monoid of natural numbers:
%% Elide the Sum isomorphism
% type N = Sum Natural
\begin{code}
poly :: Semiring b => (b <-- N) -> (b -> b)
poly (F f) = \ x -> bigSum i  f i * pow x i
\end{code}
Polynomial multiplication via convolution follows from the following property:
\begin{theorem}[\provedIn{theorem:poly fun}]\thmlabel{poly fun}
The function |poly| is a semiring homomorphism when multiplication on |b| commutes.
\end{theorem}

\workingHere

\noindent
\note{Next:
\begin{itemize}\itemsep0ex
\item Generalize via monoidal scan
\item Examples
\item Finite maps
\item Non-scalar domains (``multivariate'' polynomials) as in notes from 2019-01-\{28,29\}
\item Non-scalar codomains
\end{itemize}
}

\sectionl{What else?}
\vspace{-3ex}
\note{
\begin{itemize}\itemsep0ex
\item Counting
\item Probability distributions
\item Temporal/spatial convolution
\item Discrete and continuous
\item Context-free languages (recursion)
\item Other applications:
\item 2D parsing?
\end{itemize}
}

\sectionl{Related Work}
\begin{itemize}\itemsep0ex
\item \emph{Fun with semirings}
\item \emph{Polynomial Functors Constrained by Regular Expressions}
\item \href{https://doisinkidney.com/}{Donnacha Oisín Kidney's blog}
\item Dan Piponi's blog
\item \citet{Uustalu2002DSR}, since tries appear to be cotrees, and the function comonad relates closely to Brzozowski-style ``derivatives''.
\item Many more references in \verb|todo.md|.
\end{itemize}


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

\appendix

\sectionl{Proofs}

\subsection{\thmref{list}}\proofLabel{theorem:list}

%format bigSumA (lim) = "\bigOp\sum{" lim "}{1}"
%format bigSumB (lim) = "\bigOp\sum{" lim "}{2}"
Recall the definition of |elems|:
\begin{code}
elems :: (Semiring p, HasSingle p a) => [a] -> p
elems as = bigSum (a <# as) (single a)
\end{code}
The homomorphism proofs:
\begin{code}
    elems zero
==  elems (L [])                 -- |zero| on |List a|
==  bigSum (a <# []) (single a)  -- |elems| definition
==  zero                         -- vacuous sum

    elems one
==  elems (L [mempty])                 -- |one| on |List a|
==  bigSum (a <# [mempty]) (single a)  -- |elems| definition
==  single mempty                      -- singleton sum
==  one                                -- |one| on |List a|

    elems (L u <+> L v)
==  elems (L (u ++ v))                                             -- |(<+>)| on |List a|
==  bigSum (a <# u ++ v) (single a)                                -- |elems| definition
==  (bigSum (a <# u) (single a)) <+> (bigSum (a <# v) (single a))  -- \lemref{elems plus}
==  elems u <+> elems v                                            -- definition of |elems|

    elems (L u <.> L v)
==  elems (L (liftA2 (<>) u v))                -- |(<.>)| on |List a|
==  bigSumB (a <# liftA2 (<>) u v) (single a)  -- |elems| definition
==  ...                                        -- \note{finish}
==  elems u <.> elems v
\end{code}

\begin{lemma}\lemlabel{elems plus}
The |elems| function is a monoid homomorphism targeting the sum monoid, i.e.,
\begin{code}
elems [] == zero
elems (xs ++ ys) == elems xs <+> elems ys
\end{code}
\end{lemma}
\begin{proof}
By list induction.
\end{proof}

\subsection{\thmref{pred}}\proofLabel{theorem:pred}

\subsection{\lemref{decomp +->}}\proofLabel{lemma:decomp +->}

\begin{code}
    bigSum a a +-> f a
==  bigSum a F (\ w -> if w == a then f a else zero)  -- |(+->)| on |b <-- a|
==  F (\ w -> bigSum a if w == a then f a else zero)  -- |(<+>)| on |b <-- a|
==  F (\ w -> f w)                                    -- summation property
==  F f                                               -- $\eta$ reduction
\end{code}

\subsection{\thmref{<--}}\proofLabel{theorem:<--}

\subsection{\thmref{:<--}}\proofLabel{theorem::<--}

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
\end{proof}

\subsection{\lemref{atEps b <-- [c]}}\proofLabel{lemma:atEps b <-- [c]}

\begin{code}

    atEps zero
==  atEps (F (\ a -> zero))  -- |zero| on |b <-- a|
==  (\ a -> zero) []         -- |atEps| definition
==  zero                     -- $\beta$ reduction

    atEps one
==  atEps (F (equal mempty))  -- |one| on |b <-- a|
==  equal mempty mempty       -- |atEps| definition            
==  one                       -- |equal| definition

    atEps (F f <+> F g)
==  atEps (F (\ a -> f a <+> g a))      -- |(<+>)| on |b <-- a|
==  (\ a -> f a <+> g a) []             -- |atEps| definition
==  f [] <+> g []                       -- $\beta$ reduction
==  atEps (F f) <+> atEps (F g)         -- |atEps| definition

    atEps (F f <.> F g)
==  atEps (bigSum (u,v) u <> v +-> f u <.> g v)               -- |(<.>)| on |b <-- a|
==  atEps (\ w -> bigSumQ (u,v BR u <> v == []) f u <.> g v)  -- alternative definition from \figref{<--}
==  bigSumKeys (u,v BR u == [] && v == []) NOP f u <.> g v    -- |u <> v == [] <=> u == [] && v == []| 
==  f [] <.> g []                                             -- singleton sum
==  atEps (F f) <.> atEps (F g)                               -- |atEps| definition

    atEps (star p)
==  atEps (one <+> p <.> star p)        -- defining property of |star|
==  one <+> atEps p <.> atEps (star p)  -- |atEps| distributes over |one|, |(<+>)| and |(<.>)|
==  one <+> atEps p <.> star (atEps p)  -- coinduction (?)
==  star (atEps p)                      -- defining property of |star|

    atEps (s .> F f)
==  atEps (F (\ a -> s * f a))
==  (\ a -> s * f a) []
==  s * f []
==  s * atEps (F f)
\end{code}
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
Finally, closure:
\begin{code}
    deriv (star p) c
==  deriv (one <+> p <.> star p) c                        -- star semiring law
==  deriv one c <+> deriv (p <.> star p) c                -- additivity of |deriv|
==  deriv (p <.> star p) c                                -- |deriv one c == zero| (above)
==  atEps p .> deriv (star p) c <+> deriv p c <.> star p  -- |deriv (p * q)| above
\end{code}
Thus, by \lemref{affine fixed point} below,
\begin{code}
deriv (star p) c == star (atEps p) .> deriv p c <.> star p
\end{code}

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

\begin{lemma}\lemlabel{affine fixed point}
The equation |q == r <+> s .> q| has solution |q = star s .> r|.
\end{lemma}
\begin{proof}~
\begin{code}
    star s .> r
==  (one <+> s <.> star s) .> r         -- star semiring law
==  one .> r <+> (s <.> star s) .> r    -- distributivity
==  r <+> s .> (star s .> r)            -- multiplicative identity and associativity
\end{code}
\end{proof}

\subsection{\thmref{semiring decomp b <-- [c]}}\proofLabel{theorem:semiring decomp b <-- [c]}

\begin{code}
    zero
==  atEps zero <: deriv zero  -- \lemref{decomp (b <-- [c])}
==  zero <: (\ c -> zero)     -- \lemreftwo{atEps b <-- [c]}{deriv b <-- [c]}
==  zero <: zero              -- |zero| on functions
\end{code}

\begin{code}
    one
==  atEps one <: deriv one  -- \lemref{decomp (b <-- [c])}
==  one <: (\ c -> zero)    -- \lemreftwo{atEps b <-- [c]}{deriv b <-- [c]}
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
==  a .> (b <: dq) <+> (zero <: \ c -> dp c <.> (b <: dq))                    -- \note{needs lemma}
\end{code}

%% \lemref{atEps and deriv via (<:)}

%% star (a <: dp) = q where q = star a .> (one <: (<.> NOP q) .  dp)

\begin{code}
    star (a <: dp)
==  atEps (star (a <: dp)) <: deriv (star (a <: dp))                     -- \lemref{decomp (b <-- [c])}
==  star a <: \ c -> star a .> dp c * star (a <: dp)                     -- \lemref{atEps and deriv via (<:)} below
==  star a .> (one <: \ c -> dp c * star (a <: dp))                      -- \note{needs same lemma as above}
\end{code}

\workingHere

%% single w = product (map symbol w)
%%   where
%%      symbol d = zero <: equal d

\begin{code}
    |single w|
==  ...
\end{code}

\begin{code}
    s .> p
==  ...
\end{code}

\begin{lemma}\lemlabel{atEps and deriv via (<:)}
The |atEps| and |deriv| functions satisfy the following properties in terms of |(<:)|-decompositions:
\begin{code}
atEps ((a <: dp)  <+>  (b <: dq))  == a <+> b
atEps ((a <: dp)  <.>  (b <: dq))  == a <.> b
atEps (star (a <: dp)) == star a
\end{code}
\begin{code}
deriv ((a <: dp)  <+>  (b <: dq)) c == dp c <+> dq c
deriv ((a <: dp)  <.>  (b <: dq)) c == a .> dq c <+> dp c <.> (b <: dq)
deriv (star (a <: dp)) c == star a .> dp c * star (a <: dp)
\end{code}
\end{lemma}
\begin{proof}
Substitute into \lemreftwo{atEps b <-- [c]}{deriv b <-- [c]}, and simplify, using the |Decomposable| laws.
\notefoot{Have I stated these laws?}
\end{proof}

\subsection{\thmref{Trie}}\proofLabel{theorem:Trie}

\subsection{\thmref{Fourier}}\proofLabel{theorem:Fourier}

%format T = "\mathcal F"
\note{Additivity of |T|, and the convolution theorem. What about |star p| and |single w|?}

\subsection{\thmref{decomp (b <-- N)}}\proofLabel{theorem:decomp (b <-- N)}

\begin{code}
    atEps (F f) <: deriv (F f)
==  f 0 <: I (F (f . (1 NOP +)))                                -- |atEps| and |deriv| on |b <-- N|
==  F (\ i -> if i == 0 then f 0 else (f . (1 NOP +)) (i - 1))  -- |(<:)| on |b <-- N|
==  F (\ i -> if i == 0 then f 0 else f (1 + (i - 1)))          -- |(.)| definition
==  F (\ i -> if i == 0 then f 0 else f i)                      -- arithmetic
==  F (\ i -> if i == 0 then f i else f i)                      -- |i == 0| in |then| branch
==  F f                                                         -- property of conditional
\end{code}

\subsection{\lemref{deriv (b <-- N)}}\proofLabel{lemma:deriv (b <-- N)}

\begin{code}
    deriv zero
==  deriv (F (\ i -> zero))        -- |zero| on |b <-- a|
==  F ((\ i -> zero) . (+ NOP 1))  -- |deriv| definition
==  F (\ i -> zero)                -- $\beta$ reduction
==  zero                           -- |zero| on |b <-- a|
\end{code}
\begin{code}
    deriv one
==  deriv (F (\ i -> if i == 0 then one else zero))   -- |one| on |b <-- a|
==  F (\ i -> if i+1 == 0 then one else zero)         -- |deriv| definition
==  F (\ i -> zero)                                   -- |i+1 /= 0|
==  zero                                              -- |zero| on |b <-- a|
\end{code}
\begin{code}
    deriv (F f <+> F g)
==  deriv (F (\ i -> f i <+> g i))             -- |(<+>)| on |b <-- a|
==  F (\ i -> f (i+1) <+> g (i+1))             -- |deriv| definition; $\beta$ reduction
==  F (\ i -> f (i+1)) <+> F (\ i -> g (i+1))  -- |(<+>)| on |b <-- a|
==  deriv (F f) <+> deriv (F g)                -- |deriv| definition
\end{code}
\begin{code}
    deriv (F f <.> F g)
==  deriv (bigSum (u,v)  u + v +-> f u <.> g v)                 -- |(<.>)| on |b <-- a|
==  bigSum (u,v)  deriv (u + v +-> f u <.> g v)                 -- |deriv| additivity (previous property)
==  (bigSum v  deriv (0 + v +-> f 0 <.> g v)) <+>
    (bigSum (u',v)  deriv (1 + u' + v +-> f (1 + u') <.> g v))  -- case split |u|
\end{code}
First addend:
\begin{code}
    bigSum v  deriv (0 + v +-> f 0 <.> g v)
==  f 0 .> (bigSum v  deriv (v +-> g v))                        -- linearity
==  f 0 .> deriv (bigSum v  (v +-> g v))                        -- additivity
==  f 0 .> deriv (F g)                                          -- \lemref{decomp +->}
\end{code}
Second addend:
\begin{code}
    bigSum (u',v)  deriv (1 + u' + v +-> f (1 + u') <.> g v)
==  bigSum (u',v)  u' + v +-> f (1 + u') <.> g v                -- \lemref{deriv +-> Nat} below
==  F (f . (1 NOP +)) <.> F g                                   -- |(<.>)| on |b <-- a|
==  deriv (F f) <.> F g                                         -- |deriv| on |b <-- a|
\end{code}
Combining results:
\begin{code}
deriv (F f <.> F g) == f 0 .> deriv (F g) <+> deriv (F f) <.> F g
\end{code}
i.e.,
\begin{code}
deriv (p <.> q) == atEps p .> deriv q <+> deriv p <.> q
\end{code}

\noindent
\note{Next, derivations for |closure p| and either |single n| or |n +-> b|.}

\begin{lemma}\lemlabel{deriv +-> Nat}
Differentiation on |b <-- N| satisfies the following properties on singletons:
\begin{code}
    deriv (0 +-> b)
==  deriv (F (\ j -> if j == 0 then b else zero))    -- |(+->)| definition
==  F (\ j -> if j+1 == 0 then b else zero)          -- |deriv| on |b <-- N|
==  F (\ j -> zero)                                  -- |j+1 /= 0| (for |N|)
==  zero                                             -- |zero| on |b <-- a|

    deriv (i+1 +-> b)
==  deriv (F (\ j -> if j == i+1 then b else zero))  -- |(+->)| definition   
==  F (\ j -> if j+1 == i+1 then b else zero)        -- |deriv| on |b <-- N| 
==  F (\ j -> if j == i then b else zero)            -- |(+ NOP 1)| is injective
==  i +-> b                                          -- |zero| on |b <-- a|  
\end{code}
\end{lemma}

\subsection{\thmref{standard FunApp}}\proofLabel{theorem:standard FunApp}

First consider |fmap|, as defined in \figref{FunApp}.
\begin{code}
    fmap h (F f)
==  bigSum u h u +-> f u          -- definition of |fmap| on |(<--) b|
==  bigSum u f u .> single (h u)  -- definition of |(+->)|
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
==  bigSum (u,v) (f u * g v) .> single (h u v)      -- definition of |(+->)|
==  bigSum (u,v) f u .> (g v .> single (h u v))     -- associativity
==  bigSum u f u .> bigSum v g v .> single (h u v)  -- linearity
==  bigSum u f u .> bigSum v h u v +-> g v          -- definition of |(+->)|
==  bigSum u f u .> fmap (h u) (F g)                -- definition of |fmap|
==  f >>= \ u -> fmap (h u) (F g)                   -- definition of |(>>=)|
\end{code}
\end{spacing}

\subsection{\thmref{poly fun}}\proofLabel{theorem:poly fun}

The semantics as polynomial functions:
\begin{code}
poly :: Semiring b => (b <-- N) -> (b -> b)
poly (F f) = \ x -> bigSum i  f i <.> pow x i
\end{code}
Monomials are especially simple:
\begin{lemma}\lemlabel{poly +->}
\begin{code}
poly (n +-> b) = \ x -> b * pow x n
\end{code}
\end{lemma}
\begin{proof}~
\begin{code}
poly (n +-> b)
poly (\ i -> if i == n then b else zero)                  -- |(+->)| definition
\ x -> bigSum i (if i == n then b else zero) <.> pow x n  -- |poly| definition
\ x -> b * pow x n                                        -- other terms vanish
\end{code}
\end{proof}

\noindent
Homomorphism proofs for \thmref{poly fun}:
\begin{code}
    poly zero
==  poly (F (\ i -> zero))             -- |zero| on |b <-- a|
==  \ x -> bigSum i  zero <.> pow x i  -- |poly| definition
==  \ x -> bigSum i  zero              -- |zero| as annihilator
==  \ x -> zero                        -- |zero| as additive identity
==  zero                               -- |zero| on |a -> b|
\end{code}

\begin{code}
    poly one
==  poly (F (\ i -> if i == mempty then one else zero))             -- |one| on |b <-- a|
==  poly (F (\ i -> if i == Sum 0 then one else zero))              -- |mempty| on |N|
==  \ x -> bigSum i (if i == Sum 0 then one else zero) <.> pow x i  -- |poly| definition
==  \ x -> bigSum i (if i == Sum 0 then pow x i else zero)          -- simplify
==  \ x -> pow x 0                                                  -- other terms vanish
==  \ x -> one                                                      -- multiplicative identity
==  one                                                             -- |one| on |a -> b|
\end{code}

\begin{code}
    poly (F f <+> F g)
==  poly (F (\ i -> f i <+> g i))                                       -- |(<+>)| on |b <-- a|
==  \ x -> bigSum i  (f i <+> g i) <.> pow x i                          -- |poly| definition
==  \ x -> bigSum i  f i <.> pow x i <+> g i <.> pow x i                -- distributivity
==  \ x -> (bigSum i  f i <.> pow x i) <+> (bigSum i  g i <.> pow x i)  -- summation property
==  \ x -> poly (F f) x <+> poly (F g) x                                -- |poly| definition
==  poly (F f) <+> poly (F g)                                           -- |(<+>)| on |a -> b|
\end{code}

\begin{code}
    poly (F f <.> F g)
==  poly (bigSum (i,j)  i + j +-> f i <.> g j)                          -- |(<.>)| on |b <-- a|
==  bigSum (i,j)  poly (i + j +-> f i <.> g j)                          -- additivity of |poly| (previous property)
==  bigSum (i,j) (\ x -> (f i <.> g j) <.> pow x (i + j))               -- \lemref{poly +->}
==  \ x -> bigSum (i,j) (f i <.> g j) <.> pow x (i + j)                 -- |(<+>)| on functions
==  \ x -> bigSum (i,j) (f i <.> g j) <.> (pow x i <.> pow x j)         -- exponentiation property
==  \ x -> bigSum (i,j) (f i <.> pow x i) <.> (g j <.> pow x j)         -- commutativity assumption
==  \ x -> (bigSum i  f i <.> pow x i) <.> (bigSum j  g j <.> pow x j)  -- summation property
==  \ x -> poly (F f) x <.> poly (F g) x                                -- |poly| definition
==  poly (F f) <.> poly (F g)                                           -- |(<.>)| on functions
\end{code}

\note{The sum and product derivations might read more easily in reverse.}

\bibliography{bib}

\end{document}

