% -*- latex -*-

%% While editing/previewing, use 12pt and tiny margin.
\documentclass[twoside]{article}  % fleqn, 
\usepackage[margin=0.12in]{geometry}  % 0.12in, 0.9in, 1in

\usepackage{setspace}

%% \documentclass{article}
%% \usepackage{fullpage}

%% Temporary title
\def\tit{Efficient parsing and generalized convolution}

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
\date{Early draft of \today}

\setlength{\blanklineskip}{2ex} % blank lines in code environment

\nc\proofLabel[1]{\label{proof:#1}}
%if short
\nc\proofRef[1]{proof in \citep[Appendix C]{Elliott-2018-convolution-extended}}
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

\begin{document}

\maketitle

%% \begin{abstract}
%% ...
%% \end{abstract}

\sectionl{Introduction}

%format <+> = +
%format <.> = *
%% %format zero = 0
%% %format one = 1
%format zero = "\mathbf{0}"
%format one = "\mathbf{1}"

%format `elem` = "\mathbin{`\Varid{elem}`}"
%format <# = "\in"
%format # = "\mid"

%format paren (e) = "\left(" e "\right)"

%format Pow = "\Pow"
%format emptyset = "\emptyset"
%format (single (s)) = "\single{"s"}"
%format set (e) = "\set{"e"}"
%format bigunion (lim) (body) = "\bigunion_{" lim "}{" body "}"
%format pow a (b) = a "^{" b "}"
%format `union` = "\cup"
%format closure p = "\closure{"p"}"

\sectionl{Languages}

A \emph{language} is a set of strings, where a string is a sequence of values of some given type (``symbols'' from an ``alphabet'').
Languages are commonly built up via a few simple operations:
\notefoot{Maybe use the standard terminology |zero|, |(<+>)|, |(<.>)|, and |closure| here.}
\begin{itemize}
\item The \emph{empty} language |zero = set ()|.
\item For a string |s|, the \emph{singleton} language |single s = set s|.
\item For two languages |p| and |q|, the \emph{union} |p <+> q = set (u # u <# p || u <# q)|.
\item For two languages |p| and |q|, the element-wise \emph{concatenation} |p <.> q = set (u <> v # u <# p && v <# q)|, where ``|<>|'' denotes string concatenation.
\item For a language |p|, the \emph{closure} |closure p = bigunion (n > 0) (pow p n)|, where |pow p n| is |p| concatenated with itself |n| times.
\end{itemize}
These operations suffice to describe all \emph{regular} languages.
The language specifications (language-denoting \emph{expressions} rather than languages themselves) finitely constructed from these operations are called \emph{regular expressions}.
%(If we allow \emph{recursive} definitions, we get \emph{context-free} languages.)

Some observations:
\begin{itemize}
\item Union is associative, with |zero| as its identity.
      \notefoot{Maybe state equations for this observations and the next two.}
\item Element-Wise concatenation is associative and commutative, with |single mempty| as its identity, where |mempty| is the empty string.
\item Left- and right-concatenation distribute over union.
\item The empty language annihilates under concatenation, i.e., |p <.> zero = zero <.> q = zero|.
\item The closure operation satisfies the equation |closure p = mempty <+> p <.> closure p|.\footnote{Syntactically, we'll take concatenation (``|<.>|'') to bind more tightly than union (``|<+>|''), so the RHS of this definition is equivalent to |mempty <+> (p <.> closure p)|}
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
  closure :: a -> a
  closure p = q where q = one <+> p <.> q  -- default

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

The semiring interface has a corresponding notion of structure preservation:
\begin{definition}
A function |h| from one semiring to another is called \emph{semiring homomorphism} when the following conditions hold:
\begin{code}
h zero == zero
h one == one
forall a b NOP . NOP h (a  <+>  b) == h a  <+>  h b
forall a b NOP . NOP h (a  <.>  b) == h a  <.>  h b
\end{code}
\end{definition}
\mynote{Explain the value of homomorphisms to the methodology of this paper: simple and consistent specification style, non-leaky abstraction, guarantee that the laws hold. Refer to my TCM and AD papers.}

Languages as sets fulfill this combined interface as described above and again in the pseudocode in \figrefdef{set}{Mathematical sets as a ``language'' (pseudocode)}{
\begin{code}
instance Monoid s => Semiring (Pow s) where
  zero  = emptyset
  one   = single mempty
  p  <+>  q  = p `union` q
             = set (u | u <# p || u <# q)
  p  <.>  q  = set (u <> v | u <# p && v <# q)

instance StarSemiring (Pow s) where closure p = bigunion (n >= 0) (pow p n)

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

instance Monoid a => StarSemiring (List a)  -- default

instance HasSingle (List a) a where single a = L [a]
\end{code}
\vspace{-4ex}
}.
Rather than using lists directly, \figref{list} defines |List a|, freeing regular lists for another interpretation.
\notefoot{Refer to a later section that treats a list as a function from |Nat|, with finite lists getting padded with |zero|.}
Lists relate to sets as follows:
\begin{code}
listElems :: List a -> Pow a
listElems (L as) = foldr insert emptyset as where insert a s = single a <+> s
\end{code}
The instance definitions in \figreftwo{set}{list} bear a family resemblance to each other, which we can readily make precise:
\begin{theorem}[\provedIn{theorem:list}]\thmLabel{list}
Given the definitions in \figref{list}, |listElems| is a homomorphism with respect to each instantiated class.
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
%format DOT = "\!."
\nc\bigOrZ[2]{\hspace{-#2ex}\bigvee\limits_{\substack{#1}}\hspace{-#2ex}}
%format bigOr (lim) = "\bigOrZ{" lim "}{0}"
%format bigOrQ (lim) = "\bigOrZ{" lim "}{1.5}"
%format BR = "\\"
We can require that |predSet| (and thus |setPred|) is semiring homomorphism and solve the required homomorphism equations to yield a |Semiring| instance, as shown in \figrefdef{pred}{Membership predicate as semiring (language representation)}{
\begin{code}
newtype Pred a = Pred (a -> Bool)

instance (Monoid a, Eq a) => Semiring (Pred a) where
  zero = Pred (\ w -> False)
  one = single mempty
  Pred f  <+>  Pred g = Pred (\ w -> f w || g w)
  Pred f  <.>  Pred g = Pred (\ w -> bigOr (u,v) f u && g v && u <> v == w)

instance (Monoid a, Eq a) => StarSemiring (Pred a)  -- default |closure|

instance Eq a => HasSingle (Pred a) a where
  single w = Pred (\ w' -> w' == w)
\end{code}
\vspace{-4ex}
}.
For some monoids, including lists, we can also express the product operation in a more clearly computable form via \emph{splittings}:
\begin{code}
  Pred f <.> Pred g  = Pred (\ w -> or [ f u && g v | (u,v) <- splits w ])
\end{code}
where |splits| inverts |(<>)|:
\notefoot{Maybe generalize from \emph{lists} of pairs to an associated |Foldable|.}
\begin{code}
class Monoid t => Splittable t where
  isEmpty  :: t -> Bool     -- whether equal to |mempty|
  splits   :: t -> [(t,t)]  -- the inverse of |mappend|

instance Splittable [a] where
  isEmpty = null
  splits []      = [([],[])]
  splits (a:as)  = ([],a:as) : [((a:l),r) | (l,r) <- splits as]
\end{code}
Sets and predicates have the same sort of relationship as between sets and lists (\thmRef{list}), though symmetrically:
\begin{theorem}[\provedIn{theorem:pred}]\thmLabel{pred}
Given the definitions in \figref{pred}, |setPred| and |predSet| are homomorphisms (and together form an isomorphism) with respect to each instantiated class.
\end{theorem}

\sectionl{Booleans and Beyond}

For examples other than numbers and languages, |Bool| is a star semiring, and |a -> b| is a star semiring when |b| is, as in \figrefdef{bool and function}{Booleans and functions as semirings}{
\begin{code}
instance Semiring Bool where
  zero  = False
  one   = True
  (<+>)  = (||)
  (<.>)  = (&&)

instance StarSemiring Bool where
  closure b  = one <+> b <.> closure b
             = True || (b && closure b)
             = True

instance Semiring b => Semiring (a -> b) where
  zero  = \ a -> zero
  one   = \ a -> one
  f  <+>  g  = \ a -> f a <+> g a
  f  <.>  g  = \ a -> f a <.> g a

instance StarSemiring b => StarSemiring (a -> b) where
  closure f = \ a -> closure (f a)
\end{code}
\vspace{-4ex}
}.
\notefoot{Maybe a theorem here saying that these instances satisfy the necessary laws. Otherwise suggest that the reader verify. I'm unsure how to prove the closure property. Perhaps coinduction. See journal notes for 2019-01-16.}
\out{We will use the |a -> b| semiring in \secref{Convolution}.\notefoot{Check that we did.}}

%format bigSum (lim) (body) = "\bigSumZ{" lim "}{0}" body
%format bigSumQ (lim) (body) = "\bigSumZ{" lim "}{1.5}" body
\nc\bigSumZ[2]{\displaystyle\hspace{-#2ex}\sum_{\substack{#1}}\,\hspace{-#2ex}}
%format <-- = "\leftarrow"
%format .> = "\cdot"
%format +-> = "\mapsto"

Re-examining the instances in \figref{pred}, we can see uses of |False|, |(||||)|, and |(&&)|, as well as an equality test (for |single w|), which yields |False| or |True|.
We can therefore easily generalize the codomain of ``predicates'' from booleans to \emph{any} semiring.
It will also be useful to extend |single a| to |a +-> s|, mapping |a| to |s| and everything else to zero:
We can build |a +-> s| from |single a| and a new ``scaling'' operation |s .> p|, which multiplies each of codomain values in |p| by |s|:\footnote{
For sets, lists, and predicates, |s| will be |Bool|, e.g.,
\begin{code}
instance Monoid a => Scalable (List a) Bool where
  s .> as = if s then as else zero
\end{code}
\mynote{Maybe it's not worth bothering with |Scalable| and |(+->)| for sets, lists and predicates.}
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
Since we already have a semiring of functions (\figref{bool and function}), let's refer to the generalized |Pred a| as ``|b <-- a|'', as in \figrefdef{<--}{|b <-- a| as generalized language representation}{
\begin{code}
newtype b <-- a = F { unF :: a -> b }

instance (Semiring b, Monoid a, Eq a) => Semiring (b <-- a) where
  zero = F (\ w -> zero)
  one = single mempty
  F f  <+>  F g = F (\ w -> f w <+> g w)
  F f  <.>  F g = bigSum (u,v) (u <> v +-> f u <.> g v)

instance (Monoid a, Eq a) => StarSemiring (b <-- a)

instance (Semiring b, Eq a) => HasSingle (b <-- a) a where
  single a = F (\ a' -> boolVal (a' == a))

boolVal :: Semiring b => Bool -> b
boolVal False  = zero
boolVal True   = one

instance Semiring s => Scalable (s <-- a) s where
  s .> F f = F (\ a -> s <.> f a) 
\end{code}
\vspace{-4ex}
}.
\notefoot{If I change |HasSingle| and |Scalable| to type constructor classes, the reversal of parameters will be necessary, as it already is for |Functor|, |Applicative|, and |Monad| instances.}

\begin{theorem}[\provedIn{theorem:<--}]\thmLabel{<--}
Given the instance definitions in \figref{<--}, |b <-- a| satisfies the laws of the instantiated classes whenever |a| is a monoid and |b| is a semiring.
\end{theorem}

When the monoid |a| is a list, we can again express the product operation from \figref{<--} in a more clearly computable form:
\begin{code}
  F f <.> F g  = F (\ w -> sum [ f u <.> g v | (u,v) <- splits w ])
\end{code}

%format :<-- = "\leftarrowtriangle"

Another representation of functions from |a| to |b| is |Map a b|, where |Map| is an efficient representation of finite maps, i.e., partial functions defined on finite subsets of their domains \needcite{}.
Although we can think of |Map a b| as denoting partial functions from |a| to |b|, if we further require |b| to be semiring, we can treat missing entries as being implicitly zero, yielding a \emph{total} function.
\notefoot{Describe finite maps and |findWithDefault|.}
As with functions, it will be helpful later to flip the order of type parameters to |Map|.
\begin{theorem}[\provedIn{theorem:Map}]\thmLabel{Map}
Given the definitions in \figrefdef{Map}{Finite maps as a language representation}{
\begin{code}
newtype b :<-- a = M (Map a b) deriving Show

mapTo :: (Ord a, Semiring b) => (b :<-- a) -> (b <-- a)
mapTo (M m) = F (\ a -> findWithDefault zero a m)

instance (Monoid a, Ord a, Semiring b) => Semiring (b :<-- a) where
  zero = M empty
  one = single mempty
  M p  <+>  M q = M (unionWith (<+>) p q)
  M p  <.>  M q = M  (fromListWith (<+>)
                       [(u <> v, s <.> t) | (u,s) <- toList p, (v,t) <- toList q])

instance Semiring s => HasSingle (s :<-- a) a s where
  a +-> s = M (singleton a s)
\end{code}
\vspace{-4ex}
}, |mapTo| is a homomorphism with respect to each instantiated class.
\notefoot{Describe the |Map| operations used in \figref{Map}.}
\notefoot{Look for a better name than ``|mapTo|''.}
\end{theorem}
The finiteness of finite maps interferes with giving a useful |StarSemiring| instance.

\mynote{Define another wrapper for |[a]| that represents |a <-- Sum Nat|.
Maybe also multidimensional arrays.
Probably save for later when I discuss spatial convolution and polynomials.}

\sectionl{Decomposing Functions}

%format <: = "\blacktriangleleft"
%format <: = "\triangleleft"
%format atEps = "\Varid{at}_\epsilon"
%format deriv = "\derivOp"

The implementations in previous sections work but can be made much more efficient.
As preparation, let's now explore a decomposition of functions of lists.

Any function on lists can be expressed in terms of how it handles the empty list |[]| and non-empty lists |c:cs|, as made precise by the following definition:
\begin{code}
infix 1 <:
(<:) :: b -> (c -> [c] -> b) -> [c] -> b
(b <: h) []      = b
(b <: h) (c:cs)  = h c cs
\end{code}
\begin{lemma}\lemLabel{decompose function}
Any function from lists |f :: [c] -> b| can be decomposed as follows:
\begin{code}
f == atEps f <: deriv f
\end{code}
where
\begin{code}
atEps :: ([c] -> b) -> b
atEps f = f []

deriv :: ([c] -> b) -> c -> ([c] -> b)
deriv f = \ c cs -> f (c : cs)
\end{code}
\end{lemma}
\begin{proof}
Any argument to |f| must be either |[]| or |c : cs| for some value |c| and list |cs|.
Consider each case:
\begin{code}
    (atEps f <: deriv f) []
==  atEps f []                   -- definition of |b <: h|
==  f []                         -- definition of |atEps|
                                           
    (atEps f <: deriv f) (c:cs)  NOP
==  deriv f (c:cs)               -- definition of |b <: h|
==  f (c:cs)                     -- definition of |deriv|
\end{code}
Thus, for \emph{all} |w :: [c]|, |f w == (atEps f <: deriv f) w|, from which the lemma follows by extensionality.
\end{proof}

This decomposition generalizes a pair of operations used by \citet{Brzozowski64} mapping languages to languages (as sets of strings):\footnote{Brzozowski wrote ``$\derivOp_c\,p$'' instead of ``|deriv p c|'', but the latter will prove more convenient below.}
\begin{code}
delta p = if mempty <# p then set mempty else emptyset 

deriv p c = set (cs | c:cs <# p)
\end{code}
To see the relationship between Brzozowski's two operations and the decomposition above, recast |delta| and |deriv| in terms of predicates (functions to booleans):
\begin{code}
delta p  = \ NOP case  []   -> p []
                       _:_  -> False
         = mempty +-> p mempty
         = p mempty .> one

deriv p = \ c cs -> p (c : cs)
\end{code}

\noindent
%format `scaleT` = .>
%format scaleT = (.>)
Understanding how |atEps| and |deriv| relate to the semiring vocabulary will help us develop an efficient implementation in \secref{Tries} below.
First, however, we'll need to generalize to representations other than |b <-- a|:
\begin{code}
class Semiring a => Decomposable a h s | a -> h s where
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
\begin{code}
class Indexable p k v | p -> k v  where (!) :: p -> k -> v

instance Indexable (k -> v) k v   where f ! k = f k

instance (Ord k, Semiring v) => Indexable (Map k v) k v where (!) = mat
\end{code}

\noindent
Now adapt the |[c] -> b| instance of |Decomposable| to |b <-- [c]|:
\begin{code}
instance Semiring s => Decomposable (s <-- [c]) ((->) c) s where
  b <: h = F (b <: unF . h)
  atEps  (F f) = f mempty
  deriv  (F f) = \ c -> F (\ cs -> f (c:cs))
\end{code}

%% \begin{code}
%%   b <: h = F (\ NOP case  []    -> b
%%                           c:cs  -> unF (h c) cs)
%% \end{code}

\begin{lemma}[\provedIn{lemma:atEps}]\lemLabel{atEps}
On |b <-- a|, the |atEps| function is a star semiring homomorphism, i.e.,
\begin{code}
atEps zero         == zero
atEps one          == one
atEps (p  <+>  q)  == atEps p  <+>  atEps q 
atEps (p  <.>  q)  == atEps p  <.>  atEps q 

atEps (closure p)  == closure (atEps p)
\end{code}
Moreover, |atEps (single [d]) == zero|.

\end{lemma}
\begin{lemma}[\provedIn{lemma:deriv}, generalizing Lemma 3.1 of \citet{Brzozowski64}]\lemLabel{deriv}
Differentiation on |b <-- a|, has the following properties:
\notefoot{If I replace application to |c| by indexing by |c| (i.e., |(! NOP c)|), will this lemma hold for all of the representations? I suspect so. Idea: Define $\derivOp_c\,p = \derivOp\,p\:!\:c$.}
\begin{code}
deriv zero  c == zero
deriv one   c == zero
deriv (p  <+>  q) c == deriv p c <+> deriv q c
deriv (p  <.>  q) c == p mempty .> deriv q c <+> deriv p c <.> q

deriv (closure p) c == closure (p mempty) .> deriv p c * closure p

deriv (single [d]) c == boolVal (d == c)
\end{code}
\end{lemma}
Equivalently, |deriv (p  <.>  q) c = delta p * deriv q c <+> deriv p c <.> q|, generalizing a notion of \citet[Definition 3.2]{Brzozowski64}.
% \workingHere \mynote{I'm moving |(.>)| sooner. Fix this part.}
\begin{corollary}
The following properties hold:
\begin{code}
zero  = zero  <: \ c -> zero
one   = one   <: \ c -> zero
(a  <:  dp)  <+>  (b <: dq) = (a  <+>  b) <: (\ c -> dp c <+> dq c)
(a  <:  dp)  <.>  (b <: dq) = (a  <.>  b) <: (\ c -> a .> dq c <+> dp c <.> (b <: dq))

closure (a <: dp) = q
  where
     q = as <: (h . dp)
     as = closure a
     h d = as .> d <.> q

single w = product (map symbol w)
  where
     symbol d = zero <: (\ c -> boolVal (c == d))
\end{code}
\end{corollary}
\begin{proof}
Combine \lemRefThree{decompose function}{atEps}{deriv}.
\end{proof}

%let derivProduct = True

%if derivProduct
\begin{lemma}[\provedIn{lemma:derivProduct}]\lemLabel{derivProduct}
The following alternative characterizations of products and closure on functions hold:%
\notefoot{Since I moved the |one| addend to after |a .> q|, I think we're going to look for long matches before short ones, possibly with harmful results. Test thoroughly, and describe results later in the paper.}%
\notefoot{Check on convergence. If I can't get it, then drop this lemma, and change \figref{Trie}.}
\begin{code}
(a <: dp) <.> q = a .> q <+> (zero <: (<.> NOP q) . dp)

closure (a <: dp) = q where q = closure a .> (one <: (<.> NOP q) .  dp)
\end{code}
\end{lemma}
%endif

Returning to scaling, there's a very important optimization to be made.
When |s == zero|, |s .> p == zero|, so we can discard |p| entirely.
Rather than give this responsibility to each |Scalable| instance, let's define |(.>)| to apply this optimization on top of a more primitive |scale| method:
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

\sectionl{Tries}

%format :< = "\mathrel{\Varid{:\!\!\triangleleft}}"

Since a language is a set of strings, we have considered representations of such sets as lists and as predicates.
Another choice of language representation is the \emph{trie}, as introduced by Thue in 1912, according to Knuth \needcite{}.
As shown by Hinze \needcite{}, tries can be extended to represent not just sets but partial functions, as well as defined generically for partial functions from types other than strings.
Putting genericity aside\notefoot{Re-raise later?} and restricting our attention to functions of lists (``strings''), we can formulate a simple trie data type as follows:

> data Trie c s = s :< Map c (Trie c s)

The similarity between the |Trie| type and the function decomposition from \secref{Decomposing Functions} (motivating the constructor's name) makes the denotation of tries quite simple to express:\footnote{Equivalently, |trieFun (e :< d) = e <: \ c cs -> trieFun (d ! c) cs|.}
%format OD c s = Ord SPC c
%format OD c s = (Ord SPC c, DetectableZero SPC s)
\begin{code}
trieFun :: OD c => Trie c s -> ([c] -> s)
trieFun (e :< d) = e <: trieFun . (d NOP !)
\end{code}
Likewise, the properties from section \secref{Decomposing Functions} make it fairly easy to calculate instances for |Trie|.
\begin{theorem}[\provedIn{theorem:Trie}]\thmLabel{Trie}
Given the definitions in \figrefdef{Trie}{Tries as a language representation}{
\begin{code}
data Trie c s = s :< Map c (Trie c s)

instance OD c s => Decomposable (Trie c s) (Map c) s where
  a <: d = a :< d
  atEps  (a  :<  d) = a
  deriv  (a  :<  d) = d

scaleT :: OD c s => s -> Trie c s -> Trie c s
s `scaleT` t   | isZero s   = zero
               | otherwise  = go t
 where
   go (e :< ts) = (s <.> e) :< fmap go ts

instance OD c s => Semiring (Trie c s) where
  zero = zero :< empty
  one  = one  :< empty
  (a :< dp) <+> (b :< dq) = (a <+> b) :< unionWith (<+>) dp dq
  (a :< ps) <.> q = a `scaleT` q <+> (zero :< fmap (<.> NOP q) ps)

instance OD c s => StarSemiring (Trie c s) where
  closure (a :< dp) = q where q = closure a .> (one <: (<.> NOP q) .  dp)

instance OD c s => HasSingle (Trie c s) [c] where
  single w = product [zero :< singleton c one | c <- w]
\end{code}
\vspace{-4ex}
}, |trieFun| is a homomorphism with respect to each instantiated class.
\notefoot{Consider making |scaleT| be a method of a new class. Derive instances homomorphically. Maybe a semimodule will be additive plus scalable.}
\notefoot{I think we could exploit a |Semiring b => Semiring (Map c b)| instance and so replace |unionWith (<+>)| by |(<+>)| here. Maybe also something for |single w|. I might want to use \emph{total maps} \citep{Elliott-2009-tcm}, especially in \secref{Beyond Convolution}.}
\end{theorem}
Note again the important optimization for |zero `scaleT` t = zero|, eliminating the entire, possibly infinite trie |t|.
This optimization applies quite often in practice, since languages tend to be sparse.

\sectionl{Regular Expressions}

\mynote{A sort of ``free'' variant of functions. Easy to derive homomorphically.}

\sectionl{Convolution}

%format bar (x) = "\bar{"x"}"
%format blam = "\bar{\lambda}"

Consider again the definition of semiring ``multiplication'' on functions |f,g :: b <-- a| from \figref{<--}, temporarily eliding the |F| constructors:
\notefoot{To do: try \emph{with} all of the required |F| constructors. Try also with lighter-weight notation for |F|. For instance, replace ``|F f|'' by ``|bar f|'' and ``|\ w -> cdots|'' by ``|blam w -> cdots|''.}
\begin{equation}\eqnlabel{convolution}
(f * g)\,w = \bigSumZ{u,v \\ u \mappend v = w}1 f\,u * g\,v
\end{equation}
If we specialize the functions' codomains to |Bool|, we get the definition in \figref{pred}:

>   (f  <.>  g) w = bigOrQ (u,v BR u <> v == w) f u && g v

Using the set/predicate isomorphism from \secref{Matching}, we can translate this definition from predicates to sets, as in \figref{set}:

>   p  <.>  q  = set (u <> v | u <# p && v <# q)

which is the definition of the concatenation of two languages from \secref{Languages}.

By specializing the \emph{domain} of the functions to sequences (from general monoids), we can get efficient matching of semiring-generalized ``languages'', as in \secreftwo{Decomposing Functions}{Tries}, which translates to regular expressions (\secref{Regular Expressions}), generalizing work of \citet{Brzozowski64}\mynote{, while apparently improving performance.
\notefoot{Measure and compare in \secref{Regular Expressions}.}}

%format R = "\mathbb R"
%format C = "\mathbb C"

Let's now consider specializing the functions' domains to \emph{integers} instead of sequences, recalling that integers (and numeric types in general) form a monoid under addition.
\vspace{-2ex}
\begin{spacing}{2}
\begin{code}
(f <.> g) w  = bigSumQ (u,v BR u <> v == w) (f u <.> g v)
             = bigSumQ (u,v BR u + v == w) (f u <.> g v)
             = bigSumQ (u,v BR v = w - u) (f u <.> g v)
             = bigSum u (f u <.> g (w - u))
\end{code}
\end{spacing}
\vspace{-3ex}
\noindent
which is the standard definition of discrete \emph{convolution} \needcite{}\footnote{Note that this reasoning applies to \emph{any} group (monoid with inverses)}.
Therefore, just as \eqnref{convolution} generalizes language concatenation (via the predicate/set isomorphism), it also generalizes the usual notion of discrete convolution.
Moreover, if the domain is a continuous type such as |R| or |C|, we can reinterpret summation as integration, resulting in \emph{continuous} convolution \needcite{}.
Additionally, for multi-dimensional (discrete or continuous) convolution, we can simply use tuples of scalar indices for |w| and |u|, and define tuple subtraction componentwise.
\notefoot{More generally, cartesian products of monoids are also monoids.
Consider multi-dimensional convolution in which different dimensions have different types, even mixing discrete and continuous, and maybe even sequences and numbers.
At the least, it's useful to combine finite dimensions of different sizes.}
\begin{theorem}[\provedIn{theorem:Fourier}]\thmLabel{Fourier}
The Fourier transform is a semiring homomorphism from |a -> b| to |b <- a|.
\end{theorem}

\mynote{Maybe give some convolution examples.}

%format Fin (m) = Fin "_{" m "}"
%format Array (m) = Array "_{" m "}"

Some uses of convolution (including convolutional neural networks \needcite{}) involve functions having finite support, i.e., non-zero on only a finite subset of their domains.
\notefoot{First suggest finite maps, using instances from \figref{Map}. Then intervals/arrays.}
In many cases, these domain subsets may be defined by finite \emph{intervals}.
For instance, such a 2D operation would be given by intervals in each dimension, together specifying lower left and upper right corners of a 2D interval (rectangle) out of which the functions are guaranteed to be zero.
The two input intervals needn't have the same size, and the result occupies (is supported by) a larger interval than both inputs, with sizes equaling the sum of the sizes in each dimension (minus one for the discrete case).
\notefoot{Show an example as a picture.}
Since the result's size is entirely predictable and based only on the arguments' sizes, it is appealing to track sizes statically via types.
For instance, a 1D convolution might have the following type:
\notefoot{To do: More clearly distinguish between functions with finite support vs functions with finite domains. I think I started this paragraph with the former mindset but switched to the latter.}
\begin{code}
(*) :: Semiring s => Array (m+1) s -> Array (n+1) s -> Array (m+n+1) s
\end{code}
Unfortunately, this signature is incompatible with the general type of |(*)|, in which arguments and result all have the same type.

From the perspective of functions, an array of size |n| is a memoized function from |Fin n|, which represents the finite set |set (0, ..., n-1)|.
Although we can still define a convolution-like operation in terms of index addition, indices no longer form a monoid, simply due to the non-uniformity of types.

\sectionl{Beyond Convolution}

%format lift0
%format lift1
%format lift2
%format liftn = lift "_n"

The inability to support convolution on statically sized arrays (or other memoized forms of functions over finite domains) as semiring multiplication came from the expectation that index/argument combination is via a monoid.
This limitation is a shame, since convolution still makes sense:
\begin{code}
(f <.> g) w  = bigSumQ (u,v BR u + v == w) (f u <.> g v)
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
lift2 h f g = \ w -> bigSumQ (u,v BR h u v == w) (f u <.> g v)
\end{code}
We can similarly lift functions of \emph{any} arity:
%format a1
%format an = a "_n"
%format f1
%format fn = f "_n"
%format u1
%format un = u "_n"
%format bigSumZ (lim) (body) = "\bigSumZ{" lim "}{3}" body
\begin{code}
liftn :: Semiring s => (a1 -> ... -> an -> b) -> (s <-- a1) -> ... -> (s <-- an) -> (s <-- b)
liftn h f1 ... fn = \ w -> bigSumZ (u1, ..., un BR h u1 cdots un == w) (f1 u1 <.> cdots <.> fn un)
\end{code}
Here we are summing over the set-valued \emph{preimage} of |w| under |h|.
Now consider two specific cases of |liftn|:
\begin{code}
lift1 :: Semiring s => (a -> b) -> (s <-- a) -> (s <-- b)
lift1 h f = \ w -> bigSumQ (u BR h u == w) (f u)

lift0 :: Semiring s => b -> (s <-- b)
lift0 b  = \ w -> bigSum (b == w) one
         = \ w -> if b == w then one else zero
         = \ w -> boolVal (w == b)
\end{code}

%format FunctorC = Functor
%format ApplicativeC = Applicative
%format fmapC = fmap
%format pureC = pure
%format liftA2C = liftA2
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

instance Functor Pow where
  fmap h p = set (h a | a <# p)

instance Applicative Pow where
  pure b  = set b
          = pure b
  liftA2 h p q = set (h a b | a <# p && b <# q)

instance Functor [] where
  fmap h as = [h a | a <- as]

instance Applicative [] where
  pure b  = [b]
          = single b
  liftA2 h as bs = [h a b | a <- as, b <- bs]

newtype b :<-- a = M (Map a b)

instance Semiring b => FunctorC ((:<--) b) where
  type Ok ((:<--) b) a = Ord a
  fmapC h (M p) = M (fromListWith (<+>) [(h a, b) | (a,b) <- toList p])

instance Semiring b => ApplicativeC ((:<--) b) where
  pureC a  = M (singleton a one)
           = single a
  liftA2C h (M p) (M q) =
    M (fromListWith (<+>) [(h a b, s <.> t) | (a,s) <- toList p, (b,t) <- toList q])

instance Functor ((->) a) where
  fmap h f = \ a -> f (h a)

instance Applicative ((->) a) where
  pure b  = \ a -> b
          = single b
  liftA2 h f g = \ a -> h (f a) (g a)

instance Semiring b => Functor ((<--) b) where
  type Ok ((<--) b) a = Eq a
  fmap h (F f) = F (\ w -> bigSumQ (u BR h u == w) (f u))

instance Semiring b => Applicative ((<--) b) where
  pure a  = F (\ w -> boolVal (w == a))
          = single a
  liftA2 h (F f) (F g) = F (\ w -> bigSumQ (u,v BR h u v == w) (f u <.> g v))
\end{code}
}, along with instances for some of the language representations we've considered so far.%
\footnote{The enhancement is the associated constraint \citep{Bolingbroke2011CK} |Ok|, limiting the types that the class methods must support. The line ``|type Ok f a = ()|'' means that the constraint on |a| defaults to |()|, which holds vacuously for all |a|.}%
\footnote{Originally, |Applicative| had a |(<*>)| method from which one can easily define |liftA2|. Since the base library version 4.10 \needcite, |liftA2| was added as a method (along with a default definition of |(<*>)|) to allow for more efficient implementation. \mynote{Cite \href{https://ghc.haskell.org/trac/ghc/ticket/13191}{GHC ticket 13191} if I can't find a better reference.}}
Higher-arity liftings can be defined via these three.
(Exercise.)
The use of |s <-- t| as an alternative to |t -> s| allows us to give instances for both and to stay within Haskell's type system (and ability to infer types via first-order unification).
For |b <-- a|, these definitions are not really executable code, since they involve summations are over potentially infinite ranges (as with our semiring instances for |b <-- a| in \figref{<--}).
\begin{theorem}
For each instance defined in \figref{FunApp}, the following equalities hold:
\notefoot{Probe more into the pattern of |single = pure|, |one = single mempty| and |(*) = liftA2 (<>)|.
Also the relationship between forward and reverse functions and maps.}
\begin{code}
single  = pure
one     = single mempty
(*)     = liftA2 (<>)
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
\begin{theorem}[\provedIn{theorem:decompose liftA2}]\thmLabel{decompose liftA2}
Every function |f :: b <-- a| can be decomposed into this basis as follows:
\notefoot{I'm not assuming finite support, which is part of the usual definition but problematic for the applications in this paper. Is there a problem with dropping finite support and finiteness of linear combinations?}
\begin{code}
F f = bigSum u (f u .> single u)
\end{code}
\vspace{-4ex}
\end{theorem}

The monad instance is defined as follows:\footnote{The |return| method does not appear here, since it is equivalent to |pure| from Applicative.}
\begin{code}
instance Semiring s => Monad ((<--) s) where
  (>>=) :: (s <-- a) -> (a -> (s <-- b))) -> (s <-- b)
  F f >>= h = bigSum a (f a) .> unF (h a)
\end{code}
\vspace{-4ex}
\begin{theorem}[\provedIn{theorem:standard FunApp}]\thmLabel{standard FunApp}
The definitions of |fmap| and |liftA2| on |((<--) b)| in \figref{FunApp} satisfy the following standard equations for monads:
\begin{code}
fmap f p = p >>= \ a -> pure (f a)

liftA2 h p q  = p >>= \ u -> q >>= \ v -> pure (h u v)
              = p >>= \ u -> fmap (h u) q
\end{code}
\end{theorem}

\workingHere

\begin{theorem}
The following property holds:
\begin{code}
   liftA2 h (F f) (F g)
=  F (\ w -> bigSum (u,v) f u * g v * pure (h u v) w)
=  bigSum (u,v) ((f u * g v) .> single (h u v))
=  bigSum u (f u .> bigSum v (g v .> single (h u v)))
=  bigSum u (f u .> fmap (h u) (F g))
\end{code}
\vspace{-3ex}
\end{theorem}

\mynote{
\begin{itemize}
\item We no longer need to open up |F g|.
   Instead, |liftA2 h (F f) q = bigSum u (f u .> fmap (h u) q)|.
\item Hm! This form looks a lot like a Brzozowski-style language convolution implementation I've used, with |h = (<>)| and |fmap (u NOP <>) q| implemented carefully.
\item I think I want to use this sort of formulation as early as \figref{<--}. Simplify \proofRef{theorem:standard FunApp}.
\end{itemize}
}

\sectionl{More Variations}

\mynote{Variations: counting, probability distributions, temporal/spatial convolution.}

\sectionl{What else?}

\begin{itemize}
\item Context-free languages (recursion).
\item Other applications:
\begin{itemize}
  \item Univariate and multivariate polynomials.
  \item Convolution: discrete and continuous, one- and multi-dimensional, dense and sparse.
  \item Probability distributions.
  \item 2D parsing?
\end{itemize}
\end{itemize}

\sectionl{Related Work}
\begin{itemize}
\item \emph{Fun with semirings}
\item \emph{Polynomial Functors Constrained by Regular Expressions}
\item \href{https://doisinkidney.com/}{Donnacha Oisín Kidney's blog}
\item Dan Piponi's blog
\item Many more references in \verb|todo.md|.
\end{itemize}


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

\appendix

\sectionl{Proofs}

\subsection{\thmRef{list}}\proofLabel{theorem:list}

\subsection{\thmRef{pred}}\proofLabel{theorem:pred}

\subsection{\thmRef{<--}}\proofLabel{theorem:<--}

\subsection{\thmRef{Map}}\proofLabel{theorem:Map}

\subsection{\lemRef{atEps}}\proofLabel{lemma:atEps}

\subsection{\lemRef{deriv}}\proofLabel{lemma:deriv}

For |deriv (closure p)|, see 2019-01-13 notes.

%if derivProduct
\subsection{\lemRef{derivProduct}}\proofLabel{lemma:derivProduct}

\mynote{See 2019-01-10 journal.}
%endif

\subsection{\thmRef{Trie}}\proofLabel{theorem:Trie}

\subsection{\thmRef{Fourier}}\proofLabel{theorem:Fourier}

%format F = "\mathcal F"
\mynote{Additivity of |F|, and the convolution theorem. What about |closure p| and $single w$?}

\subsection{\thmRef{standard FunApp}}\proofLabel{theorem:standard FunApp}

First consider |fmap|, as defined in \figref{FunApp}.
Eliding the |F| constructors,
\begin{spacing}{1.5}
\begin{code}
    fmap h f
==  \ w -> bigSumQ (u BR h u == w) (f u)                              -- definition of |fmap| on |(<--) b|
==  \ w -> bigSum u (if h u == w then f u else zero)                  -- |zero| as additive identity
==  \ w -> bigSum u (if h u == w then f u <.> one else f u <.> zero)  -- semiring laws
==  \ w -> bigSum u (f u <.> (if h u == w then one else zero))        -- refactor |if|
==  bigSum u (\ w -> f u <.> (if h u == w then one else zero))        -- addition of functions
==  bigSum u (f u .> (\ w -> if h u == w then one else zero))         -- definition of |(.>)|
==  bigSum u (f u .> pure (h u))                                      -- definition of |pure|
==  f >>= \ u -> pure (h u)                                           -- definition of |(>>=)|
\end{code}
\end{spacing}
\noindent
Similarly for |liftA2|:
\begin{spacing}{1.5}
\begin{code}
    liftA2 h f g
==  \ w -> bigSumQ (u,v BR h u v == w) (f u <.> g v)
==  bigSum (u,v) ((f u <.> g v) .> pure (h u v))
==  bigSum (u,v) (f u .> (g v .> pure (h u v)))
==  bigSum u (f u .> paren (bigSum v (g v .> pure (h u v))))
== f >>= \ u -> g >>= \ v -> pure (h u v)
\end{code}
\end{spacing}

\subsection{\thmRef{decompose liftA2}}\proofLabel{theorem:decompose liftA2}

\mynote{Will become trivial when I re-express |fmap|. Then the result follows from |fmap id == id|.}

\bibliography{bib}

\end{document}

