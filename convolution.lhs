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
\nc\bigunion{\bigcup}
\nc\has[1]{\mathop{\delta_{#1}}}
\nc\derivOp{\mathcal{D}}
%% \nc\derivsOp{\derivOp^{\ast}}
%% \nc\deriv[1]{\mathop{\derivOp_{#1}}}
%% \nc\derivs[1]{\mathop{\derivsOp_{#1}}}
%% \nc\conv{\ast}
\nc\conv{*}
\nc\zero{\mathbf{0}}
\nc\one{\mathbf{1}}
%% \nc\zero{0}
%% \nc\one{1}
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

\DeclareMathOperator{\true}{true}
\DeclareMathOperator{\false}{false}

\begin{document}

\maketitle

%% \begin{abstract}
%% ...
%% \end{abstract}

\sectionl{Introduction}

%format <+> = "+"
%format <.> = "\conv"
%% %format zero = 0
%% %format one = 1
%format zero = "\zero"
%format one = "\one"

%format `elem` = "\mathbin{`\Varid{elem}`}"
%format <# = "\in"

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
Languages are commonly built up via a few simple operations:\notefoot{I may want to parametrize by a monoid instead of an alphabet.}
\begin{itemize}
\item The \emph{empty} language $\emptyset = \set{}$.
\item For a string $s$, the \emph{singleton} language $\single s = \set{s}$.
\item For two languages $P$ and $Q$, the \emph{union} $P \union Q = \set{s \mid s \in P \lor s \in Q}$.
\item For two languages $P$ and $Q$, the element-wise \emph{concatenation} $P \cat Q = \set{p \mappend q \mid p \in P \land q \in Q}$, where ``$\mappend$'' denotes string concatenation.
\item For a language $P$, the \emph{closure} $\closure P = \bigunion_{n \ge 0} P^n $, where $P^n$ is $P$ concatenated with itself $n$ times\out{ (and $P^0 = \single{\mempty}$)}.
\end{itemize}
%if False
\out{Note that $\closure P$ can also be given a recursive specification: $\closure P = \mempty \union P \cat \closure P$.{Syntactically, we'll take concatenation (``$\cat$'') to bind more tightly than union (``$\union$''), so the RHS of this definition is equivalent to $\mempty \union (P \cat \closure P)$}
%endif
These operations suffice to describe all \emph{regular} languages.
The language specifications (language-denoting \emph{expressions} rather than languages themselves) finitely constructed from these operations are called \emph{regular expressions}.
%(If we allow \emph{recursive} definitions, we get \emph{context-free} languages.)

Some observations:
\begin{itemize}
\item Union is associative, with $\emptyset$ as its identity.\notefoot{Maybe state equations for this observations and the next two.}
\item Element-Wise concatenation is associative and commutative, with $\single \mempty$ as its identity, where $\mempty$ is the empty string.
\item Left- and right-concatenation distribute over union.
\item The empty language annihilates under concatenation, i.e., $P \cat \emptyset = \emptyset \cat Q = \emptyset$.
\item The $\closure P$ operation satisfies the equation $\closure P = \mempty \union (P \cat \closure P)$.
\end{itemize}
These observations are the defining properties of a \emph{star semiring} (also called a \emph{closed semiring}) \needcite{}.
\figrefdef{classes}{Abstract interface for languages (and later generalizations)}{
\begin{code}
class Semiring a where
  infixl 7 <.>
  infixl 6 <+>
  zero    , one    :: a
  (<+>)   , (<.>)  :: a -> a -> a

class Semiring a => ClosedSemiring a where
  closure :: a -> a
  closure p = q where q = one <+> p <.> q  -- default

class HasSingle a w | a -> w where
  single :: w -> a
\end{code}
\vspace{-4ex}
} shows Haskell classes for representations of languages (and later generalizations), combining the star semiring vocabulary with an operation for singletons.
The singleton-forming operation must satisfy the following properties:
\begin{align*}
\single \mempty &= \one \\
\single {u \mappend v} &= \single u \conv \single v
\end{align*}
i.e., |single| is a monoid homomorphism (targeting the product monoid).

The semiring interface has a corresponding notion of structure preservation:
\begin{definition}
A function |h| from one semiring to another is called \emph{semiring homomorphism} exactly when the following conditions hold:
\begin{code}
h zero == zero
h one == one
forall a b NOP . NOP h (a  <+>  b) == h a  <+>  h b
forall a b NOP . NOP h (a  <.>  b) == h a  <.>  h b
\end{code}
\end{definition}
\mynote{Explain the value of homomorphisms to the methodology of this paper: simple and consistent specification style, non-leaky abstraction, guarantee that the laws hold. Refer to my TCM and AD papers.}

Languages as sets fulfill this combined interface as described above and again in the pseudocode in \figrefdef{set}{Abstract sets as a ``language''}{
\begin{code}
instance Monoid s => Semiring (Pow s) where
  zero  = emptyset
  one   = single mempty
  p  <+>  q  = p `union` q
  p  <.>  q  = set (u <> v | u <# p && v <# q)

instance ClosedSemiring (Pow s)  -- default |closure|

instance HasSingle (Pow s) s where single s = set s
\end{code}
\vspace{-4ex}
%%  closure p = bigunion (n >= 0) (pow p n)
}, which generalizes from strings to any monoid.\footnote{The |Monoid| class defines |mempty| and |mappend|.}\notefoot{On second thought, postpone generalization from lists to monoids later.}\notefoot{Move the |sum| and |product| definitions to their first use.}
More concretely, we might instead use a type of (possibly infinite) lists, as in \figrefdef{list}{Lists as a language representation}{
\begin{code}
instance Monoid a => Semiring [a] where
  zero = []
  one = [mempty]
  p  <+>  q = p ++ q
  p  <.>  q = [u <> v | u <- p, v <- q]

instance Monoid a => ClosedSemiring [a] -- default

instance HasSingle [a] a where single a = [a]
\end{code}
\vspace{-4ex}
}.
Lists relate to sets as follows:
\begin{code}
listElems :: [a] -> Pow a
listElems = foldr insert emptyset where insert a as = single a `union` as
\end{code}
The instance definitions in \figreftwo{set}{list} bear a family resemblance to each other, which we can readily make precise:
\begin{theorem}[\provedIn{theorem:list}]\thmLabel{list}
Given the definitions in \figref{list}, |listElems| is a homomorphism with respect to each instantiated class.
\end{theorem}
%% Further, one can take this homomorphism property as an algebraic \emph{specifications} and \emph{calculate} the instance definitions in \figref{list}, explaining the resemblances.

\sectionl{Matching}

Now consider how we can computably \emph{match} a string for membership in a language described in the vocabulary given in the previous section.
The set-based language definition does not lead directly to effective string matching, because the sets may be infinite.
The list and finite set types do have computable membership testing so we could use them instead.\notefoot{Finite sets \needcite{} would not support closure, due to finiteness.}
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
  Pred f  <.>  Pred g = Pred (\ w -> bigOrQ (u,v BR u <> v == w) f u && g v)

instance (Monoid a, Eq a) => ClosedSemiring (Pred a)  -- default |closure|

instance Eq a => HasSingle (Pred a) a where
  single w = Pred (\ w' -> w' == w)
\end{code}
\vspace{-4ex}
}.
When the monoid |a| is a list, we can also express the product operation in a more clearly computable form via list \emph{splittings}:
\begin{code}
  Pred f <.> Pred g  = Pred (\ w -> or [ f u && g v | (u,v) <- splits w ])
\end{code}
where |splits| inverts list concatenation:
\begin{code}
splits :: [a] -> [([a],[a])]
splits []      = [([],[])]
splits (a:as)  = ([],a:as) : [((a:l),r) | (l,r) <- splits as]
\end{code}
Sets and predicates have the same sort of relationship as between sets and lists (\thmRef{list}), though symmetrically:
\begin{theorem}[\provedIn{theorem:pred}]\thmLabel{pred}
Given the definitions in \figref{pred}, |setPred| and |predSet| are homomorphisms (and together form an isomorphism) with respect to each instantiated class.
\end{theorem}

\sectionl{Beyond Booleans}

As an example other than numbers and languages, booleans form a star semiring:
\begin{code}
instance Semiring Bool where
  zero  = False
  one   = True
  (<+>) = (||)
  (<.>) = (&&)

instance ClosedSemiring Bool where
  closure b  = one <+> b <.> closure b
             = True || (b && closure b)
             = True
\end{code}

%format bigSum (lim) = "\bigSumZ{" lim "}{0}"
%format bigSumQ (lim) = "\bigSumZ{" lim "}{1.5}"
\nc\bigSumZ[2]{\displaystyle\hspace{-#2ex}\sum_{\substack{#1}}\hspace{-#2ex}}
%format <-- = "\leftarrow"

\noindent
Re-examining the instances in \figref{pred}, we can see uses of |False|, |(||||)|, and |(&&)|, as well as an equality test (for |single w|), which yields |False| or |True|.
We can therefore easily generalize the codomain of ``predicates'' from booleans to \emph{any} semiring, as in \figrefdef{FunTo}{|b <-- a| as generalized language representation}{
\begin{code}
newtype b <-- a = F (a -> b)

instance (Semiring b, Monoid a, Eq a) => Semiring (b <-- a) where
  zero = F (\ w -> zero)
  one = single mempty
  F f  <+>  F g = F (\ w -> f w <+> g w)
  F f  <.>  F g = F (\ w -> bigSumQ (u,v BR u <> v == w) f u <.> g v)

instance (Monoid a, Eq a) => ClosedSemiring (b <-- a)

instance Eq a => HasSingle (b <-- a) a where
  single w = F (\ w' -> boolVal (w' == w))

boolVal :: Semiring s => Bool -> s
boolVal False  = zero
boolVal True   = one
\end{code}
\vspace{-4ex}
}.
It will be useful to reverse the usual notation from ``|a -> b|'' to ``|b <-- a|''.
\begin{theorem}[\provedIn{theorem:FunTo}]\thmLabel{FunTo}
Given the instance definitions in \figref{FunTo}, |b <-- a| satisfies the laws of the instantiated classes whenever |a| is a monoid and |b| is a semiring.
\end{theorem}

When the monoid |a| is a list, we can again express the product operation from \figref{FunTo} in a more clearly computable form:
\begin{code}
  F f <.> F g  = F (\ w -> sum [ f u <.> g v | (u,v) <- splits w ])
\end{code}

One reason to introduce the new data type |b <-- a| is to allow us to define a simpler instance for functions in which operations are defined pointwise, as in \figrefdef{function}{|a -> b| as generalized language representation}{
\begin{code}
instance Semiring b => Semiring (a -> b) where
  zero  = \ a -> zero
  one   = \ a -> one
  f  <+>  g  = \ a -> f a <+> g a
  f  <.>  g  = \ a -> f a <.> g a

instance StarSemiring b => StarSemiring (a -> b) where
  closure f = \ a -> closure (f a)

instance HasSingle b w => HasSingle (a -> b) w where
  single w = \ a -> single w
\end{code}
\vspace{-4ex}
}.
\notefoot{Maybe a theorem here saying that these instances satisfy the necessary laws. Otherwise suggest that the reader verify. I'm unsure how to prove the closure property. Perhaps coinduction. See journal notes for 2019-01-16.}
We will use the |a -> b| semiring in \secref{Convolution}.

Another representation of functions from |a| to |b| is |Map a b|, where |Map| is an efficient representation of finite maps, i.e., partial functions defined on a finite subset of its domain \needcite{}.
\notefoot{Probably swap |Map| arguments for the required |Functor| and |Applicative| instances.}
Although we can think of |Map a b| as denoting partial functions from |a| to |b|, if we further require |b| to be semiring, we can treat missing entries as being implicitly zero, yielding a \emph{total} function:\notefoot{Describe finite maps and |findWithDefault|.}
\begin{code}
(!) :: (Ord c, Semiring s) => Map c s -> c -> s
m ! c = findWithDefault zero c m
\end{code}
\begin{theorem}[\provedIn{theorem:Map}]\thmLabel{Map}
Given the definitions in \figrefdef{Map}{Maps as a language representation}{
\begin{code}
instance (Monoid a, Ord a, Semiring b) => Semiring (Map a b) where
  zero  = empty
  one   = single one
  p  <+>  q  =  unionWith (<+>) p q
  p  <.>  q  =  fromListWith (<+>)
                  [(u <> v, s <.> t) | (u,s) <- toList p, (v,t) <- toList q]

instance Semiring s => HasSingle (Map a s) a where
  single a = singleton a one
\end{code}
\vspace{-4ex}
}, |(!)| (as a function of one argument) is a homomorphism with respect to each instantiated class.
\notefoot{Describe the |Map| operations used in \figref{Map}.}
\end{theorem}
The finiteness of finite maps interferes with giving a useful |ClosedSemiring| instance.

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
atEps :: Monoid w => (w -> b) -> b
atEps f = f mempty

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
delta p []      = p []
delta p (c:cs)  = False

deriv p = \ c cs -> p (c : cs)
\end{code}

\noindent
%format `scaleT` = .>
%format scaleT = (.>)
Understanding how |atEps| and |deriv| relate to the semiring vocabulary will help us develop an efficient implementation in \secref{Tries} below.
First, however, we'll need to generalize to representations other |a -> b|:
\begin{code}
class Semiring a => Decomposable a h s | a -> h s where
  infix 1 <:
  (<:)  :: s -> h a -> a
  atEps :: a -> s
  deriv :: a -> h a

instance Semiring b => Decomposable ([c] -> b) ((->) c) b where
  (b <: _) []      = b
  (_ <: h) (c:cs)  = h c cs
  atEps  f = f []
  deriv  f = \ c cs -> f (c : cs)
\end{code}
We'll need a way to index into |h|:
\begin{code}
class Indexable p k v | p -> k v where
  (!) :: p -> k -> v

instance Indexable (k -> v) k v where
  f ! k = f k

instance (Ord k, Semiring v) => Indexable (Map k v) k v where
  m ! c = M.findWithDefault zero c m
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
%format .> = "\cdot"
\begin{code}
deriv zero  c == zero
deriv one   c == zero
deriv (p  <+>  q) c == deriv p c <+> deriv q c
deriv (p  <.>  q) c == p mempty .> deriv q c <+> deriv p c <.> q

deriv (closure p) c == closure (p mempty) .> deriv p c * closure p

deriv (single [d]) c == boolVal (d == c)
\end{code}
where |(.>)| scales the result of a function:\footnote{Equivalently, |deriv (p  <.>  q) c = delta p * deriv q c <+> deriv p c <.> q|, where |delta p = p mempty .> one|, generalizing a notion of \citet[Definition 3.2]{Brzozowski64}.}
\begin{code}
infixl 7 .>
(.>) :: Semiring s => s -> (a -> s) -> (a -> s)
s .> f  = \ a -> s * (f a)
        = (s NOP *) . f
\end{code}
\end{lemma}
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

\sectionl{Tries}

%format :< = "\mathrel{\Varid{:\!\!\triangleleft}}"

Since a language is a set of strings, we have considered representations of such sets as lists and as predicates.
Another choice of language representation is the \emph{trie}, as introduced by Thue in 1912, according to Knuth \needcite{}.
As shown by Hinze \needcite{}, tries can be extended to represent not just sets but partial functions, as well as defined generically for partial functions from types other than strings.
Putting genericity aside\notefoot{Re-raise later?} and restricting our attention to functions of lists (``strings''), we can formulate a simple trie data type as follows:

> data Trie c s = s :< Map c (Trie c s)

The similarity between the |Trie| type and the function decomposition from \secref{Decomposing Functions} (motivating the constructor's name) makes the denotation of tries quite simple to express:\footnote{Equivalently, |trieFun (e :< d) = e <: \ c cs -> trieFun (d ! c) cs|.}
\begin{code}
trieFun :: Ord c => Trie c s -> ([c] -> s)
trieFun (e :< d) = e <: trieFun . (d NOP !)
\end{code}
Likewise, the properties from section \secref{Decomposing Functions} make it fairly easy to calculate instances for |Trie|.
\begin{theorem}[\provedIn{theorem:Trie}]\thmLabel{Trie}
Given the definitions in \figrefdef{Trie}{Tries as a language representation}{
%format OD c s = Ord c
\begin{code}
data Trie c s = s :< Map c (Trie c s)

instance OD c s => Decomposable (Trie c s) (Map c) s where
  a <: d = a :< d
  atEps  (a  :<  d) = a
  deriv  (a  :<  d) = d

scaleT :: (Ord c, Semiring s) => s -> Trie c s -> Trie c s
s `scaleT` (e :< ts) = (s <.> e) :< fmap (s NOP `scaleT`) ts

instance Ord c => Semiring (Trie c s) where
  zero = zero :< empty
  one  = one  :< empty
  (a :< dp) <+> (b :< dq) = (a <+> b) :< unionWith (<+>) dp dq
  (a :< ps) <.> q = a `scaleT` q <+> (zero :< fmap (<.> NOP q) ps)

instance Ord c => StarSemiring (Trie c s) where
  closure (a :< dp) = q where q = closure a .> (one <: (<.> NOP q) .  dp)

instance Ord c => HasSingle (Trie c s) [c] where
  single w = product [zero :< singleton c one | c <- w]
\end{code}
\vspace{-4ex}
}, |trieFun| is a homomorphism with respect to each instantiated class.
\notefoot{Consider making |scaleT| be a method of a new class. Derive instances homomorphically. Maybe a semimodule will be additive plus scalable.}
\notefoot{I think we could exploit a |Semiring b => Semiring (Map c b)| instance and so replace |unionWith (<+>)| by |(<+>)| here. Maybe also something for |single w|.}

\end{theorem}

\workingHere

\sectionl{Regular Expressions}

\mynote{A sort of ``free'' variant of functions. Easy to derive homomorphically.}

\sectionl{Convolution}

%format bar (x) = "\bar{"x"}"
%format blam = "\bar{\lambda}"

Consider again the definition of semiring ``multiplication'' on functions |f,g :: b <-- a| from \figref{FunTo}, for now eliding the |F| constructors:\notefoot{To do: try \emph{with} all of the required |F| constructors. Try also with lighter-weight notation for |F|. For instance, replace ``|F f|'' by ``|bar f|'' and ``|\ w -> cdots|'' by ``|blam w -> cdots|''.}
\begin{equation}\eqnlabel{convolution}
(f * g)\,w = \bigSumZ{u,v \\ u \mappend v = w}1 f\,u * g\,v
\end{equation}
If we specialize the functions' codomains to |Bool|, we get the definition in \figref{pred}:

>   (f  <.>  g) w = bigOrQ (u,v BR u <> v == w) f u && g v

Using the set/predicate isomorphism from \secref{Matching}, we can translate this definition from predicates to sets, as in \figref{set}:

>   p  <.>  q  = set (u <> v | u <# p && v <# q)

which is the definition of the concatenation of two languages from \secref{Languages}.

By specializing the \emph{domain} of the functions to sequences (from general monoids), we can get efficient matching of semiring-generalized ``languages'', as in \secreftwo{Decomposing Functions}{Tries}, which translates to regular expressions (\secref{Regular Expressions}), generalizing work of \citet{Brzozowski64}\mynote{, while apparently improving performance.\notefoot{Measure and compare in \secref{Regular Expressions}.}}

%format R = "\mathbb R"
%format C = "\mathbb C"

Let's now consider specializing the functions' domains to \emph{integers} instead of sequences, recalling that integers (and numeric types in general) form a monoid under addition.
Thus,
\vspace{-2ex}
\begin{spacing}{2}
\begin{code}
(f <.> g) w  = bigSumQ (u,v BR u <> v == w) f u <.> g v
             = bigSumQ (u,v BR u + v == w) f u <.> g v
             = bigSumQ (u,v BR v = w - u) f u <.> g v
             = bigSum u f u <.> g (w - u)
\end{code}
\end{spacing}
\vspace{-3ex}
\noindent
which is exactly the standard definition of discrete \emph{convolution} \needcite{}\footnote{Note that this reasoning applies to \emph{any} group (monoid with inverses)}.
Therefore, just as \eqnref{convolution} generalizes language concatenation (via the predicate/set isomorphism), it also generalizes the usual notion of discrete convolution.
Moreover, if the domain is a continuous type such as |R| or |C|, we can reinterpret summation as integration, resulting in \emph{continuous} convolution \needcite{}.
Additionally, for multi-dimensional (discrete or continuous) convolution, we can simply use tuples of scalar indices for |w| and |u|, and define subtraction on tuples to be component-wise.\notefoot{More generally, cartesian products of monoids are also monoids.
Consider multi-dimensional convolution in which different dimensions have different types, even mixing discrete and continuous, and maybe even sequences and numbers.
At the least, it's useful to combine finite dimensions of different sizes.}

\mynote{Maybe give some convolution examples.}

%format Fin (m) = Fin "_{" m "}"
%format Array (m) = Array "_{" m "}"

Some uses of convolution (including convolutional neural networks \needcite{}) involve functions having finite support, i.e., non-zero on only a finite subset of their domains.\notefoot{First suggest finite maps, using instances from \figref{Map}. Then intervals/arrays.}
More specifically, these domain subsets may be defined by finite \emph{intervals}.
For instance, such a 2D operation would be given by intervals in each dimension, together specifying lower left and upper right corners of a 2D interval (rectangle) out of which the functions are guaranteed to be zero.
The two input intervals needn't have the same size, and the result occupies (is supported by) a larger interval than both inputs, with sizes equaling the sum of the sizes in each dimension (minus one for the discrete case).
\notefoot{Show an example as a picture.}
Since the result's size is entirely predictable and based only on the arguments' sizes, it is appealing to track sizes statically via types.
For instance, a 1D convolution might have the following type:
\notefoot{To do: More clearly distinguish between functions with finite support vs functions with finite domains. I think I started this paragraph with the former mindset but switched to the latter.}
\begin{code}
(*) :: Semiring s => Array (m+1) s -> Array (n+1) s -> Array (m+n+1) s
\end{code}
Unfortunately, this type is incompatible with the general type of |(*)|, in which arguments and result all have the same type.

From the perspective of functions, an array of size |n| is a memoized function from |Fin n|, which represents the finite set |0, ..., n-1|.
Although we can still define a convolution-like operation in terms of index addition, indices no longer form a monoid, simply due to the non-uniformity of types.

\sectionl{Beyond Convolution}

%format lift0
%format lift1
%format lift2
%format liftn = lift "_n"

The inability to support convolution on statically sized arrays (or other memoized forms of functions over finite domains) as semiring multiplication came from the expectation that index/argument combination is via a monoid.
This limitation is a shame, since convolution still makes sense:
\begin{code}
(f <.> g) w  = bigSumQ (u,v BR u + v == w) f u <.> g v
\end{code}
where now
\begin{code}
(+) :: Fin (m+1) -> Fin (n+1) -> Fin (m+n+1)
\end{code}
(As in \secref{Convolution}, we're continuing to elide the |F| constructors for |b <-- a| of \figref{FunTo}.)
Fortunately, this monoid expectation can be transcended by generalizing from monoidal combination to an \emph{arbitrary} binary operation |h :: a -> b -> c|.
For now, let's call this more general operation ``|lift2 h|''.
\notefoot{Say something about the mixture of ``|->|'' and ``|<--|''.}
\begin{code}
lift2 :: Semiring s => (a -> b -> c) -> (s <-- a) -> (s <-- b) -> (s <-- c)
lift2 h f g = \ w -> bigSumQ (u,v BR h u v == w) f u <.> g v
\end{code}
We can similarly lift functions of \emph{any} arity:
%format a1
%format an = a "_n"
%format f1
%format fn = f "_n"
%format u1
%format un = u "_n"
%format bigSumZ (lim) = "\bigSumZ{" lim "}{3}"
\begin{code}
liftn :: Semiring s => (a1 -> ... -> an -> b) -> (s <-- a1) -> ... -> (s <-- an) -> (s <-- b)
liftn h f1 ... fn = \ w -> bigSumZ (u1, ..., un BR h u1 cdots un == w) f1 u1 <.> cdots <.> fn un
\end{code}
Here we are summing over the set-valued \emph{preimage} of |w| under |h|.
Now consider two specific cases of |liftn|:
\begin{code}
lift1 :: Semiring s => (a -> b) -> (s <-- a) -> (s <-- b)
lift1 h f = \ w -> bigSumQ (u BR h u == w) f u

lift0 :: Semiring s => b -> (s <-- b)
lift0 b  = \ w -> bigSum (b == w) 1
         = \ w -> if b == w then one else zero
         = \ w -> boolVal (w == b)
\end{code}

\noindent
The signatures of |lift2|, |lift1|, and |lift0| resemble those of |liftA2|, |fmap|, and |pure| from the |Functor| and |Applicative| type classes \needcite:\footnote{Originally, |Applicative| had a |(<*>)| method from which one can easily define |liftA2|. Since the base library version 4.10 \needcite, |liftA2| was added as a method to allow for more efficient implementation. \mynote{Cite \href{https://ghc.haskell.org/trac/ghc/ticket/13191}{GHC ticket 13191} if I can't find a better reference.}}
\begin{code}
class Functor f where
  fmap :: (a -> b) -> f a -> f b

class Applicative f where
  pure :: b -> f b
  liftA2 :: (a -> b -> c) -> f a -> f b -> f c
\end{code}
Higher-arity liftings can be defined via these three.
(Exercise.)

For the convolution-style liftings (|lift2|, |lift1|, and |lift0|) defined above, |f t = s <-- t| (for a semiring |s|), i.e., |f = (<--) s|.
The use of |s <-- t| rather than |t -> s| is what allows us to give these instances within's Haskell's type system (and ability to infer types via first-order unification).


\workingHere


There are, however, two problems with this story:
\begin{itemize}
\item Although Haskell supports higher-kinded types \needcite{}, Haskell compilers perform type inference via first-order unification and so will not infer the needed type function |f = Lambda t DOT t -> s| (where ``|Lambda|'' is a hypothetical type-level lambda).
\item Even if such |Functor| and |Applicative| instances were accepted, they would conflict with existing instances, which are defined pointwise: |fmap h f = \ x -> h (f x)|, |pure b = \ x -> b|, and |liftA2 h f g = \ x -> h (f x) (g x)|.
\end{itemize}
There is an easy solution to both of these problems: define a new type constructor of functions but with the domain and codomain type arguments swapped:
\begin{code}
newtype b <-- a = F (a -> b)

instance Semiring s => Functor ((<--) s) where
  fmap h (F f) = F (\ w -> bigSumQ (u BR h u == w) f u)

instance Semiring s => Applicative ((<--) s) where
  pure b = F (\ w -> boolVal (w == b))
  liftA2 h (F f) (F g) = F (\ w -> bigSumQ (u,v BR h u v == w) f u <.> g v)
\end{code}
Just as with our semiring instances for functions in \figref{FunTo}, these definitions are not really executable code, since they involve summations are over potentially infinite ranges.

%format <-- = "\leftarrow"
\mynote{I should really fix the |Semiring| instances as well, since there's another |Semiring| instance that corresponds to the usual |Functor| and |Applicative| instances for functions, with |(*) = liftA2 (*)|. Delightfully, the Fourier transform is then a semiring homomorphism! Idea: rename |Fun b a| to ``|b <-- a|''.}

\workingHere

\mynote{The free semimodule monad.}

\sectionl{More Variations}

\mynote{Variations: counting, probability distributions, temporal/spatial convolution.}

\sectionl{What else?}

\begin{itemize}
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
\end{itemize}



% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

\appendix

\sectionl{Proofs}

\subsection{\thmRef{list}}\proofLabel{theorem:list}

\subsection{\thmRef{pred}}\proofLabel{theorem:pred}

\subsection{\thmRef{FunTo}}\proofLabel{theorem:FunTo}

\subsection{\thmRef{Map}}\proofLabel{theorem:Map}

\subsection{\lemRef{atEps}}\proofLabel{lemma:atEps}

\subsection{\lemRef{deriv}}\proofLabel{lemma:deriv}

For |deriv (closure p)|, see 2019-01-13 notes.

%if derivProduct
\subsection{\lemRef{derivProduct}}\proofLabel{lemma:derivProduct}

\mynote{See 2019-01-10 journal.}
%endif

\subsection{\thmRef{Trie}}\proofLabel{theorem:Trie}

\bibliography{bib}

\end{document}

