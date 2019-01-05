% -*- latex -*-

%% While editing/previewing, use 12pt and tiny margin.
\documentclass[twoside]{article}  % fleqn, 
\usepackage[margin=0.12in]{geometry}  % 0.12in, 0.9in, 1in

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
\nc\provedIn[1]{\textnormal{See proof \citep[Appendix C]{Elliott-2018-convolution-extended}}}
%else
\nc\proofRef[1]{Appendix \ref{proof:#1}}
\nc\provedIn[1]{\textnormal{Proved in \proofRef{#1}}}
%endif

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
\nc\derivsOp{\derivOp^{\ast}}
\nc\deriv[1]{\mathop{\derivOp_{#1}}}
\nc\derivs[1]{\mathop{\derivsOp_{#1}}}
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
\nc\liftATwo{\mathop{\Varid{liftA_2}}}
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

\sectionl{Languages}

\mynote{Summarize/review languages as sets, including singleton, union, concatenation, and star/closure.}

A \emph{language} is a set of strings, where a string is a sequence of values of some given type (``symbols'' from an ``alphabet'').
Languages are commonly built up via a few simple operations:\notefoot{I may want to parametrize by a monoid instead of an alphabet.}
\begin{itemize}
\item The \emph{empty} language $\emptyset = \set{}$.
\item For a string $s$, the \emph{singleton} language $\single s = \set{s}$.
\item For two languages $P$ and $Q$, the \emph{union} $P \union Q = \set{s \mid s \in P \lor s \in Q}$.
\item For two languages $P$ and $Q$, the element-wise \emph{concatenation} $P \cat Q = \set{p \mappend q \mid p \in P \land q \in Q}$, where ``$\mappend$'' denotes string concatenation.
\item For a language $P$, the \emph{closure} $\closure P = \bigunion_{n \ge 0} P^n $, where $P^n$ is $P$ concatenated with itself $n$ times (and $P^0 = \single{\mempty}$).
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
\item Left- and right-concatenation distributes over union.
\item The empty language annihilates under concatenation, i.e., $P \cat \emptyset = \emptyset \cat Q = \emptyset$.
\item The $\closure P$ operation satisfies the equation $\closure P = \mempty \union (P \cat \closure P)$.
\end{itemize}
These observations are the defining properties of a \emph{star semiring} (also called a \emph{closed semiring}) \needcite{}.
\figrefdef{classes}{Abstract interface for languages (and later generalizations)}{
\begin{code}
class Semiring a where
  infixl 7 <.>
  infixl 6 <+>
  zero   , one    :: a
  (<+>)  , (<.>)  :: a -> a -> a

class Semiring a => ClosedSemiring a where
  closure :: a -> a
  closure p = q where q = one <+> p <.> q  -- default

class HasSingle a x where
  single :: x -> a

instance Semiring Bool where
  zero  = False
  one   = True
  (<+>)  = (||)
  (<.>)  = (&&)

instance ClosedSemiring Bool where
  closure _ = one
\end{code}
\vspace{-4ex}
} shows Haskell classes for representations of languages (and later generalizations), combining the star semiring vocabulary with an operation for singletons.
The singleton-forming operation must satisfy the following properties:
\begin{align*}
\single \mempty &= \one \\
\single {u \mappend v} &= \single u \conv \single v
\end{align*}
i.e., |single| is a monoid homomorphism (targeting the product monoid).
As an example other than numbers and languages, \figref{classes} includes the closed semiring of boolean values.

%format Set = "\mathcal P"
%format emptyset = "\emptyset"
%format single (s) = "\single{"s"}"
%format set (e) = "\set{"e"}"
%format bigunion (lim) (body) = "\bigunion_{" lim "}{" body "}"
%format pow a (b) = a "^{" b "}"

Languages fulfill this combined interface as described above and again in the pseudocode in \figrefdef{set as language}{Sets as a ``language''}{
\begin{code}
instance Monoid s => Semiring (Set s) where
  zero  = emptyset
  one   = single mempty
  p  <+>  q = set (s | s `elem` p || s `elem` q)
  p  <.>  q = set (p <> q | u `elem` p && v `elem` q)

instance ClosedSemiring (Set s)  -- default |closure|

instance HasSingle (Set s) s where
  single s = set s
\end{code}
\vspace{-4ex}
%%  closure p = bigunion (n >= 0) (pow p n)
}.
All we needed from strings is that they form a monoid, generalize to sets of values from any monoid.\footnote{The |Monoid| class defines $\mappend$ and $\mempty$.}

\mynote{On second thought, postpone generalization from lists to monoids later.}

\sectionl{Matching}

Now consider how we can computably \emph{match} a string for membership in a language described in the vocabulary given in the previous section.
The set-based language definition does not lead directly to effective string matching, because the sets may be infinite.
We can get around this difficulty easily enough by a change of representation.
Sets are isomorphic to membership predicates.
\begin{code}
newtype Pred s = Pred (s -> Bool)

setPred :: Set a -> Pred a
setPred as = Pred (\ a -> a `elem` as)

predSet :: Pred a -> Set a
predSet (Pred f) = set (a | f a)
\end{code}
It's easy to show that |setPred . predSet == id| and |predSet . setPred == id|.
% See 2018-12-10 notes.

This isomorphism suggests a simple specification for effective matching, namely the requirement that |setPred| (or |predSet|) is a \emph{homomorphism} with respect to the vocabulary of \figref{classes}.
(This style of specification has proved useful for a range of problems \cite{Elliott-2009-tcm, Elliott-2018-ad-icfp}.)
\begin{theorem}[\provedIn{theorem:pred}]\thmLabel{pred}
Given the definitions in \figrefdef{pred}{Predicates as a language (specified by homomorphicity of |predSet|/|setPred|)}{
\begin{code}
instance Semiring (Pred [c]) where
  zero = Pred (const False)
  one = Pred null
  Pred f  <+>  Pred g = Pred (\ x -> f x || g x)
  Pred f  <.>  Pred g = Pred (\ x -> or [ f u && g v | (u,v) <- splits x ] )

instance ClosedSemiring (Pred [c])  -- default |closure|

instance Eq s => HasSingle (Pred s) s where
  single s = Pred (== s)

-- All ways of splitting a given list (inverting |(<>)|).
splits :: [a] -> [([a],[a])]
splits []       = [([],[])]
splits (a:as')  = ([],a:as') : [((a:l),r) | (l,r) <- splits as']
\end{code}
\vspace{-4ex}
}, |setPred| and |predSet| are homomorphisms with respect to each instantiated class.
\end{theorem}

\mynote{Try some examples, including |star| and even the classic non-regular language $a^n b^n$ or \href{https://en.wikipedia.org/wiki/Dyck_language}{the Dyck language}.}

\sectionl{List of successes}

Although the predicate-based language implementation in \secref{Matching} is effective, it is terribly inefficient, due to the backtracking search involved in the definitions of |(<.>)| and |splits| in \figref{pred}.
An alternative technique commonly used in monadic parsing involves matching a language against \emph{prefixes} of a given string, yielding a corresponding ``residual'' suffix for each successful match \cite{Wadler-85-successes, HuttonMeijer-98-parsing}.
If there is some way to match an \emph{entire} given string (i.e., if any matching residual is empty), then that string is in the language.
As with |Pred|, we can package this technique in a new data type with an interpretation function that relates it to an already understood language representation:
\begin{code}
newtype Resid c = Resid ([c] -> [[c]])

residPred :: Resid c -> Pred [c]
residPred (Resid f) = Pred (any null . f)
\end{code}
\begin{theorem}[\provedIn{theorem:resid}]\thmLabel{resid}
Given the definitions in \figrefdef{resid}{List-of-successes as a language (specified by homomorphicity of |residPred|)}{
\begin{code}
instance Semiring (Resid c) where
  zero = Resid (const [])
  one = Resid (\ s -> [s])
  Resid f  <+>  Resid g = Resid (\ s -> f s <> g s)
  Resid f  <.>  Resid g = Resid (\ s -> [s'' | s' <- f s, s'' <- g s'])

-- Equivalent definition in monadic style
instance Semiring (Resid c) where
  zero = Resid (fail "no match")
  one = Resid return
  Resid f  <+>  Resid g = Resid (liftA2 (<>) f g)
  Resid f  <.>  Resid g = Resid (f >=> g)

instance ClosedSemiring (Resid c)

instance Eq c => HasSingle (Resid c) [c] where
  single x = Resid (maybeToList . stripPrefix x)

-- From |Data.List|
stripPrefix :: Eq a => [a] -> [a] -> Maybe [a]
stripPrefix []      ys               = Just ys
stripPrefix (x:xs)  (y:ys) | x == y  = stripPrefix xs ys
stripPrefix _ _                      = Nothing
\end{code}
\vspace{-4ex}
}, |residPred| is a homomorphism with respect to each instantiated class.
\end{theorem}

\section{Regular expressions}

%format :<+> = "\mathbin{:\!\!+}"
%format :<.> = "\mathbin{:\!\!\conv}"

Regular expressions are widely used as a syntactic description of regular languages and can be represented as an algebraic data type:
\begin{code}
infixl 6  :<+>
infixl 7  :<.>

data RegExp c  =  Char c
               |  Zero
               |  One
               |  RegExp c  :<+>  RegExp c
               |  RegExp c  :<.>  RegExp c
               |  Closure (RegExp c)
  deriving Show
\end{code}
We can convert regular expressions  to \emph{any} closed semiring with singletons:
\begin{code}
regexp :: (ClosedSemiring a, HasSingle a [c]) => RegExp c -> a
regexp (Char c)      = single [c]
regexp Zero          = zero
regexp One           = one
regexp (u  :<+>  v)  = regexp u  <+>  regexp v
regexp (u  :<.>  v)  = regexp u  <.>  regexp v
regexp (Closure u)   = closure (regexp u)
\end{code}

\begin{theorem}[\provedIn{theorem:regexp}]\thmLabel{regexp}
Given the definitions in \figrefdef{regexp}{Regular expressions as a language (specified by homomorphicity of |regexp|)}{
\begin{code}
instance Eq c => Semiring (RegExp c) where
  zero  = Zero
  one   = One
  Zero <+> b = b
  a <+> Zero = a
  a :<.> c <+> b :<.> d | a == b = a <.> (c <+> d)
  a :<.> c <+> b :<.> d | c == d = (a <+> b) <.> c
  a <+> b = a :<+> b
  Zero <.> _ = Zero
  _ <.> Zero = Zero
  One <.> b = b
  a <.> One = a
  a <.> b = a :<.> b

instance ClosedSemiring (RegExp c) where
  closure Zero = one
  closure e    = Closure e

instance HasSingle (RegExp c) [c] where
  single s = foldr (\ c e -> Char c <.> e) one s
\end{code}
\vspace{-4ex}
}, |regexp| is a homomorphism with respect to each instantiated class.\notefoot{The |HasSingle| instance can use any |Foldable| in place of |[]|. 
One could also define balanced folding of sums and products via two monoid wrappers, probably a good idea.}
(Note that the semiring laws allow optimization.\footnote{For idempotent semirings, one could also optimize |closure One| to |one|, but later interpretations will need a different value.})

\end{theorem}


\sectionl{Derivatives of languages}

The language matching algorithms embodied in the |Pred| and |Resid| types (defined in \secreftwo{Matching}{List of successes}) both perform backtracking.
We can do much better.
A classic solution is to add token lookahead, as in LR, LL, and LALR parsers \needcite{}.
While such parser generators typically have relatively complex implementations and look a fixed number of tokens ahead, Janusz Brzozowski discovered a simple and efficient technique that looks arbitrarily far ahead and eliminates all backtracking.
He applied this technique only to regular languages and expressed it as a transformation that he termed ``derivatives of regular expressions'' \citep{Brzozowski64} \mynote{additional references}.
Much more recently \citet{Might2010YaccID} extended the technique from regular to \emph{context-free} languages as a transformation on context-free grammars.

%format deriv (c) = "\derivOp_{"c"}"
%format derivs (s) = "\derivsOp_{"s"}"

%% %format deriv (c) = "\deriv{"c"}"
%% %format derivs (s) = "\derivs{"s"}"

\begin{definition} \defLabel{derivs}
The \emph{derivative} $\derivs u p$ of a language $p$ with respect to a string $u$ is the set of $u$-suffixes of strings in $p$, i.e.,
$$ \derivs u p = \set{ v \mid u \mappend v \in p } $$
\end{definition}
\begin{lemma}\lemLabel{derivs-member}
For a string $s$ and language $p$,
$$ s \in p \iff \mempty \in \derivs s p .$$
Proof: immediate from \defRef{derivs}.
\end{lemma}
The practical value of \lemRef{derivs-member} is that |derivs s p| and |mempty|-containment can be computed easily and efficiently, thanks to \lemRefs{derivs-monoid}{hasEps} below.
\begin{lemma}[\provedIn{lemma:derivs-monoid}]\lemLabel{derivs-monoid}
|derivs| satisfies the following properties:
\begin{align*}
\derivs\mempty p &= p \\
\derivs{u \mappend v} p &= \derivs v (\derivs u p)
\end{align*}
Equivalently,
\begin{align*}
\derivs\mempty &= \id \\
\derivs{u \mappend v} &= \derivs v \circ \derivs u
\end{align*}
where $\id$ is the identity function.
In other words, |derivs| is a contravariant monoid homomorphism (targeting the monoid of endo-functions).
\end{lemma}

%% %format hasEps = "\hasEps"
%format hasEps = "\Varid{has_{\mempty}}"

\begin{definition}
The derivative $\deriv c p$ of a language $p$ with respect to a single value (``symbol'') $c$ is the derivative of $p$ with respect to the singleton sequence $[c]$, i.e. $$\deriv c p = \derivs{[c]} p.$$
Equivalently, $\deriv c p = \set{v \mid c:v \in p}$, where ``$c:v$'' is the result of prepending $c$ to the sequence $v$ (so that $c:v = [c] \mappend v$).
\end{definition}
\begin{lemma}[\citet{Brzozowski64}, Theorem 3.1]\lemLabel{deriv}
The $\derivOp$ operation has the following properties:\footnote{The fourth property can be written more directly as follows:
$$\deriv c (p \conv q) = (\ite{\mempty \in p}{\deriv c q}0) + \deriv c p \conv q $$
or even
$$\deriv c (p \conv q) = \iteB{\mempty \in p}{\deriv c q + \deriv c p \conv q}{\deriv c p \conv q}. $$}
\begin{align*}
\deriv c \zero        &= \zero \\
\deriv c \one         &= \zero \\
\deriv c (p + q)      &= \deriv c p + \deriv c q \\
\deriv c (p \conv q)  &= \delta\, p \conv \deriv c q + \deriv c p \conv q \\
\deriv c (\closure p) &= \deriv c (p \conv \closure p) \\
\end{align*}
where $\delta\,p$ is the set containing just the empty string $\mempty$ if $\mempty \in p$ and otherwise the empty set itself:\notefoot{Consider eliminating |delta| in favor of just using |hasEps|.}
$$ \delta\,p = \iteB{\one}{\zero}{\mempty \in p} . $$
\end{lemma}
All that remains now is to see how to test whether $\mempty \in p$ for a language $p$.
\begin{lemma}[\provedIn{lemma:hasEps}]\lemLabel{hasEps}
The following properties hold:\notefoot{Move this definition to after \defRef{derivs} and \lemRef{derivs-member}, which motivate |hasEps|.}
$$ \mempty \not\in \zero $$
$$ \mempty \in \one $$
$$ \mempty \in p + q \iff \mempty \in p \lor \mempty \in q $$
$$ \mempty \in p \conv q \iff \mempty \in p \land \mempty \in q $$
$$ \mempty \in \closure p $$
Recalling the nature of the closed-semiring of booleans from \figref{classes}, and defining $\hasEps p = \mempty \in p$, these properties amount to saying that $\hasEps$ is a closed-semiring homomorphism, i.e.,
\begin{align*}
\hasEps \zero        &= \zero \\
\hasEps \one         &= \one \\
\hasEps (p + q)      &= \hasEps p + \hasEps q \\
\hasEps (p \conv q)  &= \hasEps p \conv \hasEps q \\
\hasEps (\closure p) &= \closure{(\hasEps p)}\\
\end{align*}
\end{lemma}

%% \noindent
%% With this new vocabulary, \lemRefThree{derivs-member}{derivs-monoid}{deriv} can be interpreted much more broadly than languages as sets of sequences.

Let's now package up these new operations as another abstract interface for language representations to implement. \lemRefs{derivs-member}{hasEps} can then be interpreted much more broadly than languages as sets of sequences.
\begin{code}
class HasDecomp a c | a -> c where
  hasEps :: a -> Bool
  deriv :: c -> a -> a

instance Eq a => HasDecomp (Set a) a where
  hasEps p = [] `elem` p
  deriv c p = set (cs | c : cs `elem` p)

derivs :: HasDecomp a c => [c] -> a -> a
derivs s p = foldl (flip deriv) p s
\end{code}
As with |Semiring|, |ClosedSemiring|, and |HasSingle|, we can calculate instances of |HasDecomp|.
\begin{theorem}[\provedIn{theorem:HasDecomp}]\thmLabel{HasDecomp}
Given the definitions in \figrefdef{HasDecomp}{Decomposition of language representations (specified by homomorphicity)}{
\begin{code}
instance HasDecomp (Pred [c]) c where
  hasEps   (Pred f) = f []
  deriv c  (Pred f) = Pred (f . (c :))

instance HasDecomp (Resid s) s where
  hasEps   (Resid f) = any null (f [])
  deriv c  (Resid f) = Resid (f . (c :))
\end{code}
\begin{code}
instance Eq c => HasDecomp (RegExp c) c where
  hasEps (Char _)      = zero
  hasEps Zero          = zero
  hasEps One           = one
  hasEps (p  :<+>  q)  = hasEps p  <+>  hasEps q
  hasEps (p  :<.>  q)  = hasEps p  <.>  hasEps q
  hasEps (Closure p)   = closure (hasEps p)
  
  deriv c (Char c')     = if c == c' then one else zero
  deriv _ Zero          = zero
  deriv _ One           = zero
  deriv c (p  :<+>  q)  = deriv c p <+> deriv c q
  deriv c (p  :<.>  q)  = delta p <.> deriv c q  <+>  deriv c p <.> q
  deriv c (Closure p)   = deriv c (p <.> Closure p)
\end{code}
%%   deriv c (Char c')     = if c == c' then one else zero
%%   deriv c (Char c')  | c == c'    = one
%%                      | otherwise  = zero
\vspace{-4ex}
}, |predSet|, |residPred|, and |regexp| are |HasDecomp| homomorphisms.
\end{theorem}

Taken together, \lemRefs{derivs-member}{hasEps} give us an effective test for ``language'' membership, assuming that the language is expressed via |Semiring|, |ClosedSemiring|, and |HasSingle| and assuming that the language representation supports |HasDecomp|:
\begin{code}

accept :: HasDecomp a c => a -> [c] -> Bool
accept p s = hasEps (derivs s p)
\end{code}

\mynote{Show some examples.}

\sectionl{Tries}

\mynote{An independent path to derivatives.}

\sectionl{Generalizing}
\mynote{Outline:}
\begin{itemize}
\item
  Beyond booleans.
\item
  Convolution.
\item
  Beyond convolution: the free semimodule monad.
\item
  Variations: counting, probability distributions, temporal/spatial convolution.
\end{itemize}

%if False

Simplify $f * g$ where $f = \lis a\,h$:
\begin{align*}
f * g &= \liftATwo\,(\mappend)\,f\,g
  \\ &= \lambda z.\!\!\sum_{\substack{x,y \\ x \mappend y = z}} f\,x * g\,y
  \\ &= \lambda z.f\,[] * g\,z +\!\!\!
        \sum_{\substack{c,x',y \\ c \cons x' \mappend y = z}}\!\!\!\! f\,(c \cons x') * g\,y
  \\ &= \lambda z.\lis a\,h\,[] * g\,z +\!\!\!
        \sum_{\substack{c,x',y \\ c \cons x' \mappend y = z}}\!\!\!\! \lis a\,h\,(c \cons x') * g\,y
  \\ &= \lambda z. a * g\,z +
        \!\!\!\sum_{\substack{c,x',y \\ c \cons x' \mappend y = z}}\!\!\!\! h\,c\,x' * g\,y
  \\ &= (\lambda z. a * g\,z) +
        (\lambda z. \!\!\!\sum_{\substack{c,x',y \\ c \cons x' \mappend y = z}}\!\!\!\! h\,c\,x' * g\,y)
  \\ &= (\lambda z. a * g\,z) + \lis\,0\,(\lambda c. h\,c * g)
\end{align*}
Note that $\lambda z. a * g\,z$ is the scalar/vector product of $a$ and $g$, and $\lambda c. h\,c * g$ is mapping $(*\,g)$ over $h$.
I'll need to fill in some of the reasoning here.

%endif

\sectionl{What else?}

\begin{itemize}
\item Other applications:
\begin{itemize}
  \item Univariate and multivariate polynomials.
  \item Convolution: discrete and continuous, one- and multi-dimensional, dense and sparse.
  \item 2D parsing?
\end{itemize}
\end{itemize}


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

\appendix

\sectionl{Proofs}

\subsection{\thmRef{pred}}\proofLabel{theorem:pred}

\subsection{\thmRef{resid}}\proofLabel{theorem:resid}

\subsection{\thmRef{regexp}}\proofLabel{theorem:regexp}

\subsection{\lemRef{derivs-monoid}}\proofLabel{lemma:derivs-monoid}

\begin{code}
    derivs mempty p
==  set ( w | mempty <> w `elem` p )  -- definition of |derivs mempty|
==  set ( w | w `elem` p )            -- monoid law
==  p                                 -- set notation
\end{code}

\begin{code}
    derivs (u <> v) p
==  set ( w | (u <> v) <> w `elem` p )          -- definition of |derivs (u<>v)|
==  set ( w | u <> (v <> w) `elem` p )          -- monoid law
==  set ( w | v <> w `elem` derivs u p )        -- definition of |derivs u|
==  set ( w | w `elem` derivs v (derivs u p) )  -- definition of |derivs v|
==  derivs v (derivs u p)
\end{code}

\subsection{\lemRef{hasEps}}\proofLabel{lemma:hasEps}

\subsection{\thmRef{HasDecomp}}\proofLabel{theorem:HasDecomp}

\bibliography{bib}

\end{document}

