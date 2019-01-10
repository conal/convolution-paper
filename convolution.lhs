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
%format `setElem` = "\in"

%format Pow = "\Pow"
%format emptyset = "\emptyset"
%format single (s) = "\single{"s"}"
%format set (e) = "\set{"e"}"
%format bigunion (lim) (body) = "\bigunion_{" lim "}{" body "}"
%format pow a (b) = a "^{" b "}"
%format `union` = "\cup"
%format closure p = "\closure{"p"}"

\sectionl{Languages}

\mynote{Summarize/review languages as sets, including singleton, union, concatenation, and star/closure.}

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

class HasSingle a x where
  single :: x -> a
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
  p  <.>  q  = set (u <> v | u `setElem` p && v `setElem` q)

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
The list and finite set types do have computable membership testing so we could use them instead.
Another option is to use membership predicates \emph{as} language implementation, noting the set/predicate isomorphism:
\begin{code}
setPred :: Pow a -> (a -> Bool)
setPred as = \ a -> a `setElem` as

predSet :: (a -> Bool) -> Pow a
predSet f = set (a | f a)
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
instance (Monoid a, Eq a) => Semiring (a -> Bool) where
  zero = \ w -> False
  one = single mempty
  f  <+>  g = \ w -> f w || g w
  f  <.>  g = \ w -> bigOrQ (u,v BR u <> v == w) f u && g v

instance (Monoid a, Eq a) => ClosedSemiring (a -> Bool)  -- default |closure|

instance Eq a => HasSingle (a -> Bool) a where
  single w = \ w' -> w' == w
\end{code}
\vspace{-4ex}
}.
When the monoid |a| is a list, we can also express the product operation in a more clearly computable form via list \emph{splittings}:
\begin{code}
  f <.> g  = \ w -> or [ f u && g v | (u,v) <- splits w ]
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

As an example other than numbers and languages, booleans form a closed semiring:
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

\noindent
\nc\bigSumZ[2]{\hspace{-#2ex}\sum\limits_{\substack{#1}}\hspace{-#2ex}}
%format bigSum (lim) = "\bigSumZ{" lim "}{0}"
%format bigSumQ (lim) = "\bigSumZ{" lim "}{1.5}"
Re-examining the instances in \figref{pred}, we can see uses of |False|, |(||||)|, and |(&&)|, as well as an equality test (for |single w|), which yields |False| or |True|.
We can therefore easily generalize the codomain of ``predicates'' from booleans to \emph{any} semiring, as in \figrefdef{function}{Function-to-semiring as generalized language representation}{
\begin{code}
instance (Monoid a, Eq a, Semiring b) => Semiring (a -> b) where
  zero = \ w -> zero
  one = single mempty
  f  <+>  g = \ w -> f w <+> g w
  f  <.>  g = \ w -> bigSumQ (u,v BR u <> v == w) f u <.> g v

instance (Monoid a, Eq a) => ClosedSemiring (a -> b)

instance Eq a => HasSingle (a -> b) a where
  single w = \ w' -> boolVal (w' == w)

boolVal :: Semiring s => Bool -> s
boolVal False  = zero
boolVal True   = one
\end{code}
\vspace{-4ex}
}.
\begin{theorem}[\provedIn{theorem:function}]\thmLabel{function}
Given the definitions in \figref{function}, functions from |a| to |b| the laws of closed semirings hold whenever |a| is a monoid and |b| is a semiring.
\end{theorem}
\noindent
When the monoid |a| is a list, we can again express the product operation in a more clearly computable form:
\begin{code}
  f <.> g  = \ w -> sum [ f u <.> g v | (u,v) <- splits w ]
\end{code}

\sectionl{Tries}

%format :< = "\mathrel{\Varid{:\!\!\triangleleft}}"
%format `mat` = !
%format mat = (!)

Since a language is a set of strings, we have considered representations of such sets as lists and as predicates.
Another choice of language representation is the \emph{trie}, as introduced by Thue in 1912, according to Knuth \needcite{}.
As shown by Hinze \needcite{}, tries can be extended to represent not just sets but partial functions, as well as defined generically for partial functions from types other than strings.
Putting genericity aside\notefoot{Re-raise later?} and restricting our attention to functions of lists (``strings''), we can formulate a simple trie data type as follows:

> data Trie c s = s :< Map c (Trie c s)

where |Map| is an efficient representation of finite maps, i.e., partial functions over finite domains \needcite{}.
Although we can think of |Trie c s| as denoting partial functions from |[c]| to |s|, if we further require |s| to be semiring, we can treat missing entries as being implicitly zero, yielding a \emph{total} function:\notefoot{Describe finite maps and |findWithDefault|.}
\begin{code}
trieFun :: Ord c => Trie c s -> ([c] -> s)
trieFun (e  :<  _   ) []      = e
trieFun (_  :<  ts  ) (c:cs)  = trieFun (ts ! c) cs

(!) :: (Ord c, Semiring s) => Map c s -> c -> s
m ! c = findWithDefault zero c m
\end{code}
We really need that |Trie c s| is a semiring (and hence has |zero|), since the finite map contains tries.
As we'll see, however, |Trie c s| is a semiring whenever |s| is.
Since |trieFun| interprets a trie as a function (from a monoid to a semiring), let's also require that it be a semiring homomorphism as a specification for the trie semiring.

%format deriv (c) = "\derivOp_{"c"}"

For a trie |t = e :< ts|, how does the meaning (via |trieFun|) of the trie |t| relate to the meanings of the sub-tries in |ts|?
An answer comes from the notion of \emph{derivatives} of languages as used by \citet{Brzozowski64} for simple and efficient recognition of regular languages.
The \emph{derivative} |deriv c p| of a language |p| (as a set of strings) with respect to an initial symbol |c| is the set of |c|-suffixes of strings in |p|, i.e.,
\begin{code}
deriv :: c -> Pow [c] -> Pow [c]
deriv c p = set (u | c : u `setElem` p)
\end{code}
Recast and generalized to functions of lists,
\begin{code}
deriv :: c -> ([c] -> b) -> ([c] -> b)
deriv c p  = \ u -> p (c : u)
           = p . (c NOP :)
\end{code}
Now suppose that |p| is given by a trie:
\begin{code}
    deriv c (trieFun (e :< ts))
==  trieFun (e :< ts) . (c NOP :)
==  \ u -> trieFun (e :< ts) (c : u)
==  \ u -> trieFun (ts ! c) u
==  trieFun (ts ! c)
\end{code}
In other words, the meanings of the sub-tries of a trie |t| are the derivatives of the meaning of |t|.

Our goal is to deduce definitions of the semiring vocabulary for tries such that |trieFun| becomes a semiring homomorphism.
Understanding how differentiation relates to that vocabulary will move us closer to this goal.
\begin{theorem}[\provedIn{theorem:deriv}, generalizing a result of \citet{Brzozowski64}, Theorem 3.1]\thmLabel{deriv}
The |deriv| operation has the following properties:%
\out{
\footnote{The fourth property can be written more directly as follows:

> deriv c (p <.> q) = (if mempty `setElem` p then deriv c q else 0) <+> deriv c p <.> q

or even

> deriv c (p <.> q) = if mempty `setElem` p then deriv c q <+> deriv c p <.> q else deriv c p <.> q

}
}
%format .> = "\cdot"
\begin{code}
deriv c zero         = zero
deriv c one          = zero
deriv c (p  <+>  q)  = deriv c p <+> deriv c q
deriv c (p  <.>  q)  = p mempty .> deriv c q <+> deriv c p <.> q
deriv c (closure p)  = deriv c (p <.> closure p)
\end{code}
where |(.>)| scales the result of a function:\footnote{Equivalently, |deriv c (p  <.>  q) = delta p * deriv c q <+> deriv c p <.> q|, where |delta p = p mempty .> one|, generalizing a notion of \citet[Definition 3.2]{Brzozowski64}.}
\begin{code}
infixl 7 .>
(.>) :: Semiring s => s -> (a -> s) -> (a -> s)
s .> f  = \ a -> s * (f a)
        = (s NOP *) . f
\end{code}
\end{theorem}


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

\appendix

\sectionl{Proofs}

\subsection{\thmRef{list}}\proofLabel{theorem:list}

\subsection{\thmRef{pred}}\proofLabel{theorem:pred}

\subsection{\thmRef{function}}\proofLabel{theorem:function}

\subsection{\thmRef{deriv}}\proofLabel{theorem:deriv}

\bibliography{bib}

\end{document}

