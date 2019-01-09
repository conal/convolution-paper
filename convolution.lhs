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

sum, product :: (Foldable f, Semiring a) => f a -> a
sum      = foldr (<+>)  zero
product  = foldr (<.>)  one

class Semiring a => ClosedSemiring a where
  closure :: a -> a
  closure p = q where q = one <+> p <.> q  -- default

class HasSingle a x where
  single :: x -> a

instance Semiring Bool where
  zero    = False
  one     = True
  (<+>)   = (||)
  (<.>)   = (&&)

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

%format Pow = "\Pow"
%format emptyset = "\emptyset"
%format single (s) = "\single{"s"}"
%format set (e) = "\set{"e"}"
%format bigunion (lim) (body) = "\bigunion_{" lim "}{" body "}"
%format pow a (b) = a "^{" b "}"
%format `union` = "\cup"

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

Languages as sets fulfill this combined interface as described above and again in the pseudocode in \figrefdef{set}{Abstract sets as a ``language''}{
\begin{code}
instance Monoid s => Semiring (Pow s) where
  zero  = emptyset
  one   = single mempty
  p  <+>  q  = set (s | s `setElem` p || s `setElem` q) = p `setUnion` q
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
  p <+> q = p ++ q
  p <.> q = [u <> v | u <- p, v <- q]

instance Monoid a => ClosedSemiring [a] -- default

instance HasSingle [a] a where single a = [a]
\end{code}
\vspace{-4ex}
}.
Lists relate to sets as follows:
\begin{code}
listElems :: [a] -> Pow a
listElems []      = set ()
listElems (a:as)  = set a `union` listElems as
\end{code}
The instance definitions in \figreftwo{set}{list} bear a family resemblance to each other, which we can readily make precise:
\begin{theorem}[\provedIn{theorem:list}]\thmLabel{list}
Given the definitions in \figref{list}, |listElems| is a semiring (and close semiring) homomorphism.
\end{theorem}
%% Further, one can take this homomorphism property as an algebraic \emph{specifications} and \emph{calculate} the instance definitions in \figref{list}, explaining the resemblances.

\sectionl{Matching}

Now consider how we can computably \emph{match} a string for membership in a language described in the vocabulary given in the previous section.
The set-based language definition does not lead directly to effective string matching, because the sets may be infinite.
The list and finite set types do have computable membership testing so we could use them instead.
Another option is to use membership predicates directly, which are isomorphic to sets:
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
We can require that |predSet| (and thus |setPred|) is semiring homomorphism and solve the required homomorphism equations to yield a |Semiring| instance, as shown in \figrefdef{Pred}{Membership predicate as semiring (language representation)}{
\begin{code}
instance (Monoid a, Eq a) => Semiring (a -> Bool) where
  zero = \ w -> False
  one = \ w -> w == mempty
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
\begin{theorem}[\provedIn{theorem:Pred}]\thmLabel{Pred}
Given the definitions in \figref{Pred}, |setPred| and |predSet| are semiring homomorphisms (and together form a semiring \emph{isomorphism}).\notefoot{Even a ``\emph{closed} semiring homomorphism''. Probably say so.}
\end{theorem}

\sectionl{Beyond Booleans}



% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

\appendix

\sectionl{Proofs}

\subsection{\thmRef{list}}\proofLabel{theorem:list}

\subsection{\thmRef{Pred}}\proofLabel{theorem:Pred}

\bibliography{bib}

\end{document}

