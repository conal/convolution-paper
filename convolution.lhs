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
\nc\setop[1]{\mathbin{\hat{#1}}}
\nc\eps{\varepsilon}
\nc\closure[1]{#1^{\ast}}
\nc\mappend{\diamond}
% \nc\cat{\cdot}
\nc\cat{\,}
\nc\single\overline
\nc\union{\cup}
\nc\bigunion{\bigcup}
\nc\has[2]{\delta_{#1}\,#2}
\nc\del[1]{\has\eps{#1}}
\nc\lquot{\setminus}
\nc\consl[2]{\single{[#1]} \cat #2}
\nc\conslp[2]{\consl{#1}{(#2)}}

\begin{document}

\maketitle

%% \begin{abstract}
%% ...
%% \end{abstract}

\sectionl{Introduction}

\sectionl{Languages}

\mynote{Summarize/review languages as sets, including singleton, union, concatenation, and star/closure.}

A \emph{language} is a set of strings, where a string is a sequence of values of some given type (``symbols'' from an ``alphabet'').
Languages are commonly built up via a few simple operations:\notefoot{I may want to parametrize by a monoid instead of an alphabet.}
\begin{itemize}
\item The \emph{empty} language $\emptyset = \set{}$.
\item For a string $s$, the \emph{singleton} language $\single s = \set{s}$.
\item For two languages $P$ and $Q$, the \emph{union} $P \union Q = \set{s \mid s \in P \lor s \in Q}$.
\item For two languages $P$ and $Q$, the element-wise \emph{concatenation} $P \cat Q = \set{p \mappend q \mid p \in P \land q \in Q}$, where ``$\mappend$'' denotes string concatenation.
\item For a language $P$, the \emph{closure} $\closure P = \bigunion_{n \ge 0} P^n $, where $P^n$ is $P$ concatenated with itself $n$ times (and $P^0 = \single{\eps}$).
\end{itemize}
%if False
\out{Note that $\closure P$ can also be given a recursive specification: $\closure P = \eps \union P \cat \closure P$.{Syntactically, we'll take concatenation (``$\cat$'') to bind more tightly than union (``$\union$''), so the RHS of this definition is equivalent to $\eps \union (P \cat \closure P)$}
%endif
These operations suffice to describe all \emph{regular} languages.
The language specifications (language-denoting \emph{expressions} rather than languages themselves) finitely constructed from these operations are called \emph{regular expressions}.
%(If we allow \emph{recursive} definitions, we get \emph{context-free} languages.)

Some observations:
\begin{itemize}
\item Union is associative, with $\emptyset$ as its identity.\notefoot{Maybe state equations for this observations and the next two.}
\item Element-Wise concatenation is associative and commutative, with $\single \eps$ as its identity, where $\eps$ is the empty string.
\item Left- and right-concatenation distributes over union.
\item The empty language annihilates under concatenation, i.e., $P \cat \emptyset = \emptyset \cat Q = \emptyset$.
\item The $\closure P$ operation satisfies the equation $\closure P = \eps \union (P \cat \closure P)$.
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
\end{code}
\vspace{-4ex}
} shows Haskell classes for representations of languages (and later generalizations), combining the star semiring vocabulary with an operation for singletons.

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

instance ClosedSemiring (Set s) where
  closure p = q where q = one <+> p <.> q

instance HasSingle (Set s) s where
  single s = set s
\end{code}
\vspace{-4ex}
%%  closure p = bigunion (n >= 0) (pow p n)
}.
All we needed from strings is that they form a monoid, generalize to sets of values from any monoid.\footnote{The |Monoid| class defines $\mappend$ and $\eps$.}

\mynote{On second thought, postpone generalization from lists to monoids later.}

\sectionl{Recognition}

Now consider how we can computably \emph{recognize} whether a string belongs to a language described in the vocabulary given in the previous section.
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

This isomorphism suggests a simple specification for effective language recognition, namely the requirement that |setPred| (or |predSet|) is a \emph{homomorphism} with respect to the vocabulary defined in the previous section.
(This style of specification has proved useful for a range of problems \cite{Elliott-2009-tcm, Elliott-2018-ad-icfp}.)
\begin{theorem}[\provedIn{theorem:pred}]\thmLabel{cont}
Given the definitions in \figrefdef{pred}{Predicates as a semiring (specified by homomorphicity of |predSet|/|setPred|)}{
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

\workingHere

We will have use for some decomposition laws.
\begin{lemma} \lemLabel{sum of singletons}
A language is the sum of singleton languages:
$$p = \bigunion\limits_{s \in p} \single s.$$
\end{lemma}
\begin{lemma} \lemLabel{sum of deltas}
A language is the sum of singleton or empty languages:
$$p = \bigunion\limits_s \has s p ,$$
where
$$ \has s p =
     \begin{cases}
     \single s & \text{if $s \in p$}, \\
     0 & \text{otherwise.}
     \end{cases} $$
\end{lemma}
\mynote{So far we can accommodate any monoid.
Now focus on sequences.}
\begin{lemma}[\provedIn{lemma:empty or cons}]\notefoot{Split this lemma in two, where the first one refers to the set of strings in $p$ that start with a prefix $s$, and the second says that this set equals $s \cat (s \lquot p)$. Proofs are easy. I think we have an embedding-projection pair. Useful?} \lemLabel{empty or cons}
$$p = \del p \union \bigcup\limits_c \conslp{c}{[c] \lquot p},$$
where $s \lquot p$ is the \emph{left quotient} of the language $p$ by the string $s$:
$$s \lquot p = \set{t \mid s \mappend t \in p}.$$
\end{lemma}
\noindent
This lemma was stated and used by \citet[Theorem 4.4]{Brzozowski64}, who used the notation ``$D_s\,p$'' (``the derivative of $p$ with respect to $s$'') instead of ``$s \lquot p$''.\notefoot{I don't think $s \lquot p$ is a derivative, but I'm still unsure. The product/convolution rule somewhat resembles the Leibniz rule, but the two appear to be inconsistent.}

\sectionl{Generalizing}
\mynote{Outline:}
\begin{itemize}
\item
  Semirings.
\item
  Convolution.
\item
  Beyond convolution: the free semimodule monad.
\item
  Variations: counting, probability distributions, temporal/spatial convolution.
\end{itemize}


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

\appendix

\sectionl{Proofs}

\subsection{\thmRef{pred}}\proofLabel{theorem:pred}

\mynote{Fill in.}

\subsection{\lemRef{empty or cons}}\proofLabel{lemma:empty or cons}

The proof follows from the observations that (a) any string in $p$ is either $\eps$ or is $c:s$ for some symbol $c$ and string $s$, and (b) $s \cat (s \lquot p)$ contains exactly the strings of $p$ that begin with $s$:
\begin{align*}
 p &= \bigunion_s \has s p
\\ &= \del p \cup (\bigunion_{s \neq \eps} \has{s} p)
\\ &= \del p \cup (\bigunion_{c,s'} \has{c:s'} p)
\\ &= \del p \cup (\bigunion_{c,s'} \single{[c]} \cat \has {s'} {([c] \lquot p)})
\\ &= \del p \cup (\bigunion_c \bigunion_s \single{[c]} \cat \has {s'} {([c] \lquot p)})
\\ &= \del p \cup (\bigunion_c \single{[c]} \cat \bigunion_s \has {s'} {([c] \lquot p)})
\\ &= \del p \cup (\bigunion_c \single{[c]} \cat ([c] \lquot p))
\end{align*}


\bibliography{bib}

\end{document}

