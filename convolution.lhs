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

\begin{document}

\maketitle

%% \begin{abstract}
%% ...
%% \end{abstract}

\sectionl{Introduction}

\sectionl{Languages and parsing}

\nc\set[1]{\{\,#1\,\}}
\nc\Pow{\mathcal{P}}
\nc\setop[1]{\mathbin{\hat{#1}}}
\nc\eps{\varepsilon}
\nc\closure[1]{#1^{\ast}}
\nc\Ltau{L_\tau}
% \nc\mappend{\mathbin{+\!\!+}}
\nc\mappend{\diamond}
\nc\cat{\cdot}
\nc\union{\cup}
\nc\single\overline

\mynote{Summarize/review languages as sets, including singleton, union, concatenation, and star/closure.}

A \emph{language} is a set of strings, where a string is a sequence of values of some given type (``symbols'' from an ``alphabet'').
Languages are commonly built up via a few simple operations:
\begin{itemize}
\item The \emph{empty} language $\emptyset = \set{}$.
\item For a string $s$, the \emph{singleton} language $\single s = \set{s}$.
      In particular, $\single \eps = \set{\eps}$, where $\eps$ is the empty string.
\item For two languages $p$ and $q$, the \emph{union} $p \union q = \set{s \mid s \in p \lor s \in q}$.
\item For two languages $p$ and $q$, the \emph{concatenation} $p \cat q = \set{u \mappend v \mid u \in p \land v \in q}$, where ``$\mappend$'' denotes string concatenation.
\item For a language $p$, the \emph{closure} $\closure p = \bigcup_{n \ge 0} p^n $, where $p^n$ is $p$ concatenated with itself $n$ times (and $p^0 = \single{\eps}$).
\end{itemize}
Note that $\closure p$ can also be given a recursive specification: $\closure p = \eps \union (p \cat \closure p)$.
These operations suffice to describe all \emph{regular} languages.
The language specifications (language-denoting \emph{expressions} rather than languages themselves) constructed from these operations are called \emph{regular expressions}.
(If we allow \emph{recursive} definitions, we get \emph{context-free} languages.)
As a Haskell data type parametrized over a type |c| of symbols (characters):%
%format `Union` = "\mathbin{:\!\union}"
%format `Cat` = "\mathbin{:\!\!\cat}"
%format Closure = Star
\begin{code}
data RegExp c  =  Empty
               |  Single [c]
               |  RegExp c `Union`  RegExp c
               |  RegExp c `Cat`    RegExp c
               |  Closure (RegExp c)
\end{code}
Regular expressions have an unsurprising denotation as a language:
%format Set = "\mathcal P"
%format empty = "\emptyset"
%format single (s) = "\single{"s"}"
%format `union` = "\union"
%format `cat` = "\cat"
%format closure (u) = "\closure{"u"}"
%format regexp (e) = "\db{"e"}"
\begin{code}
regexp :: RegExp c -> Set [c]
regexp Empty          = empty
regexp (Single s)     = single s
regexp (p `Union` q)  = regexp p `union` regexp q
regexp (p `Cat` q)    = regexp p `cat` regexp q
regexp (Closure p)    = closure (regexp p)
\end{code}

\emph{Parsing} is the problem of deciding whether $s \in L$ for a string $s$ and a language (set of strings) $L$.\notefoot{Maybe ``matching'' instead of ``parsing''.}
The vocabulary above for describing regular languages allows infinite languages (thanks to $\closure p$ when $p$ is nonempty), so parsing cannot be implemented simply by comparing $s$ with each string in $L$.
Fortunately, there are efficient, well-explored techniques for parsing regular languages, given a regular expression.
One such technique is to generate a finite state machine.

%format parse1
A simpler and much less efficient parsing technique closely follows the shape of regular expressions, as shown in \figrefdef{regexp}{Semantic function for |RegExp|}{
\centering
\begin{code}
parse1 :: Eq c => RegExp c -> [c] -> Bool
parse1 Empty          s = False
parse1 (Single s')    s = s == s'
parse1 (p `Union` q)  s = parse1 p s || parse1 q s
parse1 (p `Cat` q)    s = or [ parse1 p u && parse1 q v | (u,v) <- splits s ]
parse1 (Closure p)    s = parse1 (Empty `Union` (p `Cat` Closure p)) s

-- All ways to split (\emph{un-append}) a given list.
splits :: [a] -> [([a],[a])]
splits []       = [([],[])]
splits (a:as')  = ([],a:as') : [ ((a:ls),rs) | (ls,rs) <- splits as' ]
\end{code}
\vspace{-4ex}
% splits (a:as')  = ([],a:as') : map (first (a:)) (splits as')
}.
The inefficiency of this technique comes from the blind, backtracking search performed for |p `Cat` q| via |splits|.
\begin{lemma}
|forall s u v. NOP (u,v) `elem` splits s <=> u ++ v == s|. (Proof: exercise.)
\end{lemma}
\begin{theorem}
|forall e s. NOP parse1 e s <=> s `elem` regexp e|. (Proof: exercise.)
\end{theorem}
\noindent

\mynote{Next, get from |regexp| or |parse1| to something close to Brzozowski's method, I think via memoization.}

Following \cite{Brzozowski64}, define
\nc\del[1]{\delta\,#1}
\nc\der[2]{\mathcal D_{#1}\,#2}
$$\del p =
 \begin{cases}
 \single \eps & \text{if $\eps \in p$} \\
 \emptyset & \text{otherwise}
 \end{cases}$$
and
$$\der c p = \set {s \mid c:s \in p}$$
Then \citep[Theorem 4.4]{Brzozowski64}
$$ p = \del p \union \bigcup_{c\,\in A} \single c \cdot \der c p $$
The proof follows from the observations that (a) any string in $p$ is either $\eps$ or is $c:s$ for some symbol $c$ and string $s$, and (b) $\single c \cdot \der c p$ contains exactly the strings of $p$ that begin with $c$.
First, generalize $\del p$ to test \emph{any} string for membership:
\newcommand\has[2]{\delta_{#1}\,#2}
$$
\has s p =
 \begin{cases}
 \single s & \text{if $s \in p$} \\
 \emptyset & \text{otherwise}
 \end{cases}
$$
Then, for all languages $p$ and strings $s$, $p = \bigcup\limits_s \has s p$.
Thus
\begin{align}
 p &= \bigcup_s \has s p
\\ &= \del p \cup (\bigcup_{s \neq \eps} \has{s} p)
\\ &= \del p \cup (\bigcup_{c,s'} \has{c:s'} p)
\\ &= \del p \cup (\bigcup_{c,s'} \single c \cdot \has {s'} {(\der c p)})
\\ &= \del p \cup (\bigcup_c \bigcup_s \single c \cdot \has {s'} {(\der c p)})
\\ &= \del p \cup (\bigcup_c \single c \cdot \bigcup_s \has {s'} {(\der c p)})
\\ &= \del p \cup (\bigcup_c \single c \cdot \der c p)
\end{align}

Again but with ``$\single{[c]}$'' instead of ``$\single c$'':
Thus
\begin{align}
 p &= \bigcup_s \has s p
\\ &= \del p \cup (\bigcup_{s \neq \eps} \has{s} p)
\\ &= \del p \cup (\bigcup_{c,s'} \has{c:s'} p)
\\ &= \del p \cup (\bigcup_{c,s'} \single{[c]} \cdot \has {s'} {(\der c p)})
\\ &= \del p \cup (\bigcup_c \bigcup_s \single{[c]} \cdot \has {s'} {(\der c p)})
\\ &= \del p \cup (\bigcup_c \single{[c]} \cdot \bigcup_s \has {s'} {(\der c p)})
\\ &= \del p \cup (\bigcup_c \single{[c]} \cdot \der c p)
\end{align}

Note: $\single{qwerty}$.

\sectionl{Stuff}

\mynote{Survey some representations for parsing, including a naive one as predicates (requiring nondeterministic splitting).
For regular languages specified in this vocabulary, the classic technique for efficient parsing is to generate a finite state machine.
Another technique is Brzozowski's ``derivatives of regular expressions'', extended much more recently to context-free languages.
Maybe revisit Brzozowski's technique; alternatively just mention, and compare in related work.}

\mynote{
Calculate a generalized variant from a simple specification.
Key is a known but not widely used monadic structure, namely that of \emph{free semimodules}.
Generalize from the \emph{set} monad.
}

\appendix

\sectionl{Proofs}

\bibliography{bib}

\end{document}

