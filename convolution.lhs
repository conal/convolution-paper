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
\nc\append{\mathbin{+\!\!+}}
\nc\cat{\cdot}
\nc\union{\cup}

\mynote{Summarize/review languages as sets, including singleton, union, concatenation, and star/closure.}

A \emph{language} is a set of strings, where a string is a sequence of values of some given type (``symbols'' from an ``alphabet'').
Languages are commonly built up via a few simple operations:
\begin{itemize}
\item The \emph{empty} language $\emptyset = \set{}$.
\item For a string $s$, the \emph{singleton} language $\bar s = \set{s}$.
      In particular, $\bar \eps = \set{\eps}$, where $\eps$ is the empty string.
\item For two languages $U$ and $V$, the \emph{union} $U \union V = \set{s \mid s \in U \lor s \in V}$.
\item For two languages $U$ and $V$, the \emph{concatenation} $U \cat V = \set{u \append v \mid u \in U \land v \in V}$, where ``$\append$'' denotes string concatenation.
\item For a language $U$, the \emph{closure} $ \closure U = \bigcup_{n \ge 0} U^n $, where $U^n$ is $U$ concatenated with itself $n$ times (where $U^0 = \bar{\eps}$ by convention).
\end{itemize}
These operations suffice to describe all \emph{regular} languages.
The language specifications (language-denoting \emph{expressions} rather than languages themselves) constructed from these operations) are called \emph{regular expressions}.
(If we allow \emph{recursive} definitions, we get \emph{context-free} languages.)
As a Haskell data type parametrized over a type |c| of symbols (characters):%
%% %format `Union` = "\mathbin{:\!\union}"
%% %format `Cat` = "\mathbin{:\!\!\cat}"
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
%format single (s) = "\bar{"s"}"
%format `union` = "\union"
%format `cat` = "\cat"
%format closure (u) = "\closure{"u"}"
%format lang (e) = "\db{"e"}"
\begin{code}
lang Empty          = empty
lang (Single s)     = single s
lang (p `Union` q)  = lang p `union` lang q
lang (p `Cat` q)    = lang p `cat` lang q
lang (Closure p)    = closure (lang p)
\end{code}

\emph{Parsing} is the problem of deciding whether $s \in L$ for a string $s$ and a language (set of strings) $L$.\notefoot{Maybe ``matching'' instead of ``parsing''.}
The vocabulary above for describing regular languages allows infinite languages (thanks to $\closure U$ when $U$ is nonempty), so parsing cannot be implemented simply by comparing $s$ with each string in $L$.
Fortunately, there are efficient, well-explored techniques for parsing regular languages, given a regular expression.
One such technique is to generate a finite state machine.

%if True
A simpler and much less efficient parsing technique closely follows the shape of regular expressions, as shown in \figrefdef{lang}{Semantic function for |RegExp|}{
\centering
\begin{code}
parse :: Eq c => RegExp c -> [c] -> Bool
parse Empty          s = False
parse (Single s')    s = s == s'
parse (p `Union` q)  s = parse p s || parse q s
parse (p `Cat` q)    s = or [ parse p u && parse q v | (u,v) <- splits s ]
parse (Closure p)    s = parse (Empty `Union` (p `Cat` Closure p)) s

-- All ways to split (\emph{un-append}) a given list.
splits :: [a] -> [([a],[a])]
splits []       = [([],[])]
splits (a:as')  = ([],a:as') : [ ((a:ls),rs) | (ls,rs) <- splits as' ]
\end{code}
\vspace{-4ex}
% splits (a:as')  = ([],a:as') : map (first (a:)) (splits as')
}.
%endif
\begin{lemma}
|forall s u v.SP (u,v) `elem` splits s <=> u ++ v == s|. (Proof: exercise.)
\end{lemma}
\begin{theorem}
|forall e s.SP parse e s <=> s `elem` lang e|. (Proof: exercise.)
\end{theorem}

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

