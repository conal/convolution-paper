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
\nc\Ltau{L_\tau}
% \nc\mappend{\mathbin{+\!\!+}}
\nc\mappend{\diamond}
\nc\cat{\cdot}
% \nc\union{\cup}
\nc\single\overline
% \nc\single\widebar
\nc\union{+}
\nc\bigunion{\sum}
\nc\has[2]{\delta_{#1}\,#2}
% \nc\del[1]{\delta\,#1}
% \nc\del{\delta{}\,}
\nc\del{\has\eps}
\nc\lquot[2]{#1 \setminus #2}
\nc\lquoto[2]{\lquot{[#1]}{#2}}
\nc\consl[2]{\single{[#1]} \cat #2}
\nc\conslp[2]{\consl{#1}{(#2)}}

\begin{document}

\maketitle

%% \begin{abstract}
%% ...
%% \end{abstract}

\sectionl{Introduction}

\sectionl{Languages and parsing}

\mynote{Summarize/review languages as sets, including singleton, union, concatenation, and star/closure.}

A \emph{language} is a set of strings, where a string is a sequence of values of some given type (``symbols'' from an ``alphabet'').
Languages are commonly built up via a few simple operations:\notefoot{I may want to parametrize by a monoid instead of an alphabet.}
\begin{itemize}
\item The \emph{empty} language $0 = \set{}$.
\item For a string $s$, the \emph{singleton} language $\single s = \set{s}$.
      In particular, $1 = \single \eps = \set{\eps}$, where $\eps$ is the empty string.
\item For two languages $p$ and $q$, the \emph{union} $p \union q = \set{s \mid s \in p \lor s \in q}$.
\item For two languages $p$ and $q$, the \emph{concatenation} $p \cat q = \set{u \mappend v \mid u \in p \land v \in q}$, where ``$\mappend$'' denotes string concatenation.
\item For a language $p$, the \emph{closure} $\closure p = \bigunion\limits_{n \ge 0} p^n $, where $p^n$ is $p$ concatenated with itself $n$ times (and $p^0 = \single{\eps}$).
\end{itemize}
Note that $\closure p$ can also be given a recursive specification: $\closure p = \eps \union p \cat \closure p$.\footnote{Syntactically, we'll take concatenation (``$\cat$'') to bind more tightly than union (``$\union$''), so the RHS of this definition is equivalent to $\eps \union (p \cat \closure p)$}
These operations suffice to describe all \emph{regular} languages.
The language specifications (language-denoting \emph{expressions} rather than languages themselves) constructed from these operations are called \emph{regular expressions}.
(If we allow \emph{recursive} definitions, we get \emph{context-free} languages.)
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
\begin{lemma}[\provedIn{lemma:empty or cons}]\notefoot{Split this lemma in two, where the first one refers to the set of strings in $p$ that start with a prefix $s$, and the second says that this subset equals $s \cat (\lquot s p)$. Proofs are easy.} \lemLabel{empty or cons}
$$p = \del p \union \bigcup\limits_c \conslp{c}{\lquoto c p},$$
where $\lquot s p$ is the \emph{left quotient} of the language $p$ by the string $s$:
$$\lquot s p = \set{t \mid s \mappend t \in S}.$$
\end{lemma}
\noindent
This lemma was stated and used by \citet[Theorem 4.4]{Brzozowski64}, who used the notation ``$D_s\,p$'' (``the derivative of $p$ with respect to $s$'') instead of ``$\lquot s p$''.\notefoot{I don't think $\lquot s p$ is a derivative, but I'm still unsure. The product/convolution rule somewhat resembles the Leibniz rule, but the two appear to be inconsistent.}

\appendix

\sectionl{Proofs}

\subsection{\lemRef{empty or cons}}\proofLabel{lemma:empty or cons}

The proof follows from the observations that (a) any string in $p$ is either $\eps$ or is $c:s$ for some symbol $c$ and string $s$, and (b) $s \cat (\lquot s p)$ contains exactly the strings of $p$ that begin with $s$:
\begin{align*}
 p &= \bigunion_s \has s p
\\ &= \del p \cup (\bigunion_{s \neq \eps} \has{s} p)
\\ &= \del p \cup (\bigunion_{c,s'} \has{c:s'} p)
\\ &= \del p \cup (\bigunion_{c,s'} \single{[c]} \cat \has {s'} {(\lquoto c p)})
\\ &= \del p \cup (\bigunion_c \bigunion_s \single{[c]} \cat \has {s'} {(\lquoto c p)})
\\ &= \del p \cup (\bigunion_c \single{[c]} \cat \bigunion_s \has {s'} {(\lquoto c p)})
\\ &= \del p \cup (\bigunion_c \single{[c]} \cat (\lquoto c p))
\end{align*}


\bibliography{bib}

\end{document}

