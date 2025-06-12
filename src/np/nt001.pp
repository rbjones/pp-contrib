% $Id: np001.tex $ﬁ
% bibref{rbjnp001} pdfname{np001}
=TEX
\documentclass[10pt,titlepage]{article}
\usepackage{makeidx}
\newcommand{\ignore}[1]{}
\usepackage{graphicx}
\usepackage[unicode]{hyperref}
\pagestyle{plain}
\usepackage[paperwidth=5.25in,paperheight=8in,hmargin={0.75in,0.5in},vmargin={0.5in,0.5in},includehead,includefoot]{geometry}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{pdftitle={Advancing Deductive Automation}}
\hypersetup{colorlinks=true, urlcolor=red, citecolor=blue, filecolor=blue, linkcolor=blue}
%\usepackage{html}
\usepackage{paralist}
\usepackage{relsize}
\usepackage{verbatim}
\usepackage{enumerate}
\usepackage{longtable}
\usepackage{url}
\newcommand{\hreg}[2]{\href{#1}{#2}\footnote{\url{#1}}}
\makeindex

\title{\LARGE\bf Focal Engineering}
\author{Roger~Bishop~Jones}
\date{\small 2025:06:10}


\begin{document}

%\begin{abstract}
% Some thoughts about directions for deductive technology.
%\end{abstract}
                               
\begin{titlepage}
\maketitle

%\vfill

%\begin{centering}

%{\footnotesize
%copyright\ Roger~Bishop~Jones;
%}%footnotesize

%\end{centering}

\end{titlepage}

\ \

\ignore{
\begin{centering}
{}
\end{centering}
}%ignore

\setcounter{tocdepth}{2}
{\parskip-0pt\tableofcontents}

\           

\section{Introduction}

This document is a re-think about the connection between AI and the automation of formal deduction and its applications.

I have a long standing interest in AI, in the logical foundations of mathematics and the automation of deductive reason and its applications, spanning many decades.
During that time there have been periods in which the automation of deduction has seemed central to the achievement of AI, and those in which it has seemed largely ignored or at best a promising application of AI rather than the means to achieve it.

For the purposes of this discussion it will be useful to distinguish approaches to AI as emergent or focal.
Emergent approaches are those in which general, if at first relatively superficial,  capapbilities are sought and progressed vigorously with the expectation that deeoer intelligence will appear as an \emph{emergent} phenomenon.
Focal approaches are those which regard certain capabilities as enabling intelligence in all domains, and, effectively treating those special capabilities as the X-factor in intelligence focusses on advancing those particular capabilities which in due course will prove widely applicable.

This is of course a false dichotomy, but despite hybrid approaches, the considerable advances lately secured by Large Language Models, fall into the emergent rather than the focal camp.
This discussion concerns the opposite pole.

I begin with a fairly broad discussion of phenomeon which might be considered focal which have some relevance to the automation of deduction and the development of AI, and aim to transform that discussion into a focal strategy for engineering intelligence through deduction. 


\section{What is Intelligence}

WHen Turing wrote his most influential paper on Artificial Intelligence which articulated a criterion which became known as the Turing Test, deliberately and explicitly disavowed attempting to define intelligence, but rather, for the sake of discussion, offered instead of the very uncertain concept of intelligence a related but more definitely defined concept measured by his test.

I have a similar difficulty in speaking about intelligence, which I think of as a poorly defined concept which misprepresents the diversity of human intellectual capabilities and is incompatible with the evolutionary history of the human brain.

The thesis behing the notion of intelligence, and its measurability as a linealry ordered intelligence quotient, is that human mental capabilities have two components, knowledge and intelligence.
Intelligence for any individual is a fixed magic ingredient which affects how readily knowledge is acquired and the level of capability which is then derived from that knowledge.
Differential capabilities arise in part from differences in knowledge, and in part from differences of intelligence as to the comprehension and application of the knowledge.

This conception of intelligence leads us naturally to a focal approach to its realisation.
Gathering knowledge will enable more applications, but only in those areas covered by the knowledge, while advancing intelligence confers advantage in all domains and improves the pace of acquisition and comprehension of the knowledge necessary to any application domain.






=============


The start point for this exercise is ProofPower support for Cambridge HOL.
I won't go into the merit of that baseline, except to say that the logical system has the characteristics which seem to me most germinal for the roles which I envisage, and the implementation in ProofPower is one with which I am familiar, and which is well documented including a suite of formal specifications in HOL itself.

The three tiers correspond to different levels of disruption of the baseline technology.
They are all considered as contributing to the tier three aspiration.
The highest tier is things which are probably only realisable by starting again from scratch, which is to say, that they involve a complete reconception of the logical kernel.
The first tier includes ideas which can be delivered as non-disruption progressions to the existing system, through the usual combinations of new theories supported by additional superstructure.
The middle tier is for ideas which can be at least explored by various degrees of disruptive re-adaptation of the existing system, possibly retaining the logical kernal but exploring more or less radical recoceptions of the overlying systems.

None of this pretends to be exhaustive, I am concerned only with ideas which might contribute to the strategic objectives which I am pursuing, and the major bets I am placing on how to best progress them.

\begin{itemize}
  \item

    Ideas simple enough to implement in the existing ProofPower system, demanding no reconception of the aims and methods of the systems.
    
  \item

    Ideas Which would significantly advance the existing system possibly into new domains, mainly by adding new technology, particularly greater automation through the adoption of AI.

  \item

    Ideas which represent major reconceptions of the purpose, methods and scope of application of HOL and its support.
    
\end{itemize}

The following materials with sketch first the strategic objectives, and some of the ideas which I think might make realisaton of those objectives possible.
Then the main ideas will be sketched, and then some degree of fleshing out of the ideas.

\section{Some Philosophy, Some Strategy}

  Here we go right over to my more radical ideas for the next generation of proof technology, before returning to the components which might best contribute to their realisation.

 \subsection{Epistemology}

  Proof is the best way we know of conclusively establishing truth, and we might say, providing the most reliable ways to conclusively establish truths.
  The philosophical underpinning of this work comes in the epistemological thesis that a certain class of logical systems provide systematic underpinnings for the representation and qualified demonstration of all declarative truths.
  Among these the system which is known as Cambridge HOL, an elaboration of Alonzo Church's Simple Theory of Types devised by Mike Gordon for use in the formal verification of digital hardware, is particularly suitable by virtue of simplicity and power of the logical system and the universality of the underlying abstract syntax for the representation of propositions expressed in any finitary declarative language.

  The central contention is twofold, that all declarative propositions can be thought of as speaking of their subject matter in terms of some abstract model which has been shown to correspond to a suitable of degree of precision to some structure or phenomenon.
  From this perspective, all such declarative propositions about real world phenomena can be factorised into a demonstrable claim about the model, and an empirically supported correspondence between the model and the world.

Alongside this perspective on the scope of the underlying abstract representation which Cambridge HOL, I have an embryonic conception of a similarly scoped \emph{deductive paradigm} which I see taking over from and subsuming what I now conceive of as a purely computational paradigm.
In the latter, when computers run programs, the operate on data the signficance of which may only be understood by certain users of the system, and execute algorithms which are precisely specified by programs, yielding results the signficance of which is not formally specified.
In the deductive paradigm, the data are interpretable as propositons, and the computation as inference, and the results as concluded propositions.
The specifications of programs effectively provide derived inference rules which the program algorithm effects.
At present these ideas about the nature of this deductive paradigm are sketchy and it is part of this work to flesh them out.

\subsection{Proof as Verified Computation}

\subsection{Singularities, Fundamental Theories and Bootstraps}

It is an important part of the strategy here to combine clarity about broadly scoped capabilities with focus on particular applications of them which are important because of their potential role in advancing the more general capability.
From the science fiction literature we have the idea of "the coming singularity" where radical acceleration of pace is anticipated once we have AI capable of re-designing AI.
In a more modest way we see in mathematics a number of "fundamental theorems" (that of arithmetic the best known) which are particularly important because of the way in which they facilitate the development of the broader theory.
A third example, particularly associated with computing but more generally applicable, of "bootstrapping" on the analogy with trying to lift oneself up by pulling on one's bootstraps.

What all these say in different ways is that chosing which asoects of a desired general capability to focus on in the early stages may startlingly advantageous.
These ideas will be refined and exploited for strategic advantage.

\section{First Sketches}

\subsection{Simple Ideas}

I have only one idea to mention here as yet.
This serves two purposes.
Firstly it strengthens the system in terms of its semantic expressiveness and logical strength, as well as providing a simpler route to support for inductive datatypes.
It is to replace the axiom of infinity with a polymorphic strong infinity, which would give a type of inaccessibly greater cardinality than any monotype.





%\listoffigures

\pagebreak

\phantomsection
\addcontentsline{toc}{section}{Bibliography}
\bibliographystyle{rbjfmu}
\bibliography{rbj}

%\addcontentsline{toc}{section}{Index}\label{index}
%{\twocolumn[]
%{\small\printindex}}

%\vfill

\tiny{
Started 2025/05/27
}%tiny

\end{document}

% LocalWords:
