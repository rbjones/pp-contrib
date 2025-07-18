% $Id: nt001.tex $ﬁ
% bibref{rbjnt001} pdfname{nt001}
=TEX
\documentclass[11pt,titlepage]{article}
\usepackage{makeidx}
\newcommand{\ignore}[1]{}
\usepackage{graphicx}
\usepackage[unicode]{hyperref}
\pagestyle{plain}
\usepackage[paperwidth=5.25in,paperheight=8in,hmargin={0.75in,0.5in},vmargin={0.5in,0.5in},includehead,includefoot]{geometry}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{pdftitle={Focal Engineering}}
\hypersetup{colorlinks=true, urlcolor=red, citecolor=blue, filecolor=blue, linkcolor=blue}
%\usepackage{html}
\usepackage{paralist}
\usepackage{relsize}
\usepackage{verbatim}
\usepackage{enumerate}
\usepackage{longtable}
\usepackage{url}
\usepackage{amsmath, amssymb}
\usepackage[utf8]{inputenc} % Enables Unicode input
\newcommand{\hreg}[2]{\href{#1}{#2}\footnote{\url{#1}}}
\makeindex

\title{\LARGE\bf Focal Knowledge Engineering}
\author{Roger~Bishop~Jones}
\date{\small 2025:06:18}


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

This essay belongs to a period of tumult in my intellectual endeavours, and aims to contribute to a reformulation of my aspirations.
My inclinations straddle the relationship between Philosophy and Engineering, spreading across some of the other disciplines which might be thought to lie between them, such as logic, mathematics, and the sciences.

The project to which I aim to contribute goes top to bottom across that spectrum, though which way is up is debateable.
From my Engineering perspective, the philosophy is an aspect of the highest and earliest stages in the systems architevtural design, which fits it into the unworkable ``waterfall' model of systems development.

From a philosophical persepective, philosophy is concerned with foundations, most importantly the foundations of epistemology. but inextricably intertwined with philosophy of language, logic, and elements of metaphysics.
Everything else is superstructure.

What is it that we are engineering?
Two things.
A distributed shared repository of knowledge, with aspirations to support declarative knowledge of all kinds (subject to the particular conception of `declarative' knowledge which formed the aspiration).
And \emph{intelligence}, a pure conception of intelligence almost diametrically opposed to the model provided by LLMs.

\section{Deduction and Intelligence}

Once upon a time, the automation of formal deduction was seen by many as a way to realise machine intelligence.
A great deal of water has flown under the bridge, including a tug of war between that strategy (and related approaches that I here speak of as {\it focal}), and alternative strategies (which I will call {\it diffuse}) seeking to realise intelligence by methods thought to be  aligned to how the human brain, as a network of neurons, effects its own intelligence.

The state of intelligence engineering is now dominated by the application of diffuse techniques on a massive scale to the mastery of human language by training on the largest possibly bodies of language culled from a very wide range of  available digital sources.
We may say of these methods that they are at an opoosite pole to the {\it focal} methods which are the subject of this essay.

Nevetheless, General Artificial Intelligence is now thought to be just round the corner by an unusually large proportion of interested parties, and is being progressed by adapting diffuse LLM technology in a variety of ways.

Of the limitations being addressed two are of particular interest for the ideas pesented here.
The first is the question of truthfulness, not well served by a paradigm built on predicting what comes next on the basis of a very large training base which is not itself filtered either for truth, consistency or even meaningfulness.
The second is the ability to reason, especially rigorous extended deductive reasoning of the kind found in mathematics.

Intelligence is in its conception essentially focal, it is the idea that there is some magic kind of capability in humans which can be measured on a one dimensional spectrum and which determines how effective the brain is in a whole variety of different domains.
Performance in any particular domain is supposed to depend on knowledge of and experience of that domain and on the quantity of this special X factor, which influences how rapidly the required knowledge can be acquired and how effectively it can be deployed.

Independently of whether this is a good analysis of the capabilities of human brains, we can see from an independent analysis of certain domains, and also from general epistemological considerations, that focal techniques are appropriate in many situations, and we may conjecture that for narrow focal domains, addressing them using highly compute and memory intensive diffuse methods is likely to be relatively inefficient.

The next section will review a variety of diverse focal phenomena, where a relatively broad capability is advanced by focus on narrower domains which are crucial to it, and will say something about how they might be exploited in achieving high levels of capabilities which are more broadly instrumental and behave in manners similar to those attributed to intelligence in humans.

\section{Focal Phenomena and Their Role in This Proposal}

\begin{itemize}

\item Epistemological Focus

The most fundamental and broadest focal element, which is largely determinative of the character of the project is the focus on demonstrable declarative knowledge and its realisation through effectively formal methods.
Demonstrable declarative knowledge comes in the form of logical truths and is instrumental in the determination of truth in all wider domains which are sufficiently well defined for deductive reason to be applicable in them.
The broad pattern is that any such declarative knowledge can be factored into two parts of which the first is the construction of a completely abstract model in which the corresponding conjecture is demonstrable, and the establishment of a correspondence between the abstract model and the concrete phenomenon, which gives an alternate concrete interpretation of the otherwise purely logical model and demonstrable propositions.

While this focus on the purely logical delivers results to the entire domain of declarative language, it is neverthess a very broad domain one you have brought into it models of all the worldly phenomena addressed by declarative language, and there are many further and more radical foci which enable that broad domain to be facilitate by addressing narrower subject matters.

\item Syntactic Abstraction

Concrete syntax is a way for human beings to communicate using physical structures which share the structure an under;yinh abstract syntax.
Abstract syntax was invented as a way of circumscribing the scope of descriptions of the semantics of programming languages.
For the intelligence we seek, concrete representations are also irrelevant, and a focus on abstract structure facilitates the process.
By the choice of an elementary universal abstract syntax, we achieve an underlying logical representation which is suitable for material whose concrete syntax belongs to diverse languages, and language is thereby reduced to vocabulary and the meanings associated with the name in the vocabulary.

A logical context in this system is a constrained signature which will normally have been constructed by conservative extensions which assign meaning to new constants on their introduction.
Such logical contexts form a hierarchy in which languages or theories with the greater vocabulary appear higher in the tree and the root is the primitive logical system.

In that context, focal interest is progressively vested further down the tree with particular focus on the primitive logical system.
Progression at these lower levels potentially benefits all the theories higher in the structure.
Chosing the low-level structure of this heirarchy will be important in facilitating the bootstrapping of intelligence.


\item quasi-universal logical foundations

A variety of logical systems have been devised which are strong enough to be considered foundations for mathematics, in which the concepts of mathematics can be defined and the theorems of mathematics formally derived.
Both the semantics and the proof systems of these foundations are usually to a degree, open ended.
Thus, in particular for set theory, a standard interpretation of well-founded set theory is an initial segment of the cumulative heirarchy and the language of set theory is more expressive insofar as the lower bound for the cardinality of such an initial segment to be considered a model of the theory.
This is proof theoretically reflected by the adoption of appropriate large cardinal axioms.
We say that such a set theory is quasi-universal if for any other declarative language its abstract semantics can be repered in set theory subject to the adoption of a sufficiently large lower bound on the cardinality of the universe.

This is an \emph{R\&D project} rather than a straight development contract, so at least at first it is exploratory, and will begin prototyping before the philosophy and aims of the project are fully articulated, and the various levels of philosophising, strategising, specification, design, prototyping and development will advance in parallel.

In the first instance then, prototyping will begin with work on the formal specfication for the kernal for a new generation of proof technology for the Cambridge HOL logical foundation system (or a very close derivative of it).

This first stage in prototyping will be primarily exploting what it takes to bootstrap a reflexive kernel for the new technology, differing from the existing ProofPower system in the following ways.

\item Detached theory heirarchy.

The theory heirarchy will no longer by closely coupled with the logical kernel, and I will probably be talking of it as a \emph{knowledge base} or a \emph{context heirarchy}.
It is inteded to be a shared distributed resource, rather like and related to the URL/RUI naming systems, but containing only the definition of logical contexts.

This not important to the earliest prototyping since that will be concerned with formal specification of the abstract logic (not concete syntax) of the HOL language, its semantics and the relationship of entailment betwee sets of sentences in a context.

\item Reflection

It is inteded that the logical kernel will be a bootstrap for a system which is capableon reasoning about itself and formally proving the soundness of derived proof algorithms.
Two features in the kernel which will support the application of such reflective capabilites are HOL execution (i.e.the efficient execution of algorithms coded in HOL abstract syntax and the direct application by execution of proven derived rules in the proof of theorems.

\item An Augmented LCF paradigm

The provision for reflection has impacts on the logical kernel beyond those two particular innovations, and together these changes drive a coach and horses though the LCF paradigm while retaining its core commitment to the security of proof despite the possibility of user extension of proof automation.

The first change consequent on the reflection principles is that because efficient algorithms once proven sound can be used in proofs, it is no long essential to powerful derived rules included in the kernel.
They can be coded outside the kernel, proven to be sound, and then used as if they were in the kernel.
The kernel can therefore, in respect of the included proof rules, be simpler (though of course, the reflection principles are a major additional complexity.

A further consequence is that tactics can be replaced by derived rules.
It is unusual for tactics to be written which are not guaranteed to prove the subgoal to which they have offered a reduction, and the code in that tactic which eventually constructs the proof therefore constitutes a sound derived rule.
It therefore seems likely that tactics and the more elaborate machinery around them could be displaced by reasoning about the soundness of algorithms and the direct application of algorithms thus proven to be sound.

I should mention here that, though I speak of soundness here, this should in talking of derivations coincide with derivability by the primitive rules, for the incompleteness of HOL lies in the relationship between its semantics and the primitive basis (insofar as only `standard' models are admitted) and the deductive system is itself complete (i.e. derivability and entailment coincide).
However, it is theoremhood we are looking for so unless we would have to prove completeness if we wanted to substitute entailment.

\item abstract syntax only

This kernel is not to involve concrete syntax in any way, or concrete representation of the context heirarchy, so a specification of an api for access to the context heirarchy will be necessary at some point, though in the first instance a formal model of a single context will suffice for defining a system for demonstration of theorems in that context.

\item the bootstrapping problem

The central problem which the prototyping in intended to investigate is the problem of bootstrapping a system along the intended lines.
The primitive inference rules in the kernel could in principle be made much simpler than in the present kernel, but its not immediately obvious that the proofs necessary to get the more powerful rules in existing systems in use would not be made more difficult.
One way of resolving that problem might be to use the existing system to develop the necessary proofs in a form acceptable to the primitive kernel with not demonstratd derived rules.

\item polymorphic strong infinity and recursive datatypes

The existing specs (of the HOL logic and ProofPower kernel) have two features which may not wuit the above aspirations.
The first is that the rules are defined as relationships rather than as functions, and hence the ability to execute them doesn't yield a computation which delivers a theorem.



\end{itemize}

\section{More Compact Attempt}

Here is an array of focal techniques which will be deployed.

\begin{itemize}

\item Epistemological

Focus on logical truth indirectly supporting deduction in all declarative language.
This is a perfect information space suitable for alpha-zero type MCTS and neural heuristics.

\item Abstract Syntax and Representation

The core system should be independent of concrete syntax and storage structure and media, allowing support for arbitrary languages and diverse data storage to be wrapped around (possibly mediated by LLMs).

\item Heirarchic Knowledge Base

Admitting concrete interpretations, a theory or logical context store makes a heirachic knowledge base.
It is desirable to structure the neural nets accordingly with a separate neural net for each logical context (theory).
This structuring admits more focus, on the key elements required to bootstrapping intelligece appearing close to the roor of the heirarchy.

\item Logical Foundation System

The root of the heirarchy is what we call a logical foundation system, which is a logical system sufficiently strong that the rest of the heirarchy can be created by conservative extension alone.
There is a caveat here concerning infinity, in principle one might need stronger infinity principles (large cardinal axioms) but its easy to accomodate these and engineering applications will not be demanding in this respect.

The logical foundation system is highly focal, it reduces the logical system to a very small semantics and deductive apparatus.

\item The Logical Kernel

The logical foundation system lends itself to implementation following the LCF paradigm, which involves a small logical kernel implementing the deductive system as functions which are logically sound and therefore incapable of proving anything which is not true.
When this is implemented as a new type whose values can only be obtained through those computations corresponding to primitive rules, it then becomes possible to program additional proof automation in a way which is guaranteed to preserve logical soundness.

\item A Reflexive Paradigm

It is a general expectation that intelligent systems will ultimately be capable of redesigning themselves and that this will accelerate their progression to superintelligence.
This is the singularity.

A new paradigm in which the system is capable of reasoning about the soundness of programs implementing inference rules is sought, and the ultimate focus in these focal strategies is the focus on what it takes for such reasoning to be effectively and rapidly exploited.
A first stage in this is to rewrite the formal specifications of the deductive system so that they become an executable program implementing that deductive system, and then incorporate in that system the admissibility of any conclusion reached by executing a proven derived rule.

This transforms the LCF paradigm, in which a major element is the use of TACTICs in goal-oriented proof.
A tactic checks a goal which it might be able to simplify into one or more simpler goals, i.e. which it can prove from certain other theorems.
Its proof, if ultimately used in the proof of the goal, will be by reduction to the primitive inferences supplied by the logical kernel.
But if it could be proven that the method proposed was sound, then it could in principle be applied without being checked by the kernel.
It is therefore possible to replace the use of tactics by the use of proven derived rules having the same effects but nopt required to provide detailed justification by reduction to the primitive rules.

\end{itemize}


\section{Forget the Focal and Try Again}

The project is to build a new generation of proof support for the Cambridge HOL logical system.
I'll describe it by comparison with the existing support systems, particularly ProofPower.

\subsection{The Role of the System}

Cambridge HOL, the logical system and the interactive proof tool, were developed for the verification of digital electronics, but were subsequently more widely applied.

ProofPower was developed in the first instance to support the application of formal methods to the development of secure information systems, in the context of UK government initiatives financing R\&D to that end and the determination by CESG that their preferred formal specification language was Z.
It was intended that ProofPower would support Z by embedding into HOL.
Additional investments were made to enable the application of ProofPower to safety critical systems involving the verification of programs in SPARK Ada.

With the advent of AI it seems likely that machine supported formal methods will be much more broadly applicable, and the target for the new generation which I am exploring here involves the use of this logical system as an abstract substrate for the representation of all declarative knowledge.
A general transition from databases (of various kinds) to the use of a distributed logic based knowledge base would enable a transition from {\it data processing} which produces results of uncertain significance, to {\it deduction} yielding clear declarative content, in the context of abstract models of the physical world.
This is would represent a paradign shift from a computational paradigm to a deductive paradigm which would gives artificial intelligence a much firmer grip on truth, and exploit focus in the intelligent exploitation of deductive methods.

This is swimming aginst the present tide, in which the dominant trend is explicitly the realisation of general intelligence by progressing current methods based around LLMs, to the representation of knowledge in neural nets, and includes making a merit of development using AI which is productive but unreliable.
These methods typically abjure focus, and involve applying heavyweight models rather than building special lightweight structures for deep thinking in narrow domains.
There is a subsidiary contemporary trend which flows from the successes of Google Deepmind's Alpha-zero technology and a variety of hybrid applications building on those methods.
These major on the adoption of neural nets not for the command of language, but for the establishment of good heuristics for Monte Carlo Tree Search in perfect information spaces which can be explored independently by the learning system without need to observe large amounts of exemplary data.
Though these methods are being explored sucessfuly by DeepMind and others, they are generally domain specific applications, and I am not aware of any success in applying such techniques more broadly.
This proposal applied the techniques to a medium in which any and all these perfect information spaces can be precisely defined, and therefore allows them to be realised in a general intelligence rather than to a specific narrow application.

The full nature and scope of such a deductive paradigm is beyond the scope of the present project, which will focus on more tangible purposes.

So I do envisage this as supporting a widely distributed knowledge base for declarative knowledge as a context for deductive intelligence.

\section{Kernel Re-Engineering}

While still ruminating about the structure of the whole proposal, I need to be doing something practical to generate more tangible progress than English prose.

For me the most interesting part of the project is possibly the most controversial and likely the most difficult to pull off.
This is the re-engineering of the logical Kernel to support ``reflection'', i.e. to prioritise the ability of the proof technology to understand, to incrementally advance, and perhaps ultimately re-conceive and redesign itself.

This I propose to progress in the first instance by rewriting the formal specifications of HOL (in HOL) (a solid version of which is provided by Rob Arthan in \cite{arthan1991formal,arthanspc001,arthanspc002,arthanspc003,arthanspc004,arthanspc005}).
The aims of this rewrite are as follows:

\begin{itemize}
\item Make it more ``constructive''.

The existing formal specification notes difficulties arising in a more ``constructive'' approach to presenting the specifications, and because of these difficulties defines inference rules, which are intended to be implemented as functions, as relations.
For this project, the formal specification must be the implementation, so that it is possible using the specification to reason about the system, to specify and verify derived rules if inference and subsequently execute those derived rules in proving theorems.
i.e. we will be using HOL as a programming language, and the kernel will include the means to execute those programs.
It may be that it will prove worthwhile to embedd a convenient programming language into HOL for this purpose, but in the first instance I will be looking to avoid the extra complexity that would introduce into the kernel by sticking to constructive use of bare HOL.

As well as rewriting the specifications of HOL, I will be aiming to restructure the theory heirarchy so that the features necessary or specification of and reasoning about HOL programs, and about the whole system, are prioritised.

\item Make it more abstract

There is not much in this, but the intention is that the logical kernel will have nothing to do with concrete syntax or the way in which the logical contexts in which it operates are stored in physical media.
This is because the abstract syntax of HOL is advocated as a substrate for any declarative language, most of which one may expect to be analogous to shallow embeddings of languages more congenial for users, or less systematically related via LLMs or other AI layers (which are beyond our present scope).

\item Basic Theory Reorganisation

In the structuring of the new kernel the ability to work with inductive structures is prioritised and general mechanisms for this will be introduced rather than, for example, using strings to represent types and terms.
Since this is prerequisite to even beginning formal specification of the HOL language, it is our first task, and I intende to begin by defining well-founded relations, proving appropriate recursion theorems, proving that all types have initial strict well-orderings, introducing polymorphic strong infinity axiom(s?), and providing the theory necessary for the construction recursive data-types (whose first applications will be to HOL types and terms).

\item

\end{itemize}
\appendix

\section{Project Synthesis and Roadmap}
\subsection*{Author: Claude Sonnet 4}

This appendix provides a comprehensive synthesis of the project based on our discussion, organized into clear sections covering the vision, technical architecture, development roadmap, key innovations, and target applications. It credits me as the author and should be inserted before the bibliography section in your document.

\subsection{Project Overview}

This project aims to develop a new generation of proof support for the Cambridge HOL (CHOL) logical system, representing a fundamental shift from computational to deductive paradigms in artificial intelligence. The core innovation is the creation of a self-improving reasoning system that can formally verify its own development process while serving as a universal substrate for declarative knowledge representation.

\subsection{Core Vision}

\subsubsection{CHOL as Quasi-Universal Foundation}
The Cambridge HOL logical system already provides a completely general, quasi-universal representation for abstract models of any subject matter. The core deductive system (the relationship ``A is derivable from C'' where A is a Boolean term and C is a set of such terms) remains unchanged. Extensions are normally conservative, with optional stronger infinity axioms as needed.
sections
\subsubsection{Perfect Information Spaces}
Abstract models are constructed by introducing new constants with constraints (conservative extensions), creating perfect information spaces suitable for intelligent reasoning. All such logical contexts are perfect information spaces, and all definite perfect information spaces can be constructed as logical contexts in CHOL. This represents a complete generalization of the Alpha-Zero method beyond specific games to cover all domains through a hierarchy of logical contexts.

\subsubsection{Self-Improving Intelligence Engineering}
Intelligence progresses fastest when intelligent systems participate in their own continued development. Engineering competence is crucial, with software engineering as the first critical capability. The system is completely general for declarative knowledge and reasoning, but design and build capability is the initial focus. Software development will be the first application domain, with all development formally verified within the system itself.

\subsection{Technical Architecture}

\subsubsection{Reflexive Logical Kernel}
The logical kernel breaks from LCF tradition by allowing proven derived rules of inference to be directly applied, rather than requiring translation into primitive steps. This enables tactics to be replaced by verified derived rules, but demands early progression of CHOL's metatheory. The reengineering of the logical kernel to support verification and application of derived rules is identified as a core technical challenge.

\subsubsection{Abstract Syntax and Distributed Knowledge Base}
The system operates exclusively on abstract syntax, independent of concrete syntax or storage structures. The theory hierarchy becomes a detached, shared distributed resource (knowledge base) accessible via defined APIs and protocols. This enables support for arbitrary languages and diverse data storage to be wrapped around the core system.

\subsubsection{AI Integration}
Large Language Models (LLMs) will use defined interfaces to access the system as a source of definitive truth. Abstract models will be exclusively created and exploited by LLMs or subsequent AI generations, solving problems raised by humans in natural language. The system will support AI-augmented dialogue for requirements refinement and solution construction/verification.

\subsection{Development Roadmap}

\subsubsection{Phase 1: Core Kernel Development}
\begin{itemize}
\item Formal specification of the abstract logic of HOL language
\item Implementation of reflexive kernel with reflection capabilities
\item Development of simplified primitive rules with reflection support
\item Metatheory development for CHOL
\item Bootstrapping investigation using existing ProofPower system
\end{itemize}

\subsubsection{Phase 2: Knowledge Base Infrastructure}
\begin{itemize}
\item Definition of APIs and protocols for knowledge base access
\item Implementation of detached theory hierarchy
\item Development of distributed resource management
\item Integration with external storage systems
\end{itemize}

\subsubsection{Phase 3: AI Integration and Applications}
\begin{itemize}
\item LLM interface development
\item Natural language processing capabilities
\item Engineering design and build applications
\item Formally verified design methods
\item AI-augmented dialogue systems
\end{itemize}

\subsubsection{Phase 4: Advanced Capabilities}
\begin{itemize}
\item Neural net heuristics in MCTS proof search
\item External resource integration (SAT/SMT solvers)
\item Advanced proof automation
\item Broader application domains
\end{itemize}

\subsection{Key Innovations}

\begin{enumerate}
\item \textbf{Universal Perfect Information Spaces}: Generalization of Alpha-Zero methods to all declarative domains through logical context hierarchy.

\item \textbf{Self-Verifying Development}: Displacement of build-and-test paradigm with formally verified construction.

\item \textbf{Reflexive Reasoning}: System capable of reasoning about and improving its own reasoning capabilities.

\item \textbf{Abstract Substrate}: Universal representation layer independent of concrete syntax or storage.

\item \textbf{AI-Augmented Deduction}: Integration of LLMs with definitive truth sources for enhanced reasoning.
\end{enumerate}

\subsection{Target Applications}

The primary application domain is engineering design and build, where the system will support:
\begin{itemize}
\item Requirements refinement through AI-augmented dialogue
\item Formally verified design methods
\item Automated solution construction and verification
\item Integration of human expertise with machine reasoning
\end{itemize}

This represents a paradigm shift from computational to deductive approaches, providing artificial intelligence with a much firmer grip on truth while enabling unprecedented levels of formal verification and self-improvement.

%\listoffigures

\pagebreak

\phantomsection
\addcontentsline{toc}{section}{Bibliography}
\bibliographystyle{rbjfmu}
\bibliography{rbj2}

%\addcontentsline{toc}{section}{Index}\label{index}
%{\twocolumn[]
%{\small\printindex}}

%\vfill

\tiny{
Started 2025/05/27
}%tiny

\end{document}

