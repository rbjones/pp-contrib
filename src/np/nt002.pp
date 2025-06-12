=IGN
nt002.pp
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\usepackage{A4}

%\def\ExpName{\mbox{{\sf exp}
%\def\Exp#1{\ExpName(#1)}

\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{More Miscellanea}
\makeindex
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\author{Roger Bishop Jones}
\date{\ }

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
The beginnings of HOL metatheory in HOL.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created: 2025/06/10

Last Change 2025/06/10

\href{http://www.rbjones.com/rbjpub/pp/doc/nt002.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/nt002.pdf}

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize

\end{centering}

\thispagestyle{empty}
\end{titlepage}

\newpage
\addtocounter{page}{1}
%\section{DOCUMENT CONTROL}
%\subsection{Contents list}
{\parskip=0pt\tableofcontents}
%\newpage
%\subsection{Document cross references}

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\newpage

\section{INTRODUCTION}



=SML
open_theory "misc3";
force_new_theory "⦏nt002⦎";
force_new_pc "⦏'nt002⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'nt002";
set_merge_pcs ["misc11", "'GSU", "'misc3","'nt002"];
=TEX

\section{HOL TYPES AND TERM}

We use the urelments in GSU as names of type and term variables and constants.
The method here is to define the constructors as operations over sets, and to take the smallest set which is closed under the constructions.

\subsection{Types}

ⓈHOLCONST
│ ⦏Mk_Tvar⦎ : 'a GSU  → 'a GSU
├───────────
│ ∀n⦁ MkTvar n = Nat⋎u 0 ↦⋎u n
■

ⓈHOLCONST
│ ⦏Mk_Tcon⦎ : 'a GSU → 'a GSU LIST → 'a GSU
├───────────
│ ∀n l⦁ MkTcon n l = Nat⋎u 1 ↦⋎u SeqCons⋎u n (SeqDisp⋎u l)
■

=GFT
=TEX

\ignore{
=IGN
set_flag("subgoal_package_quiet", true);


set_goal([], ⌜∀f s x⦁ x ∈⋎u s ⇒ f x ∈ FunImage⋎u f s⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜FunImage⋎u⌝] THEN REPEAT strip_tac);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val funimage⋎u_fc_lemma = save_pop_thm "funimage⋎u_fc_lemma";

set_merge_pcs ["misc3", "'nt002"];
=TEX
}%ignore


=SML
add_pc_thms "'nt002" [];
commit_pc "'nt002";

force_new_pc "⦏nt002⦎";
merge_pcs ["misc3", "'nt002"] "nt002";
commit_pc "nt002";

set_flag("subgoal_package_quiet", false);
=TEX




{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{misc3.th}
}  %\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
