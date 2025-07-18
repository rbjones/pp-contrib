=IGN
$Id: t056.doc$

Greek Letters
	Γ Δ Θ Λ Ξ Π Σ Υ Φ Ψ Ω
	α β γ δ ε ζ η θ ι κ λ μ ν ξ π ρ σ τ υ φ χ ψ ω
Logic: 	∧ ∨ ¬ ∀ ∃ ⦁ × ≤ ≠ ≥ ∈ ∉ ⇔ ⇒
Set symbols: 𝔹 ℂ 𝔽 ℕ ℙ ℚ ℝ 𝕊 𝕌 ℤ ⊆ ∅ ⊂ ∩ ⋂ ∪ ⋃ ⊖
Arrows: → ⤖ ⤕ ⇻ ↔ ⤀ ⇸ ↣ ↦ ↠ ⤔
Formal Text Brackets: ⌜ ⌝ ⓣ ⓜ ⓩ Ⓢ ■ ┌ └ ╒ ├
Padding symbols	│ ─ ═  Index Brackets ⦏ ⦎
Bracketing symbols: ⟨ ⟩ ⟦ ⟧ ⦇ ⦈
Subscription and Superscription: ⋎ ⋏ ↗ ↘ ↕ Underlining: ⨽ ⨼
Relation, Sequence and Bag Symbols:  ⩥ ▷ ⩤ ◁ ⁀ ↾ ↿ ⊕ ⊎ ⨾ ∘ ⨡
Miscellaneous: ⊢ ⦂ ≜ ⊥ ⊖

set_flag("pp_show_HOL_types", true);
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{rbj}

\usepackage{fontspec}
\setmainfont{ProofPowerSerif}

\ftlinepenalty=9999
\usepackage{A4}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}

\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{Ordinals and Enumerations}
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
This document provides support for a kind of ordinals in {\Product}, and for enumerations intended to support inductive definitions of recursive datatypes and foundational ontologies.
\end{abstract}

\vfill
\begin{centering}

{\footnotesize

Created 2019/12/03

Last Change 2019/12/03

\href{http://www.rbjones.com/rbjpub/pp/doc/t056.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t056.pdf}

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize

\end{centering}

\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
{\parskip=0pt\tableofcontents}

\newpage

\section{INTRODUCTION}

\ignore{
My broader aim, to which this document is intended to contribute, is foundational, and is in the spirit of H.B.Curry and his various collaboratorson Illative Combinatory Logic.
The approach I am exploring is to create a foundational ontology consisting of infinitary combinators with an equivalence relation determined by a reduction relation.
The principle ``illative'' combinator will be 𝝣, the equivalence relation.

In this document my aim is to approach the formal definition of this foundational ontology via the development of a theory of ordinals in the polymorphic higher order logic on which \Product{} is based, using an inductive definition over these ordinals.
The machinery developed for this purpose may possibly have broader applications for inductive data-types in {\Product}.
}%ignore

This document is derived from a previous document nominally on infinitary  induction \cite{rbjt051}, and I have not updated all the commentary to keep it in step with the formal text.
To tell the truth, because there was a long gap after starting this document before I recently resumed it, I'm not at all clear what innovations persuaded me that a new start was desirable.
One unimportant innovation was that I decided to express the strong infinity axiom using the terminology of the theory of ordinals (regular, strong limit), rather than going straight for it and possibly later proving those properties.
A second minor point I think was that I wanted to do as much as possible without using the strong infinity, since most HOL datatypes can be constructed on the basis of the weak countable infinity axiom which comes with HOL.
I'm not convinced of the merits of the split which is thereby created.

I find it hard to beleive that those two points sufficed to warrant this new approach, but anyway, here it is.
In the process, quite a lot of \cite{rbjt051} was discarded and has been redone from scratch in a very different way.
That includes all the work on the mechanisms for defining inductive datatypes, the new material formalising enumerations, and the set theory construction.

We begin here from the theory {\tt ordered\_sets}\cite{rbjt009} in which the theorem that over any set there exists an {\em initial strict well-ordering} is proven.
This enables us to define a polymorphic constant which denotes such an ordering over any type to which it is instantiated.
Each type is thereby made isomorphic to a initial segment of the ordinals, permitting a theory of ordinals to be developed without introducing any new types.
To get a rich theory of ordinals we would need a strong axiom of infinity, but the theory can be developed in the first instance using claims about the cardinality of the type as conditions or assumptions.

In \cite{rbjt058} I create the theory "ord" in which a new type constructor is defined with an axiom ensuring that the resulting type is strictly larger (in cardinality) than the parameter type, and is at least inaccessible.
This is placed in a separate theory and document so that any results here which may prove useful  in a strictly conservative development need not feel tainted by an unnecessary axiomatic extension.

In this document the development takes place in the following rough stages.

\begin{itemize}
\item first, some preliminary matters before the `ordinals' are introduced
\item second, the introduction of the polymorphic initial strict well-ordering in terms of which the development of a theory of ordinals is conducted, and the specialisation to that ordering of the results about well-orderings, well-foundedness, induction, recursion, and any other matters which we later find convenient in the development, and which are true of all non-empty initial strict well-orderings.
\item A progression of developments which depend upon assumptions about cardinality of the type to which our ordering is instantiated.
\end{itemize}

The development of the theory is focussed on those features which support two special applications.
The first of these is the definition of recursive datatypes.
In this area of application, in each particular application, a certain repertoire of methods for constructing data objects is to be supported, and one or more `datatypes' result from the indefinite (transfinite) iteration of these constructions.
Indefinite iteration is expected ultimately to exhaust all possible constructions, and the resulting types together constitute a fixed point or closure of a composite constructor functor which augments any starting point by those objects which can be constructed in one step from it.
This application area is addressed en-passant and to whatever extent it contributes to the second  application.

Similar methods may also be applied to the estabishment of foundational ontologies and of logical foundation systems.
In this application the constructors may be guaranteed to raise cardinality, and will therefore have no fixed point.
The resulting abstract onology will have the same cardinality as the ordinal type over which the inductive definition is performed, and the ontology will not be unconditionally closed under the constructions.
The simplest example is the construction of an ontology of pure well-founded set by adding at each stage all the elements of the powerset of the preceding ontology.
In this case the failure of closure in the resulting ontology is shown by the limitation of abstraction to separation, To secure a rich enough ontology, such as would be obtained in an axiomatic set theory via the axiom of replacement (or large cardinal axioms), an order type of large cardinality is required for our ordinals.
Though these application provide my primary motivation, any material particular to them which depends upon principles like replacement, will be the subject matter of a subsequent document (except insofar as it can be addressed conditionally).

In both of these applications, the ordinals enumerate the entities created, which are then represented by their place in the enumeration, the combined constructor (a single function with a disjoin union domain encapsulating all the individual constructors) is the inverse of this enumerating function defined by induction over the relevant type of ordinals.
The enumeration also supports inductive reasoning about these constructions and recursive definition of functions over them.

\section{PRELIMINARIES}

\ignore{
=SML
open_theory "rbjmisc";
force_new_theory "⦏ordinals⦎";
new_parent "U_orders";
new_parent "wf_relp";
new_parent "wf_recp";
new_parent "fun_rel_thms";
force_new_pc "⦏'ordinals⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'ordinals";
set_merge_pcs ["rbjmisc", "'ordinals"];
=TEX
}%ignore

\subsection{Cardinality of Sets}

This is a treatment of cardinality as a property of sets, not a theory of cardinal numbers.

The original motivation was not far removed from the present motivation, which is nice ways of expressing strong axioms of infinity.
Of course, the niceness which is most desirable is in the application of such axioms rather than in the aesthetics of their statement, and at the time when I started the material in this section I didn't have much clue about the application.

The document as a whole reflects my present feeling that the applications (at least those of particular interest to me, but possibly more generally) are best mediated by types of infinitary sequences and infinitary trees, and that other aspects of the set theories in which strong axioms are usually placed are less important in this context.
In particular, whereas I had at times felt that the development of the treatment of functions was important, I now feel that it is not, and that the notion of function already available in HOL is sufficient.
So the whole business of coding up functions as graphs of ordered pairs in set theory now seems unnecessary ({\it in this context}).

From here on in we have the original commentary (at least, {\it pro-tem}), which may not be entirely appropriate here.

The relations defined here with subscript `s' on their names are cardinality comparisons on sets.

=SML
declare_infix(300, "≤⋎s");
declare_infix(300, "<⋎s");
declare_infix(300, "~⋎s");
=TEX

ⓈHOLCONST
│ $⦏≤⋎s⦎ : 'a ℙ → 'b ℙ → BOOL
├──────
│ ∀ A B⦁ A ≤⋎s B ⇔ ∃f⦁
│	∀x y⦁ x ∈ A ∧ y ∈ A ⇒ f x ∈ B ∧ f y ∈ B ∧ (f x = f y ⇒ x = y)
■

=GFT
⦏≤⋎s_refl⦎ =		⊢ ∀ A⦁ A ≤⋎s A
⦏⊆_≤⋎s_thm⦎ =	⊢ ∀ A B⦁ A ⊆ B ⇒ A ≤⋎s B
⦏≤⋎s_trans⦎ =	⊢ ∀ A B C⦁ A ≤⋎s B ∧ B ≤⋎s C ⇒ A ≤⋎s C
=TEX

\ignore{
=SML
val ≤⋎s_def = get_spec ⌜$≤⋎s⌝;

set_goal([], ⌜∀A:'a ℙ⦁ A ≤⋎s A⌝);
a (rewrite_tac[≤⋎s_def] THEN strip_tac
	THEN ∃_tac ⌜λx:'a⦁x⌝
	THEN rewrite_tac[]);
val ≤⋎s_refl = save_pop_thm "≤⋎s_refl";

set_goal([], ⌜∀A B⦁ A ⊆ B ⇒ A ≤⋎s B⌝);
a (rewrite_tac[≤⋎s_def, sets_ext_clauses] THEN REPEAT strip_tac);
a (∃_tac ⌜λx:'a⦁x⌝ THEN asm_prove_tac[]);
val ⊆_≤⋎s_thm = save_pop_thm "⊆_≤⋎s_thm";

set_goal([], ⌜∀A B C⦁ A ≤⋎s B ∧ B ≤⋎s C ⇒ A ≤⋎s C⌝);
a (rewrite_tac[≤⋎s_def] THEN REPEAT strip_tac);
a (∃_tac ⌜λx⦁ f'(f x)⌝
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac
	THEN (REPEAT_N 3 (TRY (all_asm_ufc_tac[]))));
val ≤⋎s_trans = save_pop_thm "≤⋎s_trans";

add_pc_thms "'ordinals" [≤⋎s_refl];
set_merge_pcs ["basic_hol", "'ordinals"];
=TEX
}%ignore


ⓈHOLCONST
│ $⦏<⋎s⦎ : 'a ℙ → 'b ℙ → BOOL
├──────
│ ∀ A B⦁ A <⋎s B ⇔ A ≤⋎s B ∧ ¬ B ≤⋎s A
■

=GFT
⦏lt⋎s_irrefl⦎ =		⊢ ∀ A⦁ ¬ A <⋎s A
⦏lt⋎s_trans⦎ =	  	⊢ ∀ A B C⦁ A <⋎s B ∧ B <⋎s C ⇒ A <⋎s C
⦏lt⋎s_≤⋎s_trans⦎ =	   ⊢ ∀ A B C⦁ A <⋎s B ∧ B ≤⋎s C ⇒ A <⋎s C
⦏≤⋎s_lt⋎s_trans⦎ =	   ⊢ ∀ A B C⦁ A ≤⋎s B ∧ B <⋎s C ⇒ A <⋎s C
=TEX

\ignore{
=SML
val lt⋎s_def = get_spec ⌜$<⋎s⌝;

set_goal([], ⌜∀A:'a ℙ⦁ ¬ A <⋎s A⌝);
a (rewrite_tac[lt⋎s_def] THEN REPEAT strip_tac);
val lt⋎s_irrefl = save_pop_thm "lt⋎s_irrefl";

set_goal([], ⌜∀A B C⦁ A <⋎s B ∧ B <⋎s C ⇒ A <⋎s C⌝);
a (rewrite_tac[lt⋎s_def]
	THEN contr_tac
	THEN all_fc_tac [≤⋎s_trans]);
val lt⋎s_trans = save_pop_thm "lt⋎s_trans";

set_goal([], ⌜∀A B C⦁ A <⋎s B ∧ B ≤⋎s C ⇒ A <⋎s C⌝);
a (rewrite_tac[lt⋎s_def]
	THEN contr_tac
	THEN all_fc_tac [≤⋎s_trans]);
val lt⋎s_≤⋎s_trans = save_pop_thm "lt⋎s_≤⋎s_trans";

set_goal([], ⌜∀A B C⦁ A ≤⋎s B ∧ B <⋎s C ⇒ A <⋎s C⌝);
a (rewrite_tac[lt⋎s_def]
	THEN contr_tac
	THEN all_fc_tac [≤⋎s_trans]);
val ≤⋎s_lt⋎s_trans = save_pop_thm "≤⋎s_lt⋎s_trans";

=TEX
}%ignore

ⓈHOLCONST
│ $⦏~⋎s⦎ : 'a ℙ → 'b ℙ → BOOL
├──────
│ ∀ A B⦁
│	A ~⋎s B ⇔ ∃f g⦁
│		(∀x⦁ x ∈ A ⇒ f x ∈ B ∧ g (f x) = x)
│	∧	(∀y⦁ y ∈ B ⇒ g y ∈ A ∧ f (g y) = y)
■

=GFT
⦏card_equiv_lemma⦎ =	⊢ ∀ x y z⦁ x ~⋎s x
		   ∧ (x ~⋎s y ⇔ y ~⋎s x) ∧ (x ~⋎s y ∧ y ~⋎s z ⇒ x ~⋎s z)
=TEX

\ignore{
=SML
val eq⋎s_def = get_spec ⌜$~⋎s⌝;

set_flag("pp_show_HOL_types", false);
push_pc "hol";

set_goal([], ⌜∀x y z⦁ (x ~⋎s x)
		∧ (x ~⋎s y ⇔ y ~⋎s x)
		∧ (x ~⋎s y ∧ y ~⋎s z ⇒ x ~⋎s z)⌝);
a (rewrite_tac [get_spec ⌜$~⋎s⌝] THEN prove_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜λx:'b⦁ x⌝ THEN ∃_tac ⌜λx:'b⦁ x⌝ THEN prove_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜f' o f⌝ THEN ∃_tac ⌜g o g'⌝ THEN rewrite_tac[o_def]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (REPEAT (asm_fc_tac[]));
(* *** Goal "2.2" *** *)
a (asm_fc_tac[]);
a (spec_nth_asm_tac 5 ⌜f x'⌝);
a (asm_rewrite_tac[]);
(* *** Goal "2.3" *** *)
a (REPEAT_N 2 (asm_fc_tac[]));
(* *** Goal "2.4" *** *)
a (asm_fc_tac[]);
a (spec_nth_asm_tac 6 ⌜g' y'⌝);
a (asm_rewrite_tac[]);
val card_equiv_lemma = save_pop_thm "card_equiv_lemma";

=IGN
set_goal([], ⌜(∃ h⦁ h ∈ A ⤖ B) ⇒ A ~⋎s B⌝);
a (rewrite_tac(map get_spec [⌜$⤖⌝, ⌜$↔⌝, ⌜$~⋎s⌝]));
a (PC_T1 "sets_ext" rewrite_tac[]);
a (REPEAT strip_tac);
a (lemma_tac ⌜∃j⦁ (∀ x⦁ x ∈ h ⇒ j (Fst x) = Snd x))⌝);
⌝
⌝):

set_goal([], ⌜∀A B⦁ A ~⋎s B ⇔ A ≤⋎s B ∧ B ≤⋎s A⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac[eq⋎s_def, ≤⋎s_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜f⌝ THEN REPEAT strip_tac THEN asm_fc_tac[]);
a (GET_ASM_T ⌜g (f x) = x⌝ (once_rewrite_thm_tac o eq_sym_rule));
a (GET_ASM_T ⌜g (f y) = y⌝ (once_rewrite_thm_tac o eq_sym_rule));
a (GET_ASM_T ⌜f x = f y⌝ (rewrite_thm_tac));
(* *** Goal "2" *** *)
a (∃_tac ⌜g⌝ THEN REPEAT strip_tac THEN asm_fc_tac[]);
a (GET_ASM_T ⌜f (g x) = x⌝ (once_rewrite_thm_tac o eq_sym_rule));
a (GET_ASM_T ⌜f (g y) = y⌝ (once_rewrite_thm_tac o eq_sym_rule));
a (GET_ASM_T ⌜g x = g y⌝ (rewrite_thm_tac));
(* *** Goal "3" *** *)
a (asm_tac schroeder_bernstein_thm);


=IGN
a (lemma_tac ⌜∃f2⦁ ∀ x⦁ x ∈ A ⌝

set_goal([], ⌜⌝);
a (rewrite_tac 
pop_pc();
=TEX
}%ignore

\pagebreak

\section{GENERIC ORDINALS}

\subsection{The Ordering}

The existence of initial strict well-orderings has been established in \cite{rbjt009}, which allows us to define the following constant:

\ignore{
=SML
set_merge_pcs ["rbjmisc", "'ordinals"];

declare_infix(300, "<⋎o");
set_goal([], ⌜∃ $<⋎o:'a → 'a → BOOL⦁ UInitialStrictWellOrdering $<⋎o⌝);
a (strip_asm_tac u_initial_strict_well_ordering_thm);
a (∃_tac ⌜$<<⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏$<⋎o⦎: 'a → 'a → BOOL
├───────────
│ 	UInitialStrictWellOrdering $<⋎o
■

This is a polymorphic constant each instance of which is an initial strict well-ordering over the instance type, which may have any cardinality greater than zero.
The cardinality uniquely determines the {\it order-type} of the defined ordering over that type, which are in one to one correspondence with initial ordinals or cardinals.

=GFT
⦏lt⋎o_clauses⦎ =	⊢ (∀ x⦁ ¬ x <⋎o x)
       ∧ (((∀ x y⦁ ¬ x = y ⇒ ¬ (x <⋎o y ∧ y <⋎o x))
       ∧ (∀ x y z⦁ x <⋎o y ∧ y <⋎o z ⇒ x <⋎o z))
       ∧ (∀ x y⦁ ¬ x = y ⇒ x <⋎o y ∨ y <⋎o x)))
       ∧ (∀ A
       ⦁ ¬ A = {}
           ⇒ Minr (Universe, $<⋎o) A ∈ A
             ∧ (∀ y⦁ y ∈ A
                 ⇒ y = Minr (Universe, $<⋎o) A
		   ∨ Minr (Universe, $<⋎o) A <⋎o y))

⦏irrefl⋎o_thm⦎ =     ⊢ ∀ x⦁ ¬ x <⋎o x
⦏antisym⋎o_thm⦎ =  ⊢ ∀ x y⦁ ¬ x = y ⇒ ¬ (x <⋎o y ∧ y <⋎o x)
⦏trans⋎o_thm⦎ =      ⊢ ∀ x y z⦁ x <⋎o y ∧ y <⋎o z ⇒ x <⋎o z
⦏linear⋎o_thm⦎ =     ⊢ ∀ x y⦁ ¬ x = y ⇒ x <⋎o y ∨ y <⋎o x
⦏wf_lt⋎o_thmm⦎ =     ⊢ ∀ A⦁ ¬ A = {}
           ⇒ Minr (Universe, $<⋎o) A ∈ A
             ∧ (∀ y⦁ y ∈ A
                 ⇒ y = Minr (Universe, $<⋎o) A
		   ∨ Minr (Universe, $<⋎o) A <⋎o y)
=TEX
\ignore{
=SML
val lt⋎o_def = get_spec ⌜$<⋎o⌝;

val lt⋎o_clauses = save_thm ("lt⋎o_clauses", (* (rewrite_rule [
     ]*) (⇒_elim (∀_elim ⌜$<⋎o⌝ u_iswo_clauses2) lt⋎o_def));

val [irrefl⋎o_thm, antisym⋎o_thm, trans⋎o_thm, linear⋎o_thm, wf_lt⋎o_thm]
    = map save_thm
      	  (combine ["irrefl⋎o_thm", "antisym⋎o_thm", "trans⋎o_thm",
	  "linear⋎o_thm", "wf_lt⋎o_thm"]
    	  (strip_∧_rule lt⋎o_clauses));
=TEX
}%ignore

=GFT
⦏lt⋎o_trich⦎ =	⊢ ∀ β γ⦁ β <⋎o γ ∨ γ <⋎o β ∨ β = γ
⦏lt⋎o_trich_fc⦎ =	⊢ ∀ β γ⦁ ¬ β <⋎o γ ∧ ¬ γ <⋎o β ⇒ β = γ
⦏lt⋎o_trich_fc2⦎ =	⊢ ∀ β γ⦁ ¬ (¬ β <⋎o γ ∧ ¬ γ <⋎o β ∧ ¬ β = γ)
=TEX

\ignore{
=SML
set_goal([], ⌜∀β γ⦁ β <⋎o γ ∨ γ <⋎o β ∨ β = γ⌝);
a (contr_tac);
a (all_fc_tac [linear⋎o_thm]);
val lt⋎o_trich = save_pop_thm "lt⋎o_trich";

set_goal([], ⌜∀β γ⦁ ¬ β <⋎o γ ∧ ¬ γ <⋎o β ⇒ β = γ⌝);
a contr_tac;
a (strip_asm_tac (list_∀_elim [⌜β⌝, ⌜γ⌝] lt⋎o_trich));
val lt⋎o_trich_fc = save_pop_thm "lt⋎o_trich_fc";

set_goal([], ⌜∀β γ⦁ ¬ (¬ β <⋎o γ ∧ ¬ γ <⋎o β ∧ ¬ β = γ)⌝);
a contr_tac;
a (strip_asm_tac (list_∀_elim [⌜β⌝, ⌜γ⌝] lt⋎o_trich));
val lt⋎o_trich_fc2 = save_pop_thm "lt⋎o_trich_fc2";
=TEX
}%ignore

In axiomatic set theory the least ordinal of a set of ordinals is the distributed intersection over that set, for which a large cap symbol is often used.
Though these ordinals are not sets, a similar notation seems reasonable.

ⓈHOLCONST
│ ⦏⋂⋎o⦎: 'a ℙ → 'a
├───────────
│	∀s⦁ ⋂⋎o s = Minr(Universe, $<⋎o) s
■

=GFT
⦏⋂⋎o_thm⦎ = ⊢ ∀ A⦁ ¬ A = {} ⇒ ⋂⋎o A ∈ A ∧ (∀ y⦁ y ∈ A ⇒ y = ⋂⋎o A ∨ ⋂⋎o A <⋎o y)
⦏⋂⋎o_thm2⦎ = ⊢ ∀ so β⦁ β ∈ so ⇒ (∀ γ⦁ γ <⋎o ⋂⋎o so ⇔ (∀ η⦁ η ∈ so ⇒ γ <⋎o η)): 
=TEX

\ignore{
=SML
val ⋂⋎o_def = get_spec ⌜$⋂⋎o⌝;

val ⋂⋎o_thm = save_thm("⋂⋎o_thm", rewrite_rule
    	     [all_%forall%_intro(eq_sym_rule (all_%forall%_elim ⋂⋎o_def))] wf_lt⋎o_thm);

push_pc "hol1";
set_goal([], ⌜∀so β⦁ β ∈ so ⇒
	(∀γ⦁ γ <⋎o ⋂⋎o so ⇔ ∀η⦁ η ∈ so ⇒ γ <⋎o η)⌝);
a (REPEAT_N 4 strip_tac);
a (LEMMA_T ⌜¬ so = {}⌝ asm_tac THEN1 (rewrite_tac[] THEN contr_tac THEN asm_fc_tac[]));
a (ufc_tac [⋂⋎o_thm]);
a contr_tac; 
(* *** Goal "1" *** *)
a (spec_asm_tac ⌜∀ y⦁ y ∈ so ⇒ ¬ y = ⋂⋎o so ⇒ ⋂⋎o so <⋎o y⌝ ⌜η⌝);
a (var_elim_asm_tac ⌜η = ⋂⋎o so⌝);
a (all_ufc_tac [trans⋎o_thm]);
(* *** Goal "2" *** *)
a (spec_asm_tac ⌜∀ η⦁ η ∈ so ⇒ γ <⋎o η⌝ ⌜⋂⋎o so⌝);
val ⋂⋎o_thm2 = save_pop_thm "⋂⋎o_thm2";

pop_pc();
=TEX
}%ignore

=SML
declare_infix(300, "≤⋎o");
=TEX

ⓈHOLCONST
│ ⦏$≤⋎o⦎: 'a → 'a → BOOL
├───────────
│	∀ x y⦁ x ≤⋎o y ⇔ x <⋎o y ∨ x = y
■

=GFT
⦏≤⋎o_refl⦎ =		⊢ ∀ β⦁ β ≤⋎o β
⦏≤⋎o_lt⋎o⦎ =			⊢ ∀ β γ⦁ β ≤⋎o γ ⇔ ¬ γ <⋎o β
⦏¬⋎o_clauses⦎ =	⊢ ∀ β γ⦁ (¬ β <⋎o γ ⇔ γ ≤⋎o β) ∧ (¬ γ ≤⋎o β ⇔ β <⋎o γ)
=TEX

\ignore{
=SML
val ≤⋎o_def = get_spec ⌜$≤⋎o⌝;

=IGN
set_goal([], ⌜∀α β γ⦁ α ⊂ β ⇒ ⋂⋎o α <⋎o ⋂⋎o β⌝);
a (rewrite_tac[⋂⋎o_def]);

set_goal([], ⌜$<⋎o⌝);
set_goal([], ⌜$<⋎o⌝);
set_goal([], ⌜$<⋎o⌝);
=TEX
}%ignore

\ignore{
=SML
set_goal([], ⌜∀β⦁ β ≤⋎o β⌝);
a (rewrite_tac[≤⋎o_def]);
val ≤⋎o_refl = save_pop_thm "≤⋎o_refl";

set_goal([], ⌜∀β γ⦁ β ≤⋎o γ ⇔ ¬ γ <⋎o β⌝);
a (REPEAT ∀_tac THEN rewrite_tac [≤⋎o_def]);
a (contr_tac
	THEN strip_asm_tac (list_∀_elim [⌜β⌝, ⌜γ⌝] lt⋎o_trich)
	THEN all_fc_tac [trans⋎o_thm]
	THEN_TRY var_elim_nth_asm_tac 2
	THEN fc_tac[irrefl⋎o_thm]);
val ≤⋎o_lt⋎o = save_pop_thm "≤⋎o_lt⋎o";

set_goal([], ⌜∀β γ⦁ (¬ β <⋎o γ ⇔ γ ≤⋎o β)
	∧  (¬ γ ≤⋎o β ⇔ β <⋎o γ)⌝);
a (rewrite_tac[≤⋎o_def] THEN contr_tac
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY all_fc_tac [lt⋎o_trich_fc, trans⋎o_thm]
	THEN asm_prove_tac [irrefl⋎o_thm]);
val ¬⋎o_clauses = save_pop_thm "¬⋎o_clauses";
=TEX
}%ignore

=GFT
⦏⋂⋎o_mono_thm⦎ =	⊢ ∀ s t⦁ ¬ s = {} ∧ s ⊆ t ⇒ ⋂⋎o t ≤⋎o ⋂⋎o s
=TEX

\ignore{
=SML
set_goal([], ⌜∀ s t⦁ ¬ s = {} ∧ s ⊆ t ⇒ ⋂⋎o t ≤⋎o ⋂⋎o s⌝);
a (REPEAT strip_tac
  THEN fc_tac [⋂⋎o_thm]);
a (lemma_tac ⌜¬ t = {}⌝);
(* *** Goal "1" *** *)
a (DROP_ASM_T ⌜s ⊆ t⌝ ante_tac
  THEN rewrite_tac [sets_ext_clauses]);
a (DROP_ASM_T ⌜¬ s = {}⌝ ante_tac
  THEN rewrite_tac [sets_ext_clauses]);
a (contr_tac THEN all_asm_fc_tac[]);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [⋂⋎o_thm]);
a (DROP_ASM_T ⌜s ⊆ t⌝ ante_tac THEN rewrite_tac [sets_ext_clauses]
  THEN REPEAT strip_tac
  THEN all_asm_fc_tac[]);
a (rewrite_tac[≤⋎o_def]);
a (asm_fc_tac[] THEN asm_rewrite_tac[]);
val ⋂⋎o_mono_thm = save_pop_thm "⋂⋎o_mono_thm";
=TEX
}%ignore

\ignore{
=SML
add_rw_thms [irrefl⋎o_thm, ≤⋎o_refl] "'ordinals";
add_sc_thms [irrefl⋎o_thm, ≤⋎o_refl] "'ordinals";
add_st_thms [irrefl⋎o_thm] "'ordinals";
set_merge_pcs ["rbjmisc", "'ordinals"];
=TEX
}%ignore

=GFT
⦏lt⋎o_≤⋎o⦎ =	⊢ ∀ β γ η⦁ β <⋎o γ ⇒ β ≤⋎o γ
⦏≤⋎o_trans⦎ =	⊢ ∀ β γ η⦁ β ≤⋎o γ ∧ γ ≤⋎o η ⇒ β ≤⋎o η
⦏≤⋎o_lt⋎o_trans⦎ =	⊢ ∀ β γ η⦁ β ≤⋎o γ ∧ γ <⋎o η ⇒ β <⋎o η
⦏lt⋎o_≤⋎o_trans⦎ =	⊢ ∀ β γ η⦁ β <⋎o γ ∧ γ ≤⋎o η ⇒ β <⋎o η
⦏≤⋎o_cases⦎ =	⊢ ∀ β γ⦁ β ≤⋎o γ ∨ γ ≤⋎o β
=TEX

\ignore{
=SML
set_goal([], ⌜∀ β γ η⦁ β <⋎o γ ⇒ β ≤⋎o γ⌝);
a (rewrite_tac[≤⋎o_def] THEN REPEAT strip_tac);
val lt⋎o_≤⋎o = save_pop_thm "lt⋎o_≤⋎o";

set_goal([], ⌜∀β γ η⦁ β ≤⋎o γ ∧ γ ≤⋎o η ⇒ β ≤⋎o η⌝);
a (rewrite_tac[≤⋎o_def] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN all_fc_tac [trans⋎o_thm]
	THEN rewrite_tac[]);
val ≤⋎o_trans = save_pop_thm "≤⋎o_trans";

set_goal([], ⌜∀β γ η⦁ β ≤⋎o γ ∧ γ <⋎o η ⇒ β <⋎o η⌝);
a (rewrite_tac[≤⋎o_def] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN all_fc_tac [trans⋎o_thm]
	THEN rewrite_tac[]);
val ≤⋎o_lt⋎o_trans = save_pop_thm "≤⋎o_lt⋎o_trans";

set_goal([], ⌜∀β γ η⦁ β <⋎o γ ∧ γ ≤⋎o η ⇒ β <⋎o η⌝);
a (rewrite_tac[≤⋎o_def] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN all_fc_tac [trans⋎o_thm]
	THEN rewrite_tac[]);
val lt⋎o_≤⋎o_trans = save_pop_thm "lt⋎o_≤⋎o_trans";

set_goal([], ⌜∀β γ⦁ β ≤⋎o γ ∨ γ ≤⋎o β⌝);
a (rewrite_tac[≤⋎o_def] THEN contr_tac);
a (strip_asm_tac (all_∀_elim lt⋎o_trich));
val ≤⋎o_cases = save_pop_thm "≤⋎o_cases";

set_goal([], ⌜∀β γ⦁ β ≤⋎o γ ⇔ ∀δ⦁ δ <⋎o β ⇒ δ <⋎o γ⌝);
a (REPEAT_N 5 strip_tac THEN_TRY asm_rewrite_tac[] THEN contr_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [lt⋎o_≤⋎o_trans]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜γ⌝);
a (REPEAT_N 2 (POP_ASM_T ante_tac)
	THEN rewrite_tac[¬⋎o_clauses]
	THEN REPEAT strip_tac);
val ≤⋎o_ext_thm = save_pop_thm "≤⋎o_ext_thm";
=TEX
}%ignore

\subsection{Well-Foundedness and Induction}
=GFT
⦏lt⋎o_well_founded_thm⦎  ⊢ UWellFounded $<⋎o:
⦏lt⋎o_well_founded_thm2⦎  ⊢ WellFounded $<⋎o:
⦏lt⋎o_well_founded_thm3⦎  ⊢ well_founded $<⋎o:

⦏lt⋎o_induction_thm⦎ = ⊢ ∀ p⦁ (∀ x⦁ (∀ y⦁ y <⋎o x ⇒ p y) ⇒ p x) ⇒ (∀ x⦁ p x)
=TEX

We also introduce induction tacticals and tactics:
=GFT
⦏LT⋎O_INDUCTION_T⦎: (THM -> TACTIC) -> TERM -> TACTIC
⦏lt⋎o_induction_tac⦎: TERM -> TACTIC
=TEX

\ignore{
=SML
val lt⋎o_well_founded_thm = save_thm ("lt⋎o_well_founded_thm",
    ⇒_elim (∀_elim ⌜$<⋎o⌝ u_iswo_well_founded_thm) lt⋎o_def);

val lt⋎o_well_founded_thm2 = save_thm ("lt⋎o_well_founded_thm2",
    rewrite_rule [get_spec ⌜UWellFounded⌝] lt⋎o_well_founded_thm);

val lt⋎o_well_founded_thm3 = save_thm ("lt⋎o_well_founded_thm3",
    rewrite_rule [tac_proof(([], ⌜∀$<<⦁ UWellFounded $<< ⇔ well_founded $<<⌝), rewrite_tac [get_spec ⌜well_founded⌝, u_well_founded_induction_thm])] lt⋎o_well_founded_thm);

val lt⋎o_induction_thm = save_thm ("lt⋎o_induction_thm",
     ⇒_elim (∀_elim ⌜$<⋎o⌝ u_iswo_induction_thm) lt⋎o_def);

val LT⋎O_INDUCTION_T = GEN_INDUCTION_T lt⋎o_induction_thm;
val lt⋎o_induction_tac = gen_induction_tac lt⋎o_induction_thm;
=TEX
}%ignore

\subsection{Extension and Initiality}

Having a notation for the ``extension'' of an ordinal (i.e. set of smaller ordinals) will be handy.

ⓈHOLCONST
│ ⦏X⋎o⦎: 'a → 'a ℙ
├───────────
│	∀x⦁ X⋎o x  = {y | y <⋎o x}
■

We can then assert initiality (of any type ordered by $<⋎o$) as follows:

=GFT
⦏initial⋎o_thm⦎ = ⊢ ¬ (∃ f y⦁ OneOne f ∧ (∀ z⦁ f z <⋎o y))
⦏initial⋎o_thm2⦎ = ⊢ ¬ (∃x:'a⦁ {y:'a| T} ≤⋎s X⋎o x)
=TEX

\ignore{
=SML
val X⋎o_def = get_spec ⌜X⋎o⌝;

set_goal([], ⌜¬∃(f:'a → 'a)  y⦁ OneOne f ∧ (∀ z⦁ f z <⋎o y)⌝);
a (asm_tac lt⋎o_def);
a (fc_tac[u_initial_strict_well_ordering_def_thm]);
a contr_tac;
a (asm_fc_tac[]);
val initial⋎o_thm = save_pop_thm "initial⋎o_thm";;

set_goal([], ⌜¬ (∃x:'a⦁ {y:'a| T} ≤⋎s X⋎o x)⌝);
a (rewrite_tac[≤⋎s_def]);
a (REPEAT strip_tac);
a (strip_asm_tac initial⋎o_thm);
a (spec_nth_asm_tac 1 ⌜f:'a → 'a⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [one_one_def] THEN strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜x1⌝ THEN strip_tac THEN ∃_tac ⌜x2⌝ THEN contr_tac);
(* *** Goal "2" *** *)
a (∃_tac ⌜z⌝ THEN strip_tac THEN ∃_tac ⌜v⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [X⋎o_def] THEN contr_tac);
val initial⋎o_thm2 = save_pop_thm "initial⋎o_thm2";
=IGN
set_flag("pp_show_HOL_types", false);
=TEX
}%ignore

\subsection{Zero}

Zero ($0⋎o$) is the smallest ordinal.
Every type has one.

ⓈHOLCONST
│ ⦏0⋎o⦎: 'a
├───────────
│	0⋎o = ⋂⋎o {x|T}
■

=GFT
⦏zero⋎o_thm⦎ =	⊢ ∀ β⦁ 0⋎o ≤⋎o β
⦏lt⋎o_zero⋎o_thm⦎ =	⊢ ∀ β⦁ ¬ β <⋎o 0⋎o
⦏zero⋎o_thm2⦎ = ⊢ ∀ β⦁ 0⋎o <⋎o β ∨ 0⋎o = β
=TEX

\ignore{
=SML
val zero⋎o_def = get_spec ⌜0⋎o⌝;

set_goal([], ⌜∀ β⦁ 0⋎o ≤⋎o β⌝);
a (strip_tac THEN rewrite_tac[zero⋎o_def, ≤⋎o_def]);
a (LEMMA_T ⌜⋂⋎o {x:'a|T} ∈ {x:'a|T}⌝ asm_tac
  THEN1 PC_T1 "sets_ext" rewrite_tac[]);
a (LEMMA_T ⌜¬ {x:'a|T} = {}⌝  asm_tac
  THEN1 PC_T1 "sets_ext" rewrite_tac[]);
a (strip_asm_tac ⋂⋎o_thm);
push_pc "sets_ext";
a (spec_nth_asm_tac 1 ⌜{x:'a|T}⌝
  THEN spec_nth_asm_tac 1 ⌜β⌝
  THEN_TRY asm_rewrite_tac[]);
val zero⋎o_thm = save_pop_thm "zero⋎o_thm";
pop_pc();

val lt⋎o_zero⋎o_thm = save_thm ("lt⋎o_zero⋎o_thm",
	rewrite_rule [≤⋎o_lt⋎o] zero⋎o_thm);

val zero⋎o_thm2 = save_thm ("zero⋎o_thm2", rewrite_rule [≤⋎o_def] zero⋎o_thm);
=IGN
set_flag("pp_show_HOL_types", false);
undo 1;
=TEX
}%ignore

\subsection{Extensionality and Transitivity}

A useful principle for reasoning about the 'a ordinals is the following analogue of set theoretic extensionality:

=GFT
⦏ord_ext_thm⦎ =	⊢ ∀ β γ⦁ β = γ ⇔ (∀ δ⦁ δ <⋎o β ⇔ δ <⋎o γ)
=TEX

We will later make use of quasi extensional characterisations of operations over 'a ordinals, in which an 'a ordinal expression is characterised by a statement of the conditions under which 'a ordinals are less than the value of the expression.
This facilitates proofs about 'a ordinals in which the complexity is on the right of an inequality, or in which such can be obtained by the extensionality principle above.

This leaves an awkwardness where our goal has an expression on the left of an inequality which the following rule is intended to ameliorate.

=GFT
⦏≤⋎o_ext_thm⦎ =	⊢ ∀ β γ⦁ β ≤⋎o γ ⇔ (∀ δ⦁ δ <⋎o β ⇒ δ <⋎o γ)
=TEX

\ignore{
=SML
set_goal([], ⌜∀β γ⦁ β = γ ⇔ ∀δ⦁ δ <⋎o β ⇔ δ <⋎o γ⌝);
a (REPEAT_N 5 strip_tac THEN_TRY asm_rewrite_tac[] THEN contr_tac);
a (spec_nth_asm_tac 2 ⌜β⌝
	THEN spec_nth_asm_tac 4 ⌜γ⌝
	THEN all_fc_tac [lt⋎o_trich_fc2]);
val ord_ext_thm = save_pop_thm "ord_ext_thm";

(* skip to end of next section for ≤⋎o_ext_thm *)
=TEX
}%ignore

\subsection{Bounds and Suprema}

... and for the supremum of a set of 'a ordinals.

ⓈHOLCONST
│ ⦏Ub⋎o⦎: 'a ℙ → 'a ℙ
├───────────
│ ∀so⦁ Ub⋎o so = {β | ∀η⦁ η ∈ so ⇒ η ≤⋎o β}
■

=GFT
⦏Ub⋎o_thm⦎ =	⊢ ∀ so γ⦁ γ ∈ Ub⋎o so ⇔ (∀ η⦁ η ∈ so ⇒ η ≤⋎o γ)
⦏Ub⋎o_X⋎o_thm⦎ = ⊢ ∀ α⦁ α ∈ Ub⋎o (X⋎o α)
⦏Ub⋎o_X⋎o_thm2⦎ =  ⊢ ∀ α⦁ α ∈ Ub⋎o {β|β <⋎o α}
=TEX
\ignore{
=SML
val Ub⋎o_def = get_spec ⌜Ub⋎o⌝;

push_pc "hol1";

set_goal([], ⌜∀so γ⦁ γ ∈ Ub⋎o so ⇔ ∀η⦁ η ∈ so ⇒ η ≤⋎o γ⌝);
a (rewrite_tac[Ub⋎o_def]);
val Ub⋎o_thm = save_pop_thm "Ub⋎o_thm";

set_goal([], ⌜∀α⦁ α ∈ Ub⋎o (X⋎o α)⌝);
a (strip_tac THEN rewrite_tac[Ub⋎o_thm, X⋎o_def, ≤⋎o_def]
	THEN REPEAT strip_tac);
val Ub⋎o_X⋎o_thm = save_pop_thm "Ub⋎o_X⋎o_thm";

set_goal([], ⌜∀α⦁ α ∈ Ub⋎o {β | β <⋎o α}⌝);
a (strip_tac THEN rewrite_tac[Ub⋎o_thm, ≤⋎o_def]
	THEN REPEAT strip_tac);
val Ub⋎o_X⋎o_thm2 = save_pop_thm "Ub⋎o_X⋎o_thm2";

pop_pc();
=TEX
}%ignore

ⓈHOLCONST
│ ⦏SUb⋎o⦎: 'a ℙ → 'a ℙ
├───────────
│ ∀so⦁ SUb⋎o so = {β | ∀η⦁ η ∈ so ⇒ η <⋎o β}
■

=GFT
⦏SUb⋎o_thm⦎ =	⊢ ∀ so γ⦁ γ ∈ SUb⋎o so ⇔ (∀ η⦁ η ∈ so ⇒ η <⋎o γ)
⦏SUb⋎o_X⋎o_thm⦎ =	⊢ ∀ α⦁ α ∈ SUb⋎o (X⋎o α)
⦏SUb⋎o_X⋎o_thm2⦎ =	⊢ ∀ α⦁ α ∈ SUb⋎o {β|β <⋎o α}
⦏SUb⋎o_mono⦎ = 	 	⊢ ∀ s t⦁ s ⊆ t ⇒ SUb⋎o t ⊆ SUb⋎o s
⦏SUb⋎o_mono2⦎ = 	⊢ ∀ s t⦁ (SUb⋎o s) ⊆ (SUb⋎o (s ∩ t))
=TEX

\ignore{
=SML
val SUb⋎o_def = get_spec ⌜SUb⋎o⌝;

push_pc "hol1";

set_goal([], ⌜∀so γ⦁ γ ∈ SUb⋎o so ⇔ ∀η⦁ η ∈ so ⇒ η <⋎o γ⌝);
a (rewrite_tac[SUb⋎o_def]);
val SUb⋎o_thm = save_pop_thm "SUb⋎o_thm";

set_goal([], ⌜∀α⦁ α ∈ SUb⋎o (X⋎o α)⌝);
a (strip_tac THEN rewrite_tac[SUb⋎o_thm, X⋎o_def, ≤⋎o_def]
	THEN REPEAT strip_tac);
val SUb⋎o_X⋎o_thm = save_pop_thm "SUb⋎o_X⋎o_thm";

set_goal([], ⌜∀α⦁ α ∈ SUb⋎o {β | β <⋎o α}⌝);
a (strip_tac THEN rewrite_tac[SUb⋎o_thm, ≤⋎o_def]
	THEN REPEAT strip_tac);
val SUb⋎o_X⋎o_thm2 = save_pop_thm "SUb⋎o_X⋎o_thm2";

set_goal([], ⌜∀ s t⦁ s ⊆ t ⇒ (SUb⋎o t) ⊆ (SUb⋎o s)⌝);
a (rewrite_tac[SUb⋎o_def, sets_ext_clauses] THEN REPEAT strip_tac);
a (REPEAT (asm_fc_tac[]));
val SUb⋎o_mono = save_pop_thm "SUb⋎o_mono";

set_goal([], ⌜∀ s t⦁ (SUb⋎o s) ⊆ (SUb⋎o (s ∩ t))⌝);
a (rewrite_tac[SUb⋎o_def, sets_ext_clauses] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 3 ⌜η⌝);
val SUb⋎o_mono2 = save_pop_thm "SUb⋎o_mono2";

pop_pc();
=TEX
}%ignore

ⓈHOLCONST
│ ⦏⋃⋎o⦎: 'a ℙ → 'a
├───────────
│ ∀so⦁ ⋃⋎o so = ⋂⋎o (Ub⋎o so)
■

=GFT
⦏lt⋎o_⋃⋎o⦎ =
	⊢ ∀ so α⦁ α ∈ Ub⋎o so ⇒
		(∀γ⦁ γ <⋎o ⋃⋎o so ⇔ (∃η⦁ η ∈ so ∧ γ <⋎o η))
⦏lt⋎o_⋃⋎o2⦎ =
	⊢ ∀ α γ⦁ γ <⋎o ⋃⋎o {β|β <⋎o α} ⇔ (∃ η⦁ η <⋎o α ∧ γ <⋎o η)
=TEX

\ignore{
=SML
val ⋃⋎o_def = get_spec ⌜⋃⋎o⌝;

push_pc "hol1";

set_goal([], ⌜∀so α⦁ α ∈ Ub⋎o so ⇒
	(∀γ⦁ γ <⋎o ⋃⋎o so ⇔ ∃η⦁ η ∈ so ∧ γ <⋎o η)⌝);
a (rewrite_tac[⋃⋎o_def]
	THEN REPEAT_N 5 strip_tac
	THEN_TRY all_ufc_⇔_rewrite_tac [⋂⋎o_thm2]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (contr_tac);
a (lemma_tac ⌜γ ∈ Ub⋎o so⌝);
(* *** Goal "1.1" *** *)
a (asm_rewrite_tac [Ub⋎o_thm]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜η⌝);
a (asm_rewrite_tac[≤⋎o_lt⋎o]);
(* *** Goal "1.2" *** *)
a (asm_fc_tac[]);
a (fc_tac[irrefl⋎o_thm]);
(* *** Goal "2" *** *)
a (all_fc_tac[Ub⋎o_thm]);
a (all_fc_tac[lt⋎o_≤⋎o_trans]);
val lt⋎o_⋃⋎o = save_pop_thm "lt⋎o_⋃⋎o";

=IGN
set_goal([], ⌜∀so1 so2 α⦁ α ∈ Ub⋎o so2 ∧ so1 ⊆ so2
	⇒ ⋃⋎o so1 ≤⋎o ⋃⋎o so2⌝);
a (REPEAT strip_tac THEN rewrite_tac[]);

=SML
set_goal([], ⌜∀α γ⦁ γ <⋎o ⋃⋎o {β | β <⋎o α} ⇔ ∃η⦁ η <⋎o α ∧ γ <⋎o η⌝);
a (REPEAT ∀_tac);
a (lemma_tac ⌜∃ η⦁ η ∈ Ub⋎o {β|β <⋎o α}⌝
	THEN1 (∃_tac ⌜α:'a⌝ THEN rewrite_tac[Ub⋎o_X⋎o_thm2]));
a (all_ufc_⇔_tac[lt⋎o_⋃⋎o]);
a (asm_rewrite_tac[]);
val lt⋎o_⋃⋎o2 = save_pop_thm "lt⋎o_⋃⋎o2";

=IGN
set_goal([], ⌜∀so⦁ (∃α⦁ α ∈ Ub⋎o so) ⇒
	∀γ⦁ ⋃⋎o so <⋎o γ ⇔ ∃η⦁ η ∈ Ub⋎o so ⇒ η <⋎o γ⌝);
a (rewrite_tac[⋃⋎o_def]
	THEN REPEAT_N 5 strip_tac);
	THEN_TRY all_ufc_⇔_rewrite_tac [⋂⋎o_thm2]
	THEN REPEAT strip_tac);

pop_pc();
=TEX
}%ignore

ⓈHOLCONST
│ ⦏SSup⋎o⦎: 'a ℙ → 'a
├───────────
│ ∀so⦁ SSup⋎o so = ⋂⋎o (SUb⋎o so)
■


=GFT
⦏lt⋎o_SSup⋎o⦎ =		⊢ ∀ so α⦁ α ∈ SUb⋎o so ⇒
	      			(∀ γ⦁ γ <⋎o SSup⋎o so ⇔ (∃ η⦁ η ∈ so ∧ γ ≤⋎o η))
⦏SSup⋎o_lt⋎o⦎ =	   ⊢ ∀ α⦁ SSup⋎o {β|β <⋎o α} = α
⦏SSup⋎o_lt⋎o2⦎ =	⊢ ∀ so α β⦁ β ∈ so ∧ β ∈ SUb⋎o so ⇒
	       			(SSup⋎o so <⋎o α ⇔ (∃ β⦁ β ∈ SUb⋎o so ∧ β <⋎o α))
⦏SSup⋎o_X⋎o⦎ =		⊢ ∀ α⦁ SSup⋎o (X⋎o α) = α
=TEX

\ignore{
=SML
val SSup⋎o_def = get_spec ⌜SSup⋎o⌝;

push_pc "hol1";

set_merge_pcs ["rbjmisc", "'ordinals"];

set_goal([], ⌜∀so α⦁ α ∈ SUb⋎o so ⇒
	(∀γ⦁ γ <⋎o SSup⋎o so ⇔ ∃η⦁ η ∈ so ∧ γ ≤⋎o η)⌝);
a (rewrite_tac[SSup⋎o_def]
	THEN REPEAT_N 5 strip_tac
	THEN_TRY all_ufc_⇔_rewrite_tac [⋂⋎o_thm2]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (contr_tac);
a (lemma_tac ⌜γ ∈ SUb⋎o so⌝);
(* *** Goal "1.1" *** *)
a (asm_rewrite_tac [SUb⋎o_thm]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜η⌝);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac[≤⋎o_lt⋎o]);
(* *** Goal "1.2" *** *)
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac[SUb⋎o_thm]);
a (all_fc_tac[≤⋎o_lt⋎o_trans]);
val lt⋎o_SSup⋎o = save_pop_thm "lt⋎o_SSup⋎o";

set_goal([], ⌜∀α⦁ SSup⋎o {β | β <⋎o α} = α⌝);
a (REPEAT ∀_tac THEN once_rewrite_tac[ord_ext_thm]);
a (lemma_tac ⌜∃ η⦁ η ∈ SUb⋎o {β|β <⋎o α}⌝
	THEN1 (∃_tac ⌜α:'a⌝ THEN rewrite_tac[SUb⋎o_X⋎o_thm2]));
a (all_ufc_⇔_tac[lt⋎o_SSup⋎o]);
a (asm_rewrite_tac[]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [≤⋎o_lt⋎o_trans]);
(* *** Goal "2" *** *)
a (∃_tac ⌜δ⌝ THEN asm_rewrite_tac[]);
val SSup⋎o_lt⋎o = save_pop_thm "SSup⋎o_lt⋎o";

set_goal([], ⌜∀so β γ⦁ β ∈ so ∧ γ ∈ SUb⋎o so ⇒
	(∀α⦁ SSup⋎o so <⋎o α ⇔ ∃η⦁ η ∈ SUb⋎o so ∧ η <⋎o α)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[SSup⋎o_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜⋂⋎o (SUb⋎o so)⌝ THEN asm_rewrite_tac[]);
a (GET_ASM_T ⌜γ ∈ SUb⋎o so⌝ (asm_tac o (rewrite_rule [SUb⋎o_def])));
a (PC_T1 "sets_ext" fc_tac [⋂⋎o_thm]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜⋂⋎o (SUb⋎o so) ∈ SUb⋎o so⌝ THEN1 PC_T1 "sets_ext" ufc_tac [⋂⋎o_thm]);
a (PC_T1 "sets_ext" ufc_tac [⋂⋎o_thm]);
a (spec_nth_asm_tac 1 ⌜η⌝);
(* *** Goal "2.1" *** *)
a (var_elim_asm_tac ⌜η = ⋂⋎o (SUb⋎o so)⌝);
(* *** Goal "2.2" *** *)
a (all_fc_tac [trans⋎o_thm]);
val SSup⋎o_lt⋎o2 = save_pop_thm "SSup⋎o_lt⋎o2";

set_goal([], ⌜∀α⦁ SSup⋎o (X⋎o α) = α⌝);
a (strip_tac THEN rewrite_tac[X⋎o_def, SSup⋎o_lt⋎o]);
val SSup⋎o_X⋎o = save_pop_thm "SSup⋎o_X⋎o";

=IGN
set_goal([], ⌜∀γ P⦁ (∃η⦁ η ∈ SUb⋎o {β | P β γ}) ∧ (∀β⦁ β <⋎o γ ⇔ P β γ)
	⇒ γ = SSup⋎o{β | P β γ}⌝);
a (once_rewrite_tac[ord_ext_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_ufc_⇔_rewrite_tac [lt⋎o_SSup⋎o]);
a (∃_tac ⌜δ⌝ THEN all_asm_fc_tac[] THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac
	THEN all_ufc_⇔_rewrite_tac [lt⋎o_SSup⋎o]
	THEN strip_tac);
a (DROP_NTH_ASM_T 2 ante_tac
	THEN SYM_ASMS_T rewrite_tac
	THEN strip_tac);
a (all_fc_tac [≤⋎o_lt⋎o_trans]);
=TEX
}%ignore

=GFT
⦏SSup⋎o_mono⦎ =		⊢ ∀ s t⦁ ¬ SUb⋎o s = {} ⇒ SSup⋎o (s ∩ t) ≤⋎o SSup⋎o s
⦏SSup⋎o_mono2⦎ =  ⊢ ∀ s t⦁ ¬ SUb⋎o s = {} ∧ ¬ SUb⋎o t = {}
         ⇒ SSup⋎o s <⋎o SSup⋎o t ⇒ SSup⋎o (s ∩ t) <⋎o SSup⋎o t
=TEX

\ignore{
=SML
set_goal([], ⌜∀ s t⦁ ¬ SUb⋎o s = {} ⇒ SSup⋎o (s ∩ t) ≤⋎o SSup⋎o s⌝);
a (rewrite_tac [SSup⋎o_def] THEN REPEAT strip_tac);
a (asm_tac (list_∀_elim [⌜s:'a ℙ⌝, ⌜t:'a ℙ⌝ ] SUb⋎o_mono2));
a (rewrite_tac [≤⋎o_def] THEN contr_tac);
a (cases_tac ⌜SUb⋎o s = SUb⋎o (s ∩ t)⌝ );
(* *** Goal "1" *** *)
a (swap_nth_asm_concl_tac 2 THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac [⋂⋎o_mono_thm]);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule [≤⋎o_def])));
val SSup⋎o_mono = save_pop_thm "SSup⋎o_mono";

set_goal([], ⌜∀s t⦁ ¬ SUb⋎o s = {} ∧ ¬ SUb⋎o t = {} ⇒ SSup⋎o s <⋎o SSup⋎o t ⇒ SSup⋎o (s ∩ t) <⋎o SSup⋎o t⌝);
a (REPEAT strip_tac);
a (all_fc_tac [SSup⋎o_mono]);
a (spec_nth_asm_tac 1  ⌜t⌝);
a (all_fc_tac [≤⋎o_lt⋎o_trans]);
val SSup⋎o_mono2 = save_pop_thm "SSup⋎o_mono2";
=SML
add_rw_thms [Ub⋎o_thm, SUb⋎o_thm, Ub⋎o_X⋎o_thm, SUb⋎o_X⋎o_thm,
	Ub⋎o_X⋎o_thm2, SUb⋎o_X⋎o_thm2, lt⋎o_⋃⋎o2, SSup⋎o_lt⋎o, SSup⋎o_X⋎o] "'ordinals";
add_sc_thms [Ub⋎o_thm, SUb⋎o_thm, Ub⋎o_X⋎o_thm, SUb⋎o_X⋎o_thm,
	Ub⋎o_X⋎o_thm2, SUb⋎o_X⋎o_thm2, lt⋎o_⋃⋎o2, SSup⋎o_lt⋎o, SSup⋎o_X⋎o] "'ordinals";
add_st_thms [lt⋎o_⋃⋎o2] "'ordinals";
set_merge_pcs ["rbjmisc", "'ordinals"];
=TEX
}%ignore

\subsection{Images and Limits}

In order to define operators over the 'a ordinals (without undesirable complications) the 'a ordinals must be closed under the operations.
If we want to use such operations in formulating our strong axiom of infinity, then we would need to assert sufficiently strong closure conditions in advance of our axiom of infinity.

The basis for the closure principle on which definitions of functions like 'a ordinal addition are based is a related to the axiom of replacement in set theory.
In talking of 'a ordinals the corresponding notion is that or regularity, which we can define without any kind of axiom of infinity as follows.

First the notion of cofinality.
This definition is perhaps a little eccentric, in that it is defined over all 'a ordinals not just limit 'a ordinals, and in that it is couched in terms of arbitrary functions rather than increasing sequences, and consequently takes the supremum of the image rather than the limit of a sequence.

The supremum of an image will prove more generally useful so we give it a name.

By the image of an 'a `ordinal' through a map, I mean the image of the set of 'a ordinals less than that 'a ordinal ():

ⓈHOLCONST
│ ⦏Image⋎o⦎: (('a → 'b) × 'a) → 'b ℙ
├───────────
│ ∀f β⦁ Image⋎o(f, β) = {δ | ∃η⦁ η <⋎o β ∧ f η = δ}
■

=GFT
⦏Image⋎o_thm⦎ =	⊢ ∀ f β γ⦁ γ ∈ Image⋎o (f, β) ⇔ (∃ η⦁ η <⋎o β ∧ γ = f η)
⦏Image⋎o_zero⋎o_thm⦎ =	⊢ ∀ f⦁ Image⋎o (f, 0⋎o) = {}
⦏Image⋎o_mono_thm⦎ =	⊢ ∀ f α β⦁ α ≤⋎o β ⇒ Image⋎o (f, α) ⊆ Image⋎o (f, β)
⦏Ub⋎o_Image⋎o_zero⋎o_thm⦎ =	⊢ ∀ f γ⦁ γ ∈ Ub⋎o (Image⋎o (f, 0⋎o))
⦏SUb⋎o_Image⋎o_zero⋎o_thm⦎ =	⊢ ∀ f γ⦁ γ ∈ SUb⋎o (Image⋎o (f, 0⋎o))
=TEX

\ignore{
=SML
val Image⋎o_def = get_spec ⌜Image⋎o⌝;

set_goal([], ⌜∀f β γ⦁ γ ∈ Image⋎o (f, β) ⇔ ∃η⦁ η <⋎o β ∧ γ = f η⌝);
a (rewrite_tac[Image⋎o_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[]);
val Image⋎o_thm = save_pop_thm "Image⋎o_thm";

set_goal([], ⌜∀f⦁ Image⋎o(f, 0⋎o) = {}⌝);
a (PC_T1 "sets_ext" rewrite_tac[Image⋎o_thm, lt⋎o_zero⋎o_thm]);
val Image⋎o_zero⋎o_thm = save_pop_thm "Image⋎o_zero⋎o_thm";

set_goal([], ⌜∀f α β⦁ α ≤⋎o β ⇒ Image⋎o(f, α) ⊆ Image⋎o(f, β)⌝);
a (PC_T1 "sets_ext" rewrite_tac[Image⋎o_thm, lt⋎o_zero⋎o_thm]
	THEN REPEAT strip_tac);
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[]);
a (all_fc_tac[lt⋎o_≤⋎o_trans]);
val Image⋎o_mono_thm = save_pop_thm "Image⋎o_mono_thm";

set_goal([], ⌜∀f γ⦁ γ ∈ Ub⋎o(Image⋎o (f, 0⋎o))⌝);
a (rewrite_tac[Ub⋎o_thm,  Image⋎o_zero⋎o_thm]);
val Ub⋎o_Image⋎o_zero⋎o_thm = save_pop_thm "Ub⋎o_Image⋎o_zero⋎o_thm";

set_goal([], ⌜∀f γ⦁ γ ∈ SUb⋎o(Image⋎o (f, 0⋎o))⌝);
a (rewrite_tac[Image⋎o_zero⋎o_thm]);
val SUb⋎o_Image⋎o_zero⋎o_thm = save_pop_thm "SUb⋎o_Image⋎o_zero⋎o_thm";

add_rw_thms [Image⋎o_thm, Image⋎o_zero⋎o_thm, Ub⋎o_Image⋎o_zero⋎o_thm,
	    SUb⋎o_Image⋎o_zero⋎o_thm] "'ordinals";
add_sc_thms [Image⋎o_thm, Image⋎o_zero⋎o_thm, Ub⋎o_Image⋎o_zero⋎o_thm,
	    SUb⋎o_Image⋎o_zero⋎o_thm] "'ordinals";
add_st_thms [] "'ordinals";
set_merge_pcs ["rbjmisc", "'ordinals"];
=TEX
}%ignore

$SupIm⋎o$ is the supremum of the image of an 'a ordinal.
In the case that the function is increasing then this is the limit of a $β$ sequence.
Sometimes where such a limit is used in the literature there is no apparent benefit from the restriction to increasing sequences and I use $SupIm⋎o$ of an arbitary map, as in, for example, the definition of 'a ordinal addition.

ⓈHOLCONST
│ ⦏SupIm⋎o⦎: (('a → 'a) × 'a) → 'a
├───────────
│ ∀x⦁ SupIm⋎o x = ⋃⋎o (Image⋎o x)
■

Most of the functions we will want to define will be continuous, i.e. the value at a limit ordinal will be the limit of the values at points below that ordinal.
For the function to be defined at those limit ordinals, the limits in the range must exist,
The requirenent that they always do exist is similar in character and strength to the set theoretic axiom of replacement.
In set theory this asserts that any collection which is the same size as a set will also be a set.

In the theory of ordinals it is the notion of regularity which plays this role, and the theorems which we need to establish that recursive definitions of functions over the ordinals do indeed coherently define functions will depend upon the assumption that the ordinal types are {\it regular}.

We therefore now provide some vocabulary appropriate both to that limited requirement and to stronger axioms of infinity yielding theories comparable or greater in strength to ZFC set theory.

\ignore{
=SML
add_rw_thms [SUb⋎o_Image⋎o_zero⋎o_thm] "'ordinals";
add_sc_thms [SUb⋎o_Image⋎o_zero⋎o_thm] "'ordinals";
add_st_thms [] "'ordinals";
set_merge_pcs ["rbjmisc", "'ordinals"];
=TEX
}%ignore

$SSupIm⋎o$ is the strict supremum of the image of an 'a ordinal.

ⓈHOLCONST
│ ⦏SSupIm⋎o⦎: (('a → 'a) × 'a) → 'a
├───────────
│ ∀x⦁ SSupIm⋎o x = SSup⋎o (Image⋎o x)
■

In general the supremum of an image only exists if the image is bounded above.
However, one of the principle purposes of our axiom of strong infinity is to ensure that such bounds exist.
By analogy with replacement in set theory, which tells us that the image of a set is a set, we know that the image of a bounded collection of 'a ordinals is itself bounded.
This enables us to prove the following results about $SupIm⋎o$ and $SSupIm⋎o$.

=GFT
Ub⋎o_Image⋎o_thm	?⊢ ∀ f β⦁ ∃ γ⦁ γ ∈ Ub⋎o (Image⋎o (f, β))
⦏lt⋎o_SupIm⋎o⦎ =		?⊢ ∀ f β γ⦁ γ <⋎o SupIm⋎o (f, β) ⇔ (∃ η⦁ η <⋎o β ∧ γ <⋎o f η)
⦏SupIm⋎o_zero⋎o⦎ =	?⊢ ∀ f β γ⦁ ¬ γ <⋎o SupIm⋎o (f, 0⋎o)
⦏lt⋎o_SSupIm⋎o⦎ =	  ⊢ ∀ f β γ⦁ γ <⋎o SSupIm⋎o (f, β) ⇔ (∃ η⦁ η <⋎o β ∧ γ ≤⋎o f η)
⦏SSupIm⋎o_zero⋎o⦎ =	?⊢ ∀ f β γ⦁ ¬ γ <⋎o SSupIm⋎o (f, 0⋎o)
=TEX

\ignore{
=SML
val SupIm⋎o_def = get_spec ⌜SupIm⋎o⌝;
val SSupIm⋎o_def = get_spec ⌜SSupIm⋎o⌝;

=IGN
stop;

set_goal([], ⌜∀f β γ⦁ γ <⋎o SupIm⋎o (f, β) ⇔ ∃η⦁ η <⋎o β ∧ γ <⋎o f η⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [SupIm⋎o_def]);
a (strip_asm_tac (list_∀_elim [⌜f⌝, ⌜β⌝] Ub⋎o_Image⋎o_thm));
a (all_ufc_⇔_rewrite_tac [∀_elim ⌜Image⋎o (f, β)⌝ lt⋎o_⋃⋎o]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜$"η'"⌝ THEN asm_rewrite_tac[]);
a (SYM_ASMS_T rewrite_tac);
(* *** Goal "2" *** *)
a (∃_tac ⌜f η⌝ THEN asm_rewrite_tac[Image⋎o_thm]);
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[]);
val lt⋎o_SupIm⋎o = save_pop_thm "lt⋎o_SupIm⋎o";

=IGN
set_goal([], ⌜∀f γ⦁ ¬ γ <⋎o SupIm⋎o (f, 0⋎o)⌝);
a (rewrite_tac[SupIm⋎o_def, ⋃⋎o_def]);
val SupIm⋎o_zero⋎o = save_pop_thm "SupIm⋎o_zero⋎o";

=IGN
set_goal([], ⌜∀f α β⦁ α ≤⋎o β ⇒ SupIm⋎o (f, α) ≤⋎o SupIm⋎o (f, β)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[SupIm⋎o_def] THEN REPEAT strip_tac);

set_goal([], ⌜∀f β γ⦁ γ <⋎o SSupIm⋎o (f, β) ⇔ ∃η⦁ η <⋎o β ∧ γ ≤⋎o f η⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [SSupIm⋎o_def]);
a (strip_asm_tac (list_∀_elim [⌜f⌝, ⌜β⌝] SUb⋎o_Image⋎o_thm));
a (all_ufc_⇔_rewrite_tac [∀_elim ⌜Image⋎o (f, β)⌝ lt⋎o_SSup⋎o]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜$"η'"⌝ THEN asm_rewrite_tac[]);
a (SYM_ASMS_T rewrite_tac);
(* *** Goal "2" *** *)
a (∃_tac ⌜f η⌝ THEN asm_rewrite_tac[Image⋎o_thm]);
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[]);
val lt⋎o_SSupIm⋎o = save_pop_thm "lt⋎o_SSupIm⋎o";

set_goal([], ⌜∀f⦁ SSupIm⋎o (f, 0⋎o) = 0⋎o⌝);
a (rewrite_tac[ord_ext_thm, lt⋎o_SSupIm⋎o]);
val SSupIm⋎o_zero⋎o = save_pop_thm "SSupIm⋎o_zero⋎o";

add_rw_thms [lt⋎o_SupIm⋎o, lt⋎o_SSupIm⋎o, SupIm⋎o_zero⋎o, SSupIm⋎o_zero⋎o] "'ordinals";
add_sc_thms [lt⋎o_SupIm⋎o, lt⋎o_SSupIm⋎o, SupIm⋎o_zero⋎o, SSupIm⋎o_zero⋎o] "'ordinals";
add_st_thms [lt⋎o_SupIm⋎o, lt⋎o_SSupIm⋎o, SupIm⋎o_zero⋎o, SSupIm⋎o_zero⋎o] "'ordinals";
set_merge_pcs ["rbjmisc", "'ordinals"];
=TEX
}%ignore

\subsection{Ordering Sets of Ordinals}

Though we get an arbitrary well-ordering of sets as $⌜$$<⋎o⌝$, the particular order of sets by the supremum of their members (under $⌜$$<⋎o⌝$) is useful. 

The following function yeilds the downward closure of a set.

ⓈHOLCONST
│ ⦏Dcl⋎o⦎: 'a ℙ → 'a ℙ
├───────────
│ ∀s⦁ Dcl⋎o s = {x | ∃y⦁ y ∈ s ∧ x ≤⋎o y}
■


=SML
declare_infix(400, "<⋎u");
=TEX

ⓈHOLCONST
│ ⦏$<⋎u⦎: 'a ℙ → 'a ℙ → BOOL
├───────────
│ ∀s t⦁ s <⋎u t ⇔ Dcl⋎o s ⊂ Dcl⋎o t
■

=GFT
⦏lt⋎u_∩_mono⦎ = 	⊢ ∀ α β⦁ α <⋎u β ⇒ (α ∩ β) <⋎u β
=TEX

\ignore{
=SML
val Dcl⋎o_def = get_spec ⌜$Dcl⋎o⌝;
val lt⋎u_def = get_spec ⌜$<⋎u⌝;

set_goal([], ⌜∀ α β⦁ β <⋎u α ⇒ (β ∩ α) <⋎u α⌝);
a (REPEAT ∀_tac THEN rewrite_tac[lt⋎u_def, Dcl⋎o_def, sets_ext_clauses]);
a (contr_tac THEN all_asm_fc_tac[]);
a (all_asm_fc_tac[]);
val lt⋎u_mono = save_pop_thm "lt⋎u_mono";
=TEX
}%ignore

=GFT
⦏lt⋎u_well_founded_thm⦎  ⊢ UWellFounded $<⋎u:
⦏lt⋎u_well_founded_thm3⦎  ⊢ well_founded $<⋎u:
⦏lt⋎u_induction_thm⦎ = ⊢ ∀ p⦁ (∀ x⦁ (∀ y⦁ y <⋎u x ⇒ p y) ⇒ p x) ⇒ (∀ x⦁ p x)
=TEX

\ignore{
=IGN
set_goal([], ⌜UWellFounded $<⋎u⌝);
a (lemma_tac ⌜$<⋎u = λs t⦁ Dcl⋎o s ⊂ Dcl⋎o t⌝);
(* *** Goal "1" *** *)
a (once_rewrite_tac [ext_thm]);
a (once_rewrite_tac [ext_thm]);
a (rewrite_tac [lt⋎u_def]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
a (rewrite_tac[
⇒_elim (list_∀_elim [⌜Dcl⋎o:'a ℙ → 'a ℙ⌝, ⌜$⊂:'a  ℙ → 'a ℙ → BOOL⌝] u_well_founded_pullback_thm) lt⋎o_well_founded_thm]);
val lt⋎u_well_founded_thm = save_pop_thm ("lt⋎u_well_founded_thm");

val lt⋎u_well_founded_thm3 = save_thm ("lt⋎u_well_founded_thm3",
    rewrite_rule [tac_proof(([], ⌜∀$<<⦁ UWellFounded $<< ⇔ well_founded $<<⌝), rewrite_tac [get_spec ⌜well_founded⌝, u_well_founded_induction_thm])] lt⋎u_well_founded_thm);

val lt⋎u_induction_thm = save_thm ("lt⋎u_induction_thm",
     rewrite_rule[∀_elim ⌜$<⋎u⌝ u_well_founded_induction_thm] lt⋎u_well_founded_thm);
=TEX
}%ignore

ⓈHOLCONST
│ ⦏X⋎u⦎: 'a ℙ → 'a ℙ ℙ
├───────────
│	∀x:'a ℙ⦁ X⋎u x  = {y:'a ℙ| y <⋎u x}
■

ⓈHOLCONST
│ ⦏I⋎u⦎: 'a → 'a
├───────────
│	∀x⦁ I⋎u x  =  x
■

ⓈHOLCONST
│ ⦏Image⋎u⦎: ('a ℙ → 'b) × 'a ℙ  → 'b ℙ
├───────────
│	∀(f:'a ℙ → 'b) (w:'a ℙ)⦁ Image⋎u (f, w) =
│	       {x:'b | ∃y:'a ℙ⦁ y <⋎u w ∧ x = f (y ∩ w)}
■

\section{ENUMERATIONS AND LIMITS}

When we come to the applications of these ordinals enumerations will be central, and in order to define enumerations recursively it will be necessary to form limits.

This section introduces the chosen representation of enumerations, defining also the notion of directed set of enumerations and limits of directed sets.
The representation of these enumerations is determined by the primary application intended, which is the definition of new types (usually recursive datatypes) in HOL.
For this purpose we need a sufficiently large type of ordinals to act as represetatives, and we construct a ``projection function'' from those representatives which is the inverse of the composite of the constructor functions which allow new values of the type to be constructed from existing values together with additional information.
The projection returns the information used to construct the object whose representative it is applied to.

In addition to the typical recursive datatype definition, in which a set of representatives which is closed under the constructors is sought, very similar methods may be used in constructing what I refer to here as foundational ontologies, in which case closure may not be possible because the constructors in some cases will effect an increasing cardinality at each rank.

An enumeration for present purposes is therefore a function from an initial segment of any type considered as ordinals to some other type.
The strict supremum of the domain of the enumeration serves to identify the domain (since it must be an initial segment), and a HOL total function between the type of ordinals and the type of values being enumerated provides the details of the enumeration.
The values assigned to that function beyond the domain of the enumeration are irrelevant but in order to achieve uniqueness in the representation of the sequences we expect that they will always take the same value, viz ⌜Choose \{\}⌝ (the member of the empty set!).

The type abbreviation PEN is used, an acronym for Partial ENumeration.
=SML
declare_type_abbrev("PEN", ["'a", "'b"], ⓣ'a ×  ('a → 'b)⌝);
=TEX

There is a difficulty here arising from the intended use of enumerations for the representation of foundational ontologies, in which case the enumeration will be total over the ordinal type selected and no type of ordinals will yield a fixed point.
For such enumerations the type above won't work since there will not be an ordinal whose extension is the whole type.

The required limit operation will therefore yield a disjoint union.
Either the ordinal/map pair, or just the map, the domain for which will then be the whole type of ordinals.

There is some doubt in my mind about the extent to which partial and total enumerations should be treated together so initially I am going to do both combined operations and separate operation of partial enumerations.
Hence the following type abbreviation for the total or partial case:

The type abbreviation POTEN is used, an acronym for Partial Or Total ENumeration.
=SML
declare_type_abbrev("POTEN", ["'a", "'b"], ⓣ(ONE + 'a) ×  ('a → 'b)⌝);
=TEX

The first limit operation defined below gives the upper bound of a set of compatible PENs, and we therefore need to define first an ordering over compatible PENs.

=SML
declare_infix(400, "<⋎p");
=TEX

ⓈHOLCONST
│ $⦏<⋎p⦎: ('a,'b)PEN → ('a,'b)PEN → BOOL
├───────────
│ ∀x y f g⦁ (x, f) <⋎p (y, g) ⇔ x <⋎o y ∧ (∀z⦁ z <⋎o x ⇒ f z = g z)
■

=SML
declare_infix(400, "<⋎q");
=TEX

ⓈHOLCONST
│ $⦏<⋎q⦎: ('a,'b)POTEN → ('a,'b)POTEN → BOOL
├───────────
│ ∀x y f g⦁ (x, f) <⋎q (y, g) ⇔
│     (IsR x
│      	   ∧ (IsR y ∧ (OutR x) <⋎o (OutR y) ∨ IsL y)
│      	   ∧ (∀z⦁ z <⋎o (OutR x) ⇒ f z = g z))
■

A directed set is:

ⓈHOLCONST
│ ⦏Directed⋎p⦎: ('a,'b)PEN ℙ → BOOL
├───────────
│ ∀fs⦁ Directed⋎p fs ⇔ ∀p q⦁ p ∈ fs ∧ q ∈ fs ⇒ p <⋎p q ∨ q <⋎p p ∨ p = q
■

ⓈHOLCONST
│ ⦏Directed⋎q⦎: ('a,'b)POTEN ℙ → BOOL
├───────────
│ ∀fs⦁ Directed⋎q fs ⇔ ∀p q⦁ p ∈ fs ∧ q ∈ fs ⇒ p <⋎q q ∨ q <⋎q p ∨ p = q
■

The required limit operation is then defined:

ⓈHOLCONST
│ ⦏LimitFun⋎p⦎: ('a,'b)PEN ℙ → ('a → 'b)
├───────────
│ ∀fs⦁ LimitFun⋎p fs = λx⦁ Choose
│      {z | ∃(y, f)⦁ (y, f) ∈ fs ∧ x <⋎o y ∧ z = f y}
■

ⓈHOLCONST
│ ⦏LimitFun⋎q⦎: ('a,'b)POTEN ℙ → ('a → 'b)
├───────────
│ ∀fs:('a,'b)POTEN ℙ⦁ LimitFun⋎q fs = λx:'a⦁ Choose
│      {z | ∃(y, f)⦁ (y, f) ∈ fs ∧ (IsR y ∧ x <⋎o OutR y ∨ IsL y) ∧ z = f x}
■

ⓈHOLCONST
│ ⦏LimitOrd⋎p⦎: ('a,'b)PEN ℙ → ONE + 'a
├───────────
│ ∀fs⦁ LimitOrd⋎p fs =
│       let ords = {x | ∃f⦁ (x, f) ∈ fs}
│       in if Ub⋎o ords = {}
│          then InL One
│	   else InR (⋃⋎o ords)
■

ⓈHOLCONST
│ ⦏LimitOrd⋎q⦎: ('a,'b)POTEN ℙ → ONE + 'a
├───────────
│ ∀fs⦁ LimitOrd⋎q fs =
│       if (∃f x⦁ (x, f) ∈ fs ∧ IsL x) then InL One
│       else
│       let ords = {x | ∃f⦁ (InR x, f) ∈ fs}
│       in if Ub⋎o ords = {}
│          then InL One
│	   else InR (⋃⋎o ords)
■

The q versions are a bit odd, since if there is total function in a directed set, then it is the limit.

However, a set of partial enumerations may have a total enumeration as its limit (as hinted by the type above for $⌜LimitOrd⋎p⌝$).

Combining the previous two functions we get.

ⓈHOLCONST
│ ⦏LimitPen⋎p⦎: ('a,'b)PEN ℙ → ('a,'b)POTEN
├───────────
│ ∀fs⦁ LimitPen⋎p fs = (LimitOrd⋎p fs, LimitFun⋎p fs)
■

ⓈHOLCONST
│ ⦏LimitPen⋎q⦎: ('a,'b)POTEN ℙ → ('a,'b)POTEN
├───────────
│ ∀fs⦁ LimitPen⋎q fs = (LimitOrd⋎q fs, LimitFun⋎q fs)
■

Typically the limit will be formed of a set which is the image of a set under a function which creates partial or total enumerations.

ⓈHOLCONST
│ ⦏LimPenIm⋎u⦎: ('a ℙ → ('b, 'c)POTEN) → 'a ℙ  → ('b, 'c) POTEN
├───────────
│	∀f s⦁ LimPenIm⋎u f s = LimitPen⋎q (Image⋎u (f,s)) 
■

\subsection{Relations to Enumerations}

We have theorems which give us the existence of various kinds of orderings, e.g. strict initial well-orderings, but not enumerations, so lets fix that with a function which turns any well-order into an enumeration.

We have the usual problem with cardinalities.

\ignore{
 ⓈHOLCONST
│ ⦏Wo2Enum⋎q⦎: ('a → 'a → BOOL) →  ('b, 'a )POTEN
 ├───────────
│	∀r x⦁ Wo2Enum⋎q r x = LimitPenIm⋎u (λy⦁ Wo2Enum⋎q r y)
 ■
}%ignore

\ignore{
=SML
val LimPenIm⋎u_def = get_spec ⌜LimPenIm⋎u⌝;
val LimitPen⋎q_def = get_spec ⌜LimitPen⋎q⦎⌝;
val LimitPen⋎p_def = get_spec ⌜LimitPen⋎p⌝;
val LimitOrd⋎q_def = get_spec ⌜LimitOrd⋎q⌝;
val LimitOrd⋎p_def = get_spec ⌜LimitOrd⋎p⌝;
val LimitFun⋎p_def = get_spec ⌜LimitFun⋎p⌝;
val LimitFun⋎q_def = get_spec ⌜LimitFun⋎q⌝;
val Directed⋎p⦎_def = get_spec ⌜Directed⋎p⦎⌝;
val Directed⋎q_def = get_spec ⌜Directed⋎q⌝;
val Lt⋎p_def = get_spec ⌜$<⋎p⌝;
val Lt⋎q_def = get_spec ⌜$<⋎q⌝;
val Image⋎u_def = get_spec ⌜Image⋎u⌝;
val X⋎u⦎_def = get_spec ⌜X⋎u⦎⌝;
val I⋎u⦎_def = get_spec ⌜I⋎u⦎⌝;
=TEX
}%ignore
\subsection{Defining Functions over the Ordinals}

Often functions over \emph{'a ordinals} are defined by cases in a manner analogous to primitive recursive definitions over the natural numbers (in which the cases are zero and successors) by adding a further case for limit 'a ordinals.
Its not clear whether such an approach would work for us, because there is some difficulty in dealing with the limit case.

The approach I adopt addresses directly the limit case and subsumes the whole.

It may help to think of this as definition by inequality.
Just as sets can be uniquely determined by identifying their members, so can 'a ordinals when they are represented by sets.
Though we do not represent an 'a ordinal by a set, it is nevertheless uniquely determined by its predecessors, which would have been its members if we had been working in set theory.

Thus an 'a ordinal $β$ might be defined by a sentence of the following form:

=GFT
	∀γ⦁ γ <⋎o β ⇔ formula
=TEX	

I did look for a way of automatically proving the consistency of definitions in that form, but found this to be less straightforward than I had expected.
The reason is that not all formulae of the given form are consistent.
The formula on the right has to have the property that if true for a given value $γ$ it is true also for any smaller value.

I have therefore to fall back on forms of definition more similar to those used in t042 \cite{rbjt042}.

Thus instead of the above we would have something like:

=GFT
	β = SSup⋎o {γ | formula}
=TEX	

Which is not subject to the same constraint.

A further problem is the necessary recursion in defining operations over 'a ordinals.
A more definite example is desirable so we will look at addition.

Addition could be defined as follows:

=GFT
	∀β γ η⦁ η <⋎o β +⋎o γ ⇔ η <⋎o β ∨ ∃ρ⦁ ρ <⋎o γ ∧ η = β +⋎o ρ
=TEX

The recursion here is well-founded because the addition on the right operates on smaller arguments than the one on the left.
To make this conspicuous we can rewrite the definition, first:

=GFT
	∀β γ⦁ β +⋎o γ = SSup⋎o {η | η <⋎o β ∨ ∃ρ⦁ ρ <⋎o γ ∧ η = β +⋎o ρ}
=TEX

This first step overcomes the first problem (the dependence on establishing that the formula is `downward closed', the set in the second formulation does not need to be downward closed).

A further step allows the well-foundedness of the recursion to be made more obvious.

=GFT
	∀β γ⦁ ($+⋎o β) γ = SSup⋎o ((Image⋎o ($+⋎o β) γ) ∪ {β})
=TEX

It is a feature of $SSupIm⋎o (\$+⋎o β) γ$ that it accesses values of $\$+⋎o β$ only for 'a ordinals less than $γ$.
A suitable recursion theorem is necessary to permit definitions in this form to be accepted.

There is a question in formulating such a recursion theorem as to what access to the function is required.
A maximally general theorem will allow access to a restricted version of the function, an intermediate version to the image of the values below some 'a ordinal through the map, and a minimal version to the supremum or strict supremum of the values.
At this point it is not clear to me what is likely to be most useful.

On considering this I came to the conclusion that a general principle should be provided elsewhere, and have put one ($tf\_rec\_thm2$) in t009 \cite{rbjt009}.
This provides a recursion theorem for use with any well-founded relation.

When we specialise that to the ordering over the 'a ordinals we get:

=GFT
⦏ord_rec_thm⦎ =	⊢ ∀ af⦁ ∃ f⦁ ∀ x⦁ f x = af ((x, $<⋎o) ⟨◁ f) x
=TEX

In which the operator $⟨◁$ restricts the domain of function $f$ hiding information about values for arguments not lower in the ordering than $x$.
This can be made a little slicker for use in this document by defining a more specific restriction operator:

=SML
declare_infix(400, "◁⋎o");
=TEX

ⓈHOLCONST
│ $⦏◁⋎o⦎: 'a→ ('a → 'b) → ('a → 'b)
├───────────
│ ∀x f⦁ x ◁⋎o f = (x, $<⋎o) ⟨◁ f
■

=GFT
⦏◁⋎o_fc⦎ =	⊢ ∀γ f β⦁ β <⋎o γ ⇒ (γ ◁⋎o f) β = f β
⦏Image⋎o_◁⋎o_thm⦎ =	⊢ ∀ γ f⦁ Image⋎o (γ ◁⋎o f, γ) = Image⋎o (f, γ)
⦏SupIm⋎o_◁⋎o_thm⦎ =	⊢ ∀ γ f⦁ SupIm⋎o (γ ◁⋎o f, γ) = SupIm⋎o (f, γ)
⦏SSupIm⋎o_◁⋎o_thm⦎ =	⊢ ∀γ f⦁ SSupIm⋎o (γ ◁⋎o f, γ) = SSupIm⋎o (f, γ)
=TEX

Hence:

=GFT
⦏ord_rec_thm2⦎ =	⊢ ∀ af⦁ ∃ f⦁ ∀ x⦁ f x = af (x ◁⋎o f) x
=TEX

Unfortunately this will not work with the ProofPower consistency prover, which requires a constructor (as if we were defining a function by pattern matching over a recursive data type).
To get automatic consistency proofs we need to add a dummy constructor, so:

=GFT
⦏ord_rec_thm3⦎ =	⊢ ∀ af⦁ ∃ f⦁ ∀ x⦁ f (CombI x) = af (x ◁⋎o f) x
=TEX

=GFT
⦏Image⋎o_respects_lt⋎o⦎ =   ⊢ ∀ af⦁ (λ f x⦁ af (Image⋎o (f, x)) x) respects $<⋎o
⦏Image⋎o_recursion_thm⦎ =	⊢ ∀ af⦁ ∃ f⦁ ∀ x⦁ f (CombI x) = af (Image⋎o (f, x)) x
=TEX


\ignore{
=SML
val ◁⋎o_def = get_spec ⌜$◁⋎o⌝;

set_goal([], ⌜∀γ f β⦁ β <⋎o γ ⇒ (γ ◁⋎o f) β = f β⌝);
a (REPEAT ∀_tac THEN rewrite_tac [◁⋎o_def] THEN REPEAT strip_tac
	THEN FC_T rewrite_tac [⟨◁_fc_thm]); 
val ◁⋎o_fc = save_pop_thm "◁⋎o_fc";

set_goal([], ⌜∀γ f⦁ Image⋎o (γ ◁⋎o f, γ) = Image⋎o (f, γ)⌝);
a (REPEAT ∀_tac
  	THEN rewrite_tac [Image⋎o_def, sets_ext_clauses]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [◁⋎o_fc]);
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [◁⋎o_fc]);
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[]);
val Image⋎o_◁⋎o_thm = save_pop_thm "Image⋎o_◁⋎o_thm";

set_goal([], ⌜∀γ f⦁ SupIm⋎o (γ ◁⋎o f, γ) = SupIm⋎o (f, γ)⌝);
a (REPEAT strip_tac THEN rewrite_tac [SupIm⋎o_def, Image⋎o_◁⋎o_thm]);
val SupIm⋎o_◁⋎o_thm = save_pop_thm "SupIm⋎o_◁⋎o_thm";

set_goal([], ⌜∀γ f⦁ SSupIm⋎o (γ ◁⋎o f, γ) = SSupIm⋎o (f, γ)⌝);
a (REPEAT strip_tac THEN rewrite_tac [SSupIm⋎o_def, Image⋎o_◁⋎o_thm]);
val SSupIm⋎o_◁⋎o_thm = save_pop_thm "SSupIm⋎o_◁⋎o_thm";

val ord_rec_thm = save_thm("ord_rec_thm",
	rewrite_rule [lt⋎o_well_founded_thm2] (∀_elim ⌜$<⋎o: 'a → 'a → BOOL⌝ tf_rec_thm2));

set_goal([], ⌜∀ af⦁ ∃ f:'a → 'a⦁ ∀ x⦁ f x = af (x ◁⋎o f) x⌝);
a (rewrite_tac[◁⋎o_def, ord_rec_thm]);
val ord_rec_thm2 = save_pop_thm "ord_rec_thm2";

set_goal ([], ⌜∀ af⦁ ∃ f:'a → 'a⦁ ∀ x⦁ f (CombI x) = af (x ◁⋎o f) x⌝);
a (strip_tac);
a (strip_asm_tac (∀_elim ⌜af⌝ ord_rec_thm2));
a (∃_tac ⌜f⌝ THEN asm_rewrite_tac [get_spec ⌜CombI⌝]);
val ord_rec_thm3 = save_pop_thm "ord_rec_thm3";

=IGN
set_flag ("pp_show_HOL_types", true);
set_flag ("pp_show_HOL_types", false);
=SML

set_goal([], ⌜∀af⦁ (λ(f:'a → 'a) (x:'a)⦁ af (Image⋎o (f, x)) x) respects $<⋎o⌝);
a (rewrite_tac [get_spec ⌜$respects⌝] THEN REPEAT strip_tac);
a (LEMMA_T ⌜Image⋎o (g, x) = Image⋎o (h, x)⌝ rewrite_thm_tac);
a (rewrite_tac[sets_ext_clauses, Image⋎o_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac);
a (lemma_tac ⌜tc $<⋎o η x⌝ THEN1 fc_tac [tc_incr_thm]);
a (ASM_FC_T (rewrite_tac o list_map_eq_sym_rule) []);
(* *** Goal "2" *** *)
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac);
a (lemma_tac ⌜tc $<⋎o η x⌝ THEN1 fc_tac [tc_incr_thm]);
a (ASM_FC_T rewrite_tac []);
val Image⋎o_respects_lt⋎o_thm = save_pop_thm "Image⋎o_respects_lt⋎o_thm";

set_goal([], ⌜∀ af:'a ℙ → 'a → 'a⦁ ∃ f⦁ ∀x:'a⦁ f (CombI x) = af (Image⋎o (f, x)) x⌝);
a (REPEAT strip_tac THEN_TRY rewrite_tac[get_spec ⌜CombI⌝]);
a (∃_tac ⌜fix (λf x⦁ af (Image⋎o (f, x)) x)⌝);
a (asm_tac Image⋎o_respects_lt⋎o_thm);
a (asm_tac lt⋎o_well_founded_thm3);
a (spec_nth_asm_tac 2 ⌜af⌝);
a (all_fc_tac [get_spec ⌜fix⌝]);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac[ext_thm]);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac []);
val Image⋎o_recursion_thm = save_pop_thm "Image⋎o_recursion_thm";
=TEX
}%ignore

Rather than having specific recursion theorems for definitions involving SupIm or SSupIm, we apply the required domain restriction to the function being defined wherever it is used on the right of the definition.

For functions to be defined over sets:

=SML
declare_infix(400, "◁⋎u");
=TEX

ⓈHOLCONST
│ $⦏◁⋎u⦎: 'a ℙ → ('a ℙ → 'b) → ('a ℙ → 'b)
├───────────
│ ∀x f⦁ x ◁⋎u f = (x, $<⋎u) ⟨◁ f
■

We want to know that recursive definitions done in this way are well-founded.

=GFT
⦏◁⋎u_fc⦎ =	⊢ ∀γ f β⦁ β <⋎u γ ⇒ (γ ◁⋎u f) β = f β
⦏Image⋎u_◁⋎u_thm⦎ =	? ⊢ ∀γ f⦁ Image⋎u (γ ◁⋎u f, γ) = Image⋎u (f, γ)
⦏LimIm⋎u_◁⋎u_thm⦎ =	? ⊢ ∀γ f⦁ SupIm⋎u (γ ◁⋎u f, γ) = SupIm⋎u (f, γ)
⦏LimitPen⋎u_◁⋎u_thm⦎ =	? ⊢ ∀γ f⦁ LimitPen⋎u (γ ◁⋎u f, γ) = LimitPen⋎u  (f, γ)
=TEX

\ignore{
=IGN
val ◁⋎u_def = get_spec ⌜$◁⋎u⌝;

set_goal([], ⌜∀f β γ ⦁ β <⋎u γ ⇒ (γ ◁⋎u f) β = f β⌝);
a (REPEAT ∀_tac THEN rewrite_tac [◁⋎u_def] THEN REPEAT strip_tac
	THEN FC_T rewrite_tac [⟨◁_fc_thm]); 
val ◁⋎u_fc = save_pop_thm "◁⋎u_fc";

=IGN
stop;

set_flag("pp_show_HOL_types", true);
set_flag("pp_show_HOL_types", false);

=IGN
(* GOAL*1 *)
set_goal([], ⌜∀α f⦁¬ SUb⋎o α = {} ⇒  Image⋎u (α ◁⋎u f, α) = Image⋎u (f, α)⌝);
a (REPEAT strip_tac);
a (rewrite_tac [Image⋎u_def, sets_ext_clauses]
	THEN (REPEAT strip_tac));
a (rewrite_tac [Image⋎u_def]);
	THEN (REPEAT strip_tac));
(* *** Goal "1" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]
  THEN all_fc_tac[◁⋎u_fc]);
  
a (asm_rewrite_tac[]);

lt⋎u_mono;

a (lemma_tac ⌜y <⋎u α ⇒ (y ∩ α) <⋎u α⌝);

(* *** Goal "1.1" *** *)
a (rewrite_tac[lt⋎u_def, SSup⋎o_def, SUb⋎o_def]);
a (fc_tac [◁⋎u_fc]);
a (∃_tac ⌜y: 'b ℙ⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [◁⋎o_fc]);
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[]);
val Image⋎o_◁⋎o_thm = save_pop_thm "Image⋎o_◁⋎o_thm";
=IGN
new_conjecture(["SupIm⋎u_◁⋎u_thm"], ⌜∀γ f⦁ SupIm⋎u (γ ◁⋎u f, γ) = SupIm⋎u (f, γ)⌝);
=IGN
set_goal([], ⌜∀γ f⦁ SupIm⋎u (γ ◁⋎u f, γ) = SupIm⋎u (f, γ)⌝);
a (REPEAT strip_tac THEN rewrite_tac [SupIm⋎u_def, Image⋎u_◁⋎u_thm]);
val SupIm⋎u_◁⋎u_thm = save_pop_thm "SupIm⋎u_◁⋎u_thm";

new_conjecture(["SSupIm⋎o_◁⋎o_thm"], ⌜∀γ f⦁ SSupIm⋎o (γ ◁⋎o f, γ) = SSupIm⋎o (f, γ)⌝);

set_goal([], ⌜∀γ f⦁ SSupIm⋎o (γ ◁⋎o f, γ) = SSupIm⋎o (f, γ)⌝);
a (REPEAT strip_tac THEN rewrite_tac [SSupIm⋎u_def, Image⋎u_◁⋎u_thm]);
val SSupIm⋎o_◁⋎o_thm = save_pop_thm "SSupIm⋎o_◁⋎o_thm";

=IGN
val ord_rec_thm = save_thm("ord_rec_thm",
	rewrite_rule [lt⋎o_well_founded_thm2] (∀_elim ⌜$<⋎o: 'a → 'a → BOOL⌝ tf_rec_thm2));

set_goal([], ⌜∀ af⦁ ∃ f:'a → 'a⦁ ∀ x⦁ f x = af (x ◁⋎o f) x⌝);
a (rewrite_tac[◁⋎o_def, ord_rec_thm]);
val ord_rec_thm2 = save_pop_thm "ord_rec_thm2";

set_goal ([], ⌜∀ af⦁ ∃ f:'a → 'a⦁ ∀ x⦁ f (CombI x) = af (x ◁⋎o f) x⌝);
a (strip_tac);
a (strip_asm_tac (∀_elim ⌜af⌝ ord_rec_thm2));
a (∃_tac ⌜f⌝ THEN asm_rewrite_tac [get_spec ⌜CombI⌝]);
val ord_rec_thm3 = save_pop_thm "ord_rec_thm3";

=IGN
set_flag ("pp_show_HOL_types", true);
set_flag ("pp_show_HOL_types", false);

set_goal([], ⌜∀af⦁ (λ(f:'a → 'a) (x:'a)⦁ af (Image⋎o (f, x)) x) respects $<⋎o⌝);
a (rewrite_tac [get_spec ⌜$respects⌝] THEN REPEAT strip_tac);
a (LEMMA_T ⌜Image⋎o (g, x) = Image⋎o (h, x)⌝ rewrite_thm_tac);
a (rewrite_tac[sets_ext_clauses, Image⋎o_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac);
a (lemma_tac ⌜tc $<⋎o η x⌝ THEN1 fc_tac [tc_incr_thm]);
a (ASM_FC_T (rewrite_tac o list_map_eq_sym_rule) []);
(* *** Goal "2" *** *)
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac);
a (lemma_tac ⌜tc $<⋎o η x⌝ THEN1 fc_tac [tc_incr_thm]);
a (ASM_FC_T rewrite_tac []);
val Image⋎o_respects_lt⋎o_thm = save_pop_thm "Image⋎o_respects_lt⋎o_thm";

set_goal([], ⌜∀ af:'a ℙ → 'a → 'a⦁ ∃ f⦁ ∀x:'a⦁ f (CombI x) = af (Image⋎o (f, x)) x⌝);
a (REPEAT strip_tac THEN_TRY rewrite_tac[get_spec ⌜CombI⌝]);
a (∃_tac ⌜fix (λf x⦁ af (Image⋎o (f, x)) x)⌝);
a (asm_tac Image⋎o_respects_lt⋎o_thm);
a (asm_tac lt⋎o_well_founded_thm3);
a (spec_nth_asm_tac 2 ⌜af⌝);
a (all_fc_tac [get_spec ⌜fix⌝]);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac[ext_thm]);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac []);
val Image⋎o_recursion_thm = save_pop_thm "Image⋎o_recursion_thm";
=TEX
}%ignore

=GFT
⦏ord_rec⋎u_thm3⦎ =	⊢ ∀ af⦁ ∃ f⦁ ∀ x⦁ f (I⋎u x) = af (x ◁⋎u f) x
=TEX

\ignore{
=IGN
val ord_rec⋎u_thm = save_thm("ord_rec⋎u_thm",
	rewrite_rule [rewrite_rule [get_spec ⌜UWellFounded ⌝] lt⋎u_well_founded_thm] (∀_elim ⌜$<⋎u: 'a ℙ → 'a ℙ → BOOL⌝ tf_rec_thm2));

set_goal([], ⌜∀ af⦁ ∃ f:'a ℙ → 'a⦁ ∀ x⦁ f x = af (x ◁⋎u f) x⌝);
a (rewrite_tac[◁⋎u_def, ord_rec⋎u_thm]);
val ord_rec⋎u_thm2 = save_pop_thm "ord_rec⋎u_thm2";

set_goal ([], ⌜∀ af⦁ ∃ f:'a ℙ → 'a⦁ ∀ x⦁ f (I⋎u x) = af (x ◁⋎u f) x⌝);
a (strip_tac);
a (strip_asm_tac (∀_elim ⌜af⌝ ord_rec⋎u_thm2));
a (∃_tac ⌜f⌝ THEN asm_rewrite_tac [get_spec ⌜I⋎u⌝]);
val ord_rec⋎u_thm3 = save_pop_thm "ord_rec⋎u_thm3";

force_new_pc "'ordinals-rec";
add_∃_cd_thms [ord_rec_thm3] "'ordinals-rec";
add_∃_cd_thms [ord_rec⋎u_thm3] "'ordinals-rec";
=IGN
add_∃_cd_thms [Image⋎o_recursion_thm] "'ordinals-rec";
=TEX
}%ignore

=GFT
	?⊢  ∀ f s⦁ LimitPenIm⋎u (s ◁⋎u f) s = LimitPenIm⋎u f s
=TEX

\ignore{
=SML
set_goal([], ⌜∀ f s⦁ LimitPenIm⋎u (s ◁⋎u f) s = LimitPenIm⋎u f s⌝);
=TEX
}%ignore

\subsection{Well-Orderings}

It is also possible to represent both types of enumeration by the well-ordering (relationship) which they embody, and the distinction between total and partial enumerations does not then complicate the type since the distinction is simply whether the field of the relation is the whole type.
Its not at all clear that this is not a better way to go for most of the hard work, morphing over to an enumeration for the projection function only after the fixed point has been established.
I'll do this section as if it were a fresh start on the problem (preliminaries to support for inductive data types).





\subsection(Enumerating Well-Orderings)

In defining a projection function for an inductive datatype, the enumeration proceeds by rank, and the result is the product of enumerations of the values at each rank.
The product relation is an easily defined well-ordering and therefore should be converted into an isomorphic enumeration.
For this purpose we define here the function which enumerates the field of a well-ordereding.
Note that the domain of the enumeration may be but need not be the the same type as the field of the well-ordering, in either case interpreted as a strict initial ordinal.
Because this is an initial ordinal, it is not certain that it will suffice to capture an order over the same type which is not initial.

\ignore{
 ⓈHOLCONST
│ $⦏wo_enum⦎: ('a → ('a → BOOL)) → ('b  → 'a)
 ├───────────
│ ∀r⦁ wo_enum r x = SSup⋎o(ran (x ◁u wo_enum))
 ■
}%ignore

\section{DEFINING INACCESSIBILITY}

\ignore{
=SML
open_theory "ordinals";
force_new_theory "⦏inaccess⦎";
force_new_pc "⦏'inaccess⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'inaccess";
set_merge_pcs ["rbjmisc","'ordinals", "'inaccess"];
=TEX
}%ignore

When we come to define functions over ordinals we become dependent on closure properties of the ordinals.

To obtain convenient closure properties we constrain the theory to operate over types of sufficient cardinality and other properties.
We will also introduce a type constructor which creates types characterised by a strong axiom of infinity, with good closure properties, for example, closed under dependent function space construction, and having inacessible cardinality.

To do this we must first introduce some terminology.

The significance of this section to the purposes of this work is moot, since the strong axiom of infinity, which implicitly asserts the existence of inaccessible 'a ordinals, does not depend upon an explicit definition.

The purpose of this section is therefore as a kind of check on the formulation of that axiom.
This check could go as far as defining inaccessible and proving the equivalence of the given axiom with a formulation based on the defined concept.
However, to serve that pupose this material would have to come before the axiom, since in the context of that axiom we cannot distinguish between equivalence and entailment of the new formulation by the old.

Co-finality is usually a relation between increasing $β$ sequences (β a limit 'a ordinal) and some limit 'a ordinal $α$.
I don't yet have sequences, so its convenient to give a slightly broader definition.
Instead of increasing sequences I allow the image of any 'a ordinal under a function (which need not be increasing).
At this point I don't actually understand why an increasing sequence is asked for in the usual definition.

Such an image is ``cofinal'' in an 'a ordinal if:

\begin{itemize}
\item the image falls entirely below the 'a ordinal
\item the supremum of the image is that 'a ordinal
\end{itemize}

=SML
declare_infix(400, "CofinalIn⋎o");
=TEX

ⓈHOLCONST
│ $⦏CofinalIn⋎o⦎: (('a → 'a) × 'a) → 'a → BOOL
├───────────
│ ∀x γ⦁ x CofinalIn⋎o γ ⇔ Image⋎o x ⊆ X⋎o γ ∧ γ ∈ SUb⋎o(Image⋎o x) ∧ SupIm⋎o x = γ 
■

ⓈHOLCONST
│ ⦏Cf⋎o⦎: 'a → 'a
├───────────
│ ∀β⦁ Cf⋎o β = ⋂⋎o {γ | ∃f⦁ (f, γ) CofinalIn⋎o β}
■

We can now define the notion of regularity, one of the defining properties of inaccessible cardinals.

ⓈHOLCONST
│ ⦏Regular⋎o⦎: 'a → BOOL
├───────────
│ ∀β⦁ Regular⋎o β ⇔ Cf⋎o β = β
■

ⓈHOLCONST
│ ⦏Singular⋎o⦎: 'a → BOOL
├───────────
│ ∀β⦁ Singular⋎o β ⇔ ¬ Regular⋎o β
■

As well as using this in the definition of inaccessibility we want to be able to state that the universe is regular (to get sufficiently generous recursion principles, analogous to global replacement).
The vocabulary above doesn't really help in stating this global principle, but it is simple enough to state directly.
We will come to that later.

To get inaccessibilty we need also to express the notion of a strong limit.

ⓈHOLCONST
│ ⦏Succ⋎o⦎: 'a → 'a
├───────────
│ ∀β⦁ Succ⋎o β = ⋂⋎o {γ | β <⋎o γ}
■

ⓈHOLCONST
│ ⦏Successor⋎o⦎: 'a → BOOL
├───────────
│ ∀β⦁ Successor⋎o β ⇔ ∃γ⦁ γ <⋎o β ∧ β = Succ⋎o γ
■

ⓈHOLCONST
│ ⦏Limit⋎o⦎: 'a → BOOL
├───────────
│ ∀β⦁ Limit⋎o β ⇔ 0⋎o <⋎o β ∧ ¬ Successor⋎o β
■

ⓈHOLCONST
│ ⦏ω⋎o⦎: 'a
├───────────
│ ω⋎o = ⋂⋎o {β | Limit⋎o β}
■

As well as asking for a universe with inaccessibles, it is desirable to have good closure properties for the universe.
Asserting that every ordinal is followed by an inaccessible does a lot of that, but does not entail global replacement, so I express the ordinal analogue of replacement as a property of classes of ordinals so that it can be asserted of the whole type of ordinals.

It is then possible to check the definitions by reasoning about the relationship between replacement and regularity.

ⓈHOLCONST
│ ⦏Rc⦎: 'a ℙ → BOOL
├───────────
│ ∀A⦁ Rc A ⇔ ∀β f⦁ β ∈ A
│      ∧ (∀ν:'a⦁ ν <⋎o β ⇒ f ν ∈ A)
│      ⇒ ∃ρ⦁ ρ ∈ A ∧ (∀ν⦁ ν <⋎o β ⇒ f ν <⋎o ρ)
■

=GFT
=TEX

\ignore{
=SML
val Succ⋎o_def = get_spec ⌜Succ⋎o⌝;
val Successor⋎o_def = get_spec ⌜Successor⋎o⌝;
val Limit⋎o_def = get_spec ⌜Limit⋎o⌝;
val ω⋎o_def = get_spec ⌜ω⋎o⌝;

=IGN
set_goal([], ⌜Limit⋎o ω⋎o ∧ ∀β⦁ Limit⋎o β ⇒ ω⋎o ≤⋎o β⌝);
a (rewrite_tac[ω⋎o_def]);

=TEX
}%ignore

ⓈHOLCONST
│ ⦏StrongLimit⋎o⦎: 'a → BOOL
├───────────
│ ∀β⦁ StrongLimit⋎o β ⇔ ∀γ⦁ γ <⋎o β ⇒ ℙ (X⋎o γ) <⋎s X⋎o β
■

ⓈHOLCONST
│ ⦏Inaccessible⋎o⦎: 'a → BOOL
├───────────
│ ∀β⦁ Inaccessible⋎o β ⇔
│       	     Regular⋎o β
│ 		     ∧ StrongLimit⋎o β
│ 		     ∧ ∃ η⦁ η <⋎o β ∧ Limit⋎o η
■

\ignore{
=SML
val Inaccessible⋎o_def = get_spec ⌜Inaccessible⋎o⌝;
val CofinalIn⋎o_def = get_spec ⌜$CofinalIn⋎o⌝;
val Cf⋎o_def = get_spec ⌜Cf⋎o⌝;
val Regular⋎o_def = get_spec ⌜Regular⋎o⌝;
val StrongLimit⋎o_def = get_spec ⌜StrongLimit⋎o⌝;
=IGN

set_goal([], strong_infinity2);
a (∀_tac);
a (strip_asm_tac (∀_elim ⌜β⌝ strong_infinity)
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
(* *** Goal "1" *** *)
a (strip_asm_tac (∀_elim ⌜β⌝ strong_infinity));
a (∃_tac ⌜γ⌝ THEN asm_rewrite_tac
	[Limit⋎o_def, CofinalIn⋎o_def, Cf⋎o_def,
	Regular⋎o_def, StrongLimit⋎o_def]);
a (REPEAT strip_tac THEN asm_fc_tac[]);

set_labelled_goal "2";
a (spec_nth_asm_tac 2 ⌜f⌝);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜ρ⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜ρ⌝ THEN asm_rewrite_tac[]);

=TEX
}%ignore

The basic idea is to state that every 'a ordinal is less than some (strongly) inaccessible 'a ordinal (also a cardinal), with a little tweak to give, in effect, global replacement  (or its analogue for a theory of 'a ordinals rather than sets).
Here local replacement is the requirement that each 'a ordinal is less than some regular cardinal, global replacement tells us that the universe is regular.
The other requirement is that this regular cardinal is a strong limit, i.e. closed under powerset.
 
To validate this principle I could first prove the principal in the set theory in t023, or alternatively in t041 since the 'a ordinals are further developed there.
That would gives greater confidence in its consistency.
That it is adequate can be testing in use, or by constructing a set theory from this type of 'a ordinals which satisifies the first principle.

However, without further validation I now proceed to establish that it can be used to justify a convenient recursion principle.

The first step in this is to define a couple of functions using our axiom of infinity.

The first is a function which, given an infinite 'a ordinal, will deliver the least inaccessible 'a ordinal greater than that 'a ordinal, given a finite 'a ordinal it returns $ω$.
I will call this $Lio$.

\ignore{
=IGN
set_goal(∃Lio:'a ordinal → 'a ordinal⦁
∀β⦁ let γ = Lio β in 
    β < γ
    ∧ ∀τ⦁ τ <⋎o γ ⇒ 
	   ℙ (X⋎o τ) <⋎s X⋎o γ
	∧ (∀f⦁ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o τ)
		⇒ (∃ρ⦁ ρ <⋎o γ ∧ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o ρ)))
=TEX


 ⓈHOLCONST
│ ⦏G⋎o⦎: 'a → 'a
 ├──────────
│ ∀β⦁ G⋎o β = ⋂⋎o {γ | β <⋎o γ ∧ ω⋎o <⋎o γ
    ∧ ∀τ⦁ τ <⋎o γ ⇒ 
	   ℙ (X⋎o τ) <⋎s X⋎o γ
	∧ (∀f⦁ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o τ)
		⇒ (∃ρ⦁ ρ <⋎o γ ∧ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o ρ)))}
 ■
}%ignore

=GFT
=TEX

\ignore{
 =SML
val G⋎o_def = get_spec ⌜G⋎o⌝;

list_∀_elim [⌜{γ | β <⋎o γ ∧ ω⋎o <⋎o γ
    ∧ ∀τ⦁ τ <⋎o γ ⇒ 
	   ℙ (X⋎o τ) <⋎s X⋎o γ
	∧ (∀f⦁ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o τ)
		⇒ (∃ρ⦁ ρ <⋎o γ ∧ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o ρ)))}⌝] ⋂⋎o_def;

=IGN
set_goal([], ⌜∀β⦁ 

⌝);
=TEX
}%ignore

\section{INDUCTIVE DATA TYPES}

\ignore{
=SML
force_new_theory "⦏indatat⦎";
force_new_pc "⦏'indatat⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'indatat";
set_merge_pcs ["rbjmisc","'ordinals", "'indatat"];
=TEX
}%ignore

This section provides machinery to support two kinds of inductive data type construction.

The general pattern is to use an ordinal type as the representation and to give an inductive definition of the function over the ordinals which is the generalised projection function, i.e. the inverse of the generalised constructor which is to be used for making objects of the new type.
The generalised projection and constructor operate with disjoint unions each partition correponding to one of the intended new data types.
These are then used to partition the ordinals to give representation sets for each if the new types.

There are two quite distinct cases here, according to whether the constructions eventually yield a set closed under the constructions.
The representations are then a subset of the rekevant ordinals, and the closure properties are then amount the theorems characterising the new types,
In the second case, which occurs if the constructors invariably raise the cardinality (perhaps because invoving the power set or function space constructors) and the iteration continues until the ordinals are exhausted without realising closure.
These are what I call foundational ontologies.

The development of this machinery is driven by two simple examples included in this document just for that purpose.
For the first case the example is the syntax of HOL terms.
For the second, the simplest construction is to use the power set to create a set theory.

\subsection{The Projection Iterator}

We required a function to be provided which given a set of representatives (in fact an initial segment, or the whole, of some ordinal type) identify the things which can be constructed from them.
This is done by exhibiting the constructions which yield the particular representative, so the map from a representative to its manner of construction is the projection from the required abstract data types.

An inductive data type is generated from the empty set by iterating certain defined methods of constructing new entities of the inductively defined types from the entities already constructed (getting off the ground by the use of some constructors which require no existing members of those types).
This is defined as a map which, given some existing set of representatives of the types, delivers the ways in which new values can be constructed, i.e. the constructors to be used and the values to which those constructors are to be applied.
These are the things which one would expect to obtain from the inverses of the constructor functions, which are called projections.

The iteration of this process of construction therefore cumulatively defines a compound projection function (there would eventually be a distinct projection corresponding to each of the ways in which values of the inductive types can be constructed, but at this stage these are all be bundled into one projection which yields a disjoint union of the parameter types required by the various constructor functions, 

At each step in this process the set of representatives grows larger until perhaps there are no new values of the types to be created, and we may say that a fixed point has been reached over which the constructors are closed.

This does not always happen, in some cases, notably where the constructors always increase the cardinality of the representatives (e.g. when constructing the cumulative heirarchy in well-founded set theories) and in that case the process terminates when the type of representatives is exhausted and the result is still not closed under the constructions.

This composite projection function is a map from a type of ordinals, and is constructed by sucessively allocating to the ordinals constructions, so that the projection function is in effect an enumeration of the ways in which values of the new types can be constructed.
So we are here concerned with how such enumerations can be defined, and of course with inductive definitions of such enumerations.

This makes use of the type abnreviated as ('a,'b)PEN (for partial enumeration), in which the first variable is the type of ordinals which are to be the representatives of the new values, and the type 'b is the disjoint union of the types of the parameters to the construction functions (which would normally be more complex types in which the type 'a appears whenever a value of the new types is used in constructing a more complex value of the new types.

I therefore expect that the designer of the new types will supply a function which when given a set of supposed representatives will return a set of ways in which values can be constructed from those representatives.
Its not necessary to filter out duplicates, that will be done later.
I define below a function which given that function will deliver the resulting enumeration of all the values in the inductive data type.

???????

We then apply to that a function which augments the set of represenatatives to include those new entities immediately constructible from the originals.
This is done by filtering out duplicates, well-ordering the result, and appending this to the original projection.
The projection is represented by a function over the ordinals together with a specific ordinal which determines the set of representatives so far assigned values.

This yields is a sanitised generalised constructor, and we then need a function which will iterate the augmentation until a fixed point is reached or the ordinals are exhausted.

So this is what one needs to provide for a new type construction:
Usually the 'a parameter will be ONE, but if there are type variables in 'b  then they will have to be passed through in the value for 'a to ensure that the ordinals used for enumeration (and representation) are sufficiently numerous.

In defining such an enumeration, we need to be able to add some new set of 'b values on to the end of the enuneration.

Note the use of ⌜Choose\{\}⌝ to fix the values of the function beyond the intended range of the enumeration, with the purpose of ensuring uniqueness of representation.
The definition of limit for these entities depends on this feature.

To define the effect of one new generation of constructions, we first have to apply the defining function to the range of the existing enumeration, giving a new set of projection values to be added to the enumeration.
Then we remove anything already in the range so that the projection function remains injective.

To add this new set I first define separately the adding of a single new value, and then adding a set in two cases according to whether there is a greatest element in the set.

Adding a single element first:

ⓈHOLCONST
│ $⦏extprf⦎: ('a, 'b) PEN → 'b → ('a, 'b) PEN
├───────────
│ ∀f x w⦁ extprf (x, f) w  = (Succ⋎o x,
│       λp⦁ (if p = x then w
│	    else if p <⋎o x then f p
│	    else (Choose{})))
■

\ignore{
=IGN
stop;
set_goal([], ⌜∃ sextprf: ('a, 'b) POTEN → ('b) ℙ → ('a, 'b) POTEN⦁
	 ∀f x w⦁ sextprf (x, f) w  =
     	 if (w = {} ∨ IsL x)
	 then (x,f)
	 else LimitPen⋎q{v | ∃u⦁
	 	    u ∈ w ∧ v = sextprf (x,f) (w ∩ X⋎o u)}⌝
);

a (lemma_tac ⌜∃ sextprf: ('a, 'b) POTEN → ('b) ℙ → ('a, 'b) POTEN⦁
  ∀f x w⦁ sextprf (x, f) (I⋎u w)  =
     	 if (w = {} ∨ IsL x)
	 then (x,f)
	 else LimitPen⋎q{v | ∃u⦁
	 	    u ∈ w ∧ v = (w ◁⋎u (sextprf (x,f))) (w ∩ X⋎o u)}⌝);


a (basic_prove_∃_tac);

a (prove_∃_tac);

a (lemma_tac ⌜∃ f⦁ ∀ x⦁ f (CombI x) = λg y⦁ if x < (x ◁⋎o f) x⌝;



ord_rec_thm3  = ⊢ ∀ af⦁ ∃ f⦁ ∀ x⦁ f (CombI x) = af (x ◁⋎o f) x: THM

evaluate_∃_cd_thm ord_rec_thm3 ;
	(accept_tac o (pure_rewrite_rule [get_spec ⌜CombI⌝, SupIm⋎o_◁⋎o_thm]))
	THEN1 basic_prove_∃_tac);
=TEX
}%ignore

To achieve the recursion here we have to form the limit of directed collections of enumerations using $⌜FunLimit⋎o⌝$ and $⌜OrdLimit⋎o⌝$.

ⓈHOLCONST
│ $⦏sextprf⦎: ('a, 'b) POTEN → ('b) ℙ → ('a, 'b) POTEN
├───────────
│ ∀f x w⦁ sextprf (x, f) w  =
     	 if w = {} ∨ IsL x
	 then (x,f)
	 else LimitPen⋎q{v | ∃ u⦁
	 	    u ∈ w ∧ v = sextprf (x,f) (w ∩ X⋎o u)}
■	      

=IGN
declare_type_abbrev("PRI", ["'a", "'b"], ⓣ('a, 'b)PEN → 'b ℙ⌝);
=TEX
\ignore{
=SML
set_flag ("pp_show_HOL_types", false);
=TEX
}%ignore


\section{INDUCTIVE DATA TYPES (II)}

\ignore{
=SML
open_theory "ordinals";
force_new_theory "⦏indatat2⦎";
force_new_pc "⦏'indatat2⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'indatat2";
set_merge_pcs ["rbjmisc","'ordinals", "'indatat2"];
=TEX
}%ignore

This is a second approach to the inductive datatype, "inspired" by the perception that the first is too complicated.

I have at this point only the most slender ideas about how that should be done.

They are:

\begin{itemize}
\item More should be done in the theory of sequences to support the required constructon.
\item There should be a separate enumeration for each type in mutually defined inductive datatypes, rather than a single enumeration from which separate types will ultimately be defined (though there is no reason why they should not all be the same ordinal type). 
\end{itemize}

\appendix

\section{PROOFS IN PROGRESS}

=GFT
GOAL*1 ⌜∀α f⦁ Image⋎u (α ◁⋎u f, α) = Image⋎u (f, α)⌝
GOAL*2 ⌜∀α β⦁ α <⋎u β ⇒ α ∩ β <⋎u β⌝
GOAL*3 ⌜⌝
GOAL*4 ⌜⌝
=TEX

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj2,fmu}
} %\raggedright

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{ordinals.th}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{indatat.th}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{inaccess.th}
}%\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
