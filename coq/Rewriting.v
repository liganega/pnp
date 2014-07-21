(** remove printing ~ *)
(** printing ~ %\textasciitilde% *)
(** printing R $R$ *)
(** printing done %\texttt{\emph{done}}% *)
(** printing congr %\texttt{\emph{congr}}% *)
(** printing of %\texttt{\emph{of}}% *)
(** printing suff %\texttt{\emph{suff}}% *)


(** %
\chapter{Equality and Rewriting Principles}
\label{ch:eqrew}
%

In the previous chapter we have seen how main connectives from
Propositional Logic. However, the mathematical reasoning by means of
propositional logic only is still quite limited. In particular, by
this moment we are still unable to state what does it mean for two
objects to be _equal_. In this chapter we are going to see how
equality can be implemented in Coq. Moreover, the statement "_x_ is
equal to _y_" automatically gives us a way to replace _y_ by _x_ and
vice versa in the process of reasoning, therefore implementing a
discipline of _rewriting_---one of the key ingredients of the
mathematical proof.%\footnote{The reader could have, probably, heard
how mathematics sometimes is referred to as a "science of
rewritings".}% Later in the chapter, we will see how rewriting by
equality is just a particular case of a general proof pattern, which
allows one to define arbitrary _rewriting rules_ by exploiting Coq's
mechanism of _indexed type families_.

*)

(* begin hide *)
Require Import ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* end hide *)

(** * Propositional equality in Coq

Let us begin by exploring the definition of the equality predicate "[_
= _]".

*)

Locate "_ = _".

(**
[[
"x = y" := eq x y    : type_scope
]]
*)

Print eq.

(**
[[
Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : eq x x
]]

As we can see, the equality is just yet another inductive predicate,
similar to the logical connectives we've seen in
%Chapter~\ref{ch:logic}%. However, there are differences, which are of
importance. First, equality as a predicate is _parametrized_
%\index{datatype parameters}% over two arguments: a [Type] [A] of an
unspecified universe (so, it can be [Set], [Prop] or any of higher
universes, but not prop) and an element [x] of type [A]. There is
nothing particularly new here: we have seen parametrized inductive
predicates before, for instance, conjunction and disjunction in
%Section~\ref{sec:conjdisj}%. The novel part of this definition is
what comes after the semicolon trailing the parameter list. Unlike all
previously seen logical connectives, the equality predicate has type
[A -> Prop] in contrast to just [Prop]. In the Coq terminology, it
means that [eq] is not just inductively-defined datatype, but is an
_indexed type family_.%\index{indexed type families}% In this
particular case, it is indexed %\index{datatype indices}% by elements
of type [A], which appears at the left of the arrow.

%\index{parameters|see {datatype parameters}}%
%\index{indices|see {datatype indices}}%
%\index{GADT|see {generalized algebraic datatypes}}%


%\index{generalized algebraic datatypes}%It is common to think of
indexed type families in Coq as of _generalized algebraic datatypes_
(GADTs), familiar from Haskell%~\cite{PeytonJones-al:ICFP06}% and
allowing one to refine the process pattern matching basing on the type
index of the scrutinee. However, another analogy turns out to be much
more useful in the Coq setting: indexed type families in fact allow
one to encode _rewriting principles_. To understand, what the indexed
datatype definition has to do with rewriting, let us take a close look
at the definition of [eq]. The type of its only constructor [eq_refl]
is a bit misleading, as it looks like it is applied to two arguments:
[x] and ... [x]. To disambiguate it, we shall put some parentheses,
so, it fact, it should read as

[[
Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : (eq x) x
]]

That is, the constructor [eq_refl] delivers an element of type [eq],
whose _parameter_ is some [x] (and [eq] is directly applied to it),
and its _index_ (which comes second) is constrained to be [x] as
well. That is, case-analysing on an instance of [eq x y] in the
process of the proof construction will inevitably lead the side
condition implying that [x] and [y] actually correspond to the _same
object_. Coq will take advantage of this fact immediately, by
substituting all occurrences of [y] in the subsequent goal with [x].
Let us see how it works in practice.

** Case analysis on an equality witness

To demonstrate the actual proofs on the case analysis by equality, we
will have to perform an awkward twist: define _our own_ equality
predicate. 

*)

Set Implicit Arguments.
Inductive my_eq (A : Type) (x : A) : A -> Prop :=  my_eq_refl : my_eq x x.
Notation "x === y" := (my_eq x y) (at level 70).

(** 

As we can see, this definition literally repeats the Coq's standard
definition of propositional equality. The reason for the code
duplication is that SSReflect provides a specific treatment of Coq's
standard equality predicate, so the case-analysis on its instances is
completely superseded by the powerful [rewrite] tactics, which we will
see in %Section~\ref{sec:rewriting}% of this chapter. Alas, this
special treatment also leads to a non-standard behavior of
case-analysis on equality. This is why, for didactical purposes we
will have to stick with or own home-brewed definition until the end of
this section.

Let us now prove some interesting properties of the freshly-defined
equalities. We start with symmetry of [===] by formulating the following
lemma:%\footnote{The Coq's command \texttt{Lemma} is identical to
\texttt{Theorem}.\ccom{Lemma}}%

*)

Lemma my_eq_sym A (x y: A) : x === y -> y === x.

(**

First, we analyse on the top assumption of the goal, [x === y].

*)

case.

(** 

This leads to the goal, being switched from [y === x] to [x === y], as
all occurrences of [y] are now replaced by [x], exactly as advertised.
We can now finish the proof by applying the constructor ([apply:
my_refl_eq]) or simply by [done], which is powerful enough to figure
out what to apply.

*)

done.
Qed.

(**

Our next exercise will be to show that the predicate we have just
defined implies Leibniz equality. The proof is accomplished in one
line by first moving the assumption [P x] to the top and then
case-analysing on the equality, which leads to the automatic
replacements of [y] by [x].

*)

Lemma my_eq_Leibniz A (x y: A) (P: A -> Prop) : P x -> x === y -> P y. 
Proof. by move=>H; case. Qed.

(**

** Implementing discrimination

Another important application of the equality predicate family and
similar ones %\index{discrimination}% are _proofs by discrimination_,
in which the contradiction is reached (i.e., the falsehood is derived)
our of the fact that two clearly non-equal elements are assumed to be
equal. The next lemma demonstrates the essens of the proof by
discrimination using the [my_eq] predicate.

*)

Lemma disaster : 2 === 1 -> False.
Proof.
move=> H.

(**

As it is already hinted by the name of the method, the key insight in
the proofs by discrimination is to construct a function that can
distinguish between values of the type with an implicit _definitional
equality_,%\index{definitional equality}% which relates two values if
they have identical structure.%\footnote{Naturally, it is not trivial
to establish definitional equality on \emph{any} values, as the values
might be of an infinite nature. For instance, establishing the
equality of two functions would require checking their results on all
elements of the common domain, which might be infinite. in this
respect, the propositional equality acts like it ``compares the
references'', whereas definitional equality ``compares the structure''
of two elements.}% In particular, natural numbers can be compared
against each other by means of direct pattern matching, which is
decidable for them, thanks to the inductive definition. Using this
insight we define a local "discriminating" function [D] using the
SSReflect's enhanced [pose] %\ssrt{pose}% tactic:

 *)

pose D x := if x is 2 then False else True.

(**

Now, proving [D 1] is [True] can be accomplished by simple executing
[D] with appropriate arguments (recall that [D] is an
always-terminating just a function, whose result is a computable
value). That SSReflect's tactic [have]%\ssrt{have}% allows to declare
the local fact, which can be then proving on-site by simple
computation (which is performed via [by []]).

*)

have D1: D 1 by [].

(**

Next we "push" [D1] and [H] back to the goal (using the [:] tactical),
and case-analyse on the top assumption [H]. Notice that the semantics
of [:] %\ssrtl{:}% is such that it first performs a series of
"pushings" and then runs the tactic on the left of itself (i.e.,
[case]).

 *)

case: H D1. 

(**

Now, we got what we have needed: the proof of the falsehood! Thanks to
the equality-provided substitution, [D 1] turned into [D 2], and the
only thing that remains now is to _evaluate_ it.

*)

move=>/=.

(**

The tactical %\ssrtl{/=}%[/=], coming after [=>] runs all possible
simplifications on the result obtained by the tactics, preceding [=>],
finishing the proof.

*)

done.
Qed.

(**

Let us provide a bit more explanation how did it happen that we
managed to derive the falsehood in the process of the proof. The
discrimination function [D] is a function from [nat] to [Prop], and,
indeed it can return [True] and [False], so it contains no
contradictions by itself. We also managed to prove easily a trivial
proposition [D 1], which is just [True], so it's derivable. The true
twist happened when we managed to turn the assumption [D 1] (which was
[True]) to [D 2] (which is [False]). This was only possible because of
the assumed equality [2 === 1], which contained the "falsehood" from
the very beginning and forced Coq to substitute the occurrence of [1]
in the goal by [2], so the discrimination function in the assumption
finished the job.

%\begin{exercise}%
Let us change the statement of a previous lemma for a little bit:

*)

Lemma disaster2 : 1 === 2 -> False.

(**

Now, try to prove it using the same scheme. What goes wrong and how to
fix it?

%\end{exercise}%

*)

(* begin hide *)
Proof.
by move=>H; move/disaster: (my_eq_sym H).
Qed.
(* end hide *)

(** 

** Reasoning with Coq's standard equality

Now we know what drives the reasoning by equality and discrimination,
so let us forget about the home-brewed predicate [my_eq] and use the
standard equality instead. Happily, the discrimination pattern we used
to implement "by hand" now is handled by Coq/SSReflect automatically,
so the trivially false equalities deliver the proofs right away by
simply typing [done]. 

*)

Lemma disaster3: 2 = 1 -> False.
Proof. done. Qed.

(** 

Moreover, the case-analysing on the standard equality now comes in the
form of the powerful [rewrite] tactics, which takes the reasoning to
the whole new level and is a subject of the next section.

* Proofs by rewriting %\label{sec:rewriting}%

The vast majority of the steps when constructing real-life proofs in
Coq are _rewriting_ step. The general flow of the interactive
(considered in more detail in %Chapter~\ref{ch:ssrstyle}%) is
typically targeted on formulating and proving small auxiliary
hypotheses about equalities in the forward-style reasoning and then
exploiting the derived equalities by means of rewriting in the goal
and, occasionally, other assumptions in the context. All rewriting
machinery is handled by SSReflect's enhanced [rewrite]%\ssrt{rewrite}%
tactics, and in this section we focus on its particular uses.

** Unfolding definitions and on-site rewritings

One of the common uses of the [rewrite] tactic is to fold/unfold
transparent definitions. In general, Coq is capable to perform the
unfoldings itself, whenever it's required. Nevertheless, manual
unfolding of a definition might help to understand the details of the
implementation, as demonstrated by the following example.

*)

Definition double A (f: A -> A) (x: A) := f (f x).

Lemma double2 A (x: A) f t: 
  t = double f x -> double f t = nat_iter 4 f x.
Proof.

(**

The first thing to do in this proof is to get read of the auxiliary
variable [t], as it does not occur in any of the assumptions, but just
in the subsequent goal. This can be done using the following sequence
of tactics that first moves the equality assumption to the top and
then rewrites by it in the goal.

*)

move=>Et; rewrite Et.

(**

Even though the remaining goal is simple enough to be completed by
[done], let us unfold both definition to make sure that the two terms
are indeed equal structurally. Such unfoldings can be _chained_, just
as any other rewritings.

 *)

rewrite /double /nat_iter.
done.

(**

An alternative way to prove the same statement would be to use the
<< -> >> %\ssrtl{->}% tactical, which is usually combined with [move] or
[case], but instead of moving the assumption to the top, it makes sure
that the assumption is an equality and rewrites by it.

 *)

Restart.
by move=>->; rewrite /double.
Qed.

(** 

Notice that the tactical has a companion one << <- >>, which performs
the rewriting by an equality assumption from right to left, in
contrast to << -> >>, which rewrites left to right.

The reverse operation to folding is done by using [rewrite -/...]
instead of [rewrite /...]%\footnote{As the reader will notice soon, it
is a general pattern with SSReflect's rewriting to prefix a
\texttt{rewrite} argument with \texttt{-}, if the \emph{reverse}
rewriting operation should be performed.}%

** Proofs by congruence and rewritings by lemmas

*)

Require Import ssrnat.
Definition f x y :=  x + y.

Goal forall x y, x + y + (y + x) = f y x + f y x.
Proof. 
move=> x y.

(** 

First, let us unfold only all occurrences of [f] in the goal.

*)

rewrite /f.

(**

We can now reduce the goal by appealing to SSReflect's [congr]
tactics, which takes advantage of the fact that equality implies
Leibniz' equality, in particular, with respect to the addition taken
as a function, so the external addition of equal elements can be
"stripped off".

*)

congr (_ + _).

(** 

Now, the only thing left to prove is that the addition is commutative,
so at this point we will just make use of SSReflect's library lemma
for integer addition.

*)

Check addnC.

(**
[[
addnC
     : ssrfun.commutative addn
]]

At this point such signature might seem a bit cryptic, but worry not:
this is just a way to express in a generic way that the addition over
natural numbers is commutative, which can be witnessed by checking the
definition of [ssrfun.commutative] predicate:

*)

Print ssrfun.commutative.

(** 
[[
ssrfun.commutative = 
fun (S T : Type) (op : S -> S -> T) => forall x y : S, op x y = op y x
     : forall S T : Type, (S -> S -> T) -> Prop
]]

As we can see, the definition of the [commutative] predicate ensures
the equality of the operation's result with its arguments, permuted,
hence [op x y = op y x]. The type of the lemma [addnC] therefore
refines [op] to be "[_ + _]", so, after specializing the definition
appropriately, the type of [addnC] should be read as:

[[
addnC
     : forall n m: nat, n + m = m + n
]]

Now, we can take advantage of this equality and rewrite by it a part
of the goal. Notice that Coq will figure out how the
universally-quantified variables should be instantiated (i.e., with
[y] and [x], respectively):

*)

by rewrite [y + _]addnC.
Qed.

(** 

The _r-pattern_ %\index{r-pattern}% (redex pattern) [[y + _]],
preceding the lemma to be used for rewriting, specifies, which
subexpression of the goal should be a subject of rewriting. In this
particular case, it does not matter that much, since any single
rewriting by commutativity in any of the sums, ont the left or on the
right, would make the proof go through. However, in a more
sophisticated goal it makes sense to specify explicitly, what should
be rewritten:

*)

Goal forall x y z, (x + (y + z)) = (z + y + x).
Proof.
by move=>x y z; rewrite [y + _]addnC; rewrite [z + _ + _]addnC.
Qed.

(** 

Proofs of "obvious" equalities that hold modulo, e.g., commutativity
and subjectivity, usually require several rewriting to be established,
which might be tedious.  There are ways to automate such proofs by
means of overloaded lemmas via _canonical structures_. These
techniques, hinted briefly in %Chapter~\ref{ch:depstruct}% are mostly
outside of the scope of this notes, so we address the reader to a
number of papers, presenting the state of the art in this
direction%~\cite{Gontier-al:ICFP11,Mahboubi-Tassi:ITP13}%.

** Naming in subgoals and conditional rewritings

When working with multiple cases, it is possible to "chain" the
executing of several tactics. Then, in the case of a script [tac1;
tac2], if the goal is replaced by several after applying [tac1], then
[tac2] will be applied to _all_ subgoals, generated by [tac1]. For
example, let us consider a proof of the following lemma from the
standrad [ssrnat] module:

*)

Lemma addnCA: forall m n p, m + (n + p) = n + (m + p).
Proof.
move=>m n. 

(** 

[[
  m : nat
  n : nat
  ============================
   forall p : nat, m + (n + p) = n + (m + p)
]]

The proof will proceed by induction on [m]. We have already seen the
use of the [case] tactics, which just performs the case
analysis. Another SSReflect tactic [elim] %\ssrt{elim}% generalizes
[case] by applying the default induction principle ([nat_ind] in this
case) with the respect to the remaining goal (that is, the predicate
[[forall p : nat, m + (n + p) = n + (m + p)]]) is to be proven by
induction.  The following sequence of tactics proceeds by induction on
[m] with the default induction principle. It also names some of the
generated assumptions. In particular, the following steps are
performed:

- [m] is pushed as a top assumption of the goal
- [elim] is run, which leads to generation of the two goals.

  -- The first goal is of the shape
[[
forall p : nat, 0 + (n + p) = n + (0 + p)
]]

  -- The second goal has the shape
[[
forall n0 : nat,
 (forall p : nat, n0 + (n + p) = n + (n0 + p)) ->
 forall p : nat, n0.+1 + (n + p) = n + (n0.+1 + p)
]]

- The subsequent structured naming [=> [|m Hm] p] names zero assumptions
  in the first goal and the two top assumptions [m] and [Hm] in the
  second goal. It then next names the assumption [p] in _both_ goals
  and moves it to the top.

*)

elim: m=>[ | m Hm ] p. 

(** 

The first goal can now be proved by multiple rewriting via the lemma
[add0n], stating that [0] is the left unit with respect to the
addition:

*)

by rewrite !add0n.

(**

The second goal can be proved by a series of rewritings using the fact
about the [(_ + 1)] function:

 *)


by rewrite !addSnnS -addnS.

(**

The conclusion of the [addnS] lemma is rewritten right-to-left.

The whole proof could be, however, accomplished in one line using the
_conditional_ rewritings. The intuitions is to _chain_ the rewritings
in the goals, generated by [elim] in a way that the unsuccessful
rewriting would not fail the whole proof construction, as they are
irrelevant for some goals anyway. This is how it can be done:

 *)

Restart.
by move=>m n; elim: m=>[ | m Hm ] p; rewrite ?add0n ?addSnnS -?addnS.
Qed.

(** 

Notice that the conditional rewritings (e.g., [?addSnnS]) are
performed as many times as they can be.

** Selective occurrence rewritings

Sometimes, instead of providing an r-pattern to specialize the
rewriting, it is more convenient to specify, which particular
syntactic occurrences%\index{occurrence switch}% in the goal term
should be rewritten. This is demonstrated by the following alternative
proof of commutativity of addition from the lemma [addnCA], which we
have proved before:

*)

Lemma addnC: forall m n, m + n = n + m.
Proof.
by move=> m n; rewrite -{1}[n]addn0 addnCA addn0. Qed.

(** 

The first rewriting with [addn0] "adds" [0] to the first occurrence of
[addn0], so the left-hand side of the equality becomes [m + (n +
0)]. The next rewriting employs the lemma [addnCA], so we get [n + (m
+ 0) = n + m] as the goal, and the last one "removes" zero, so the
result trivially follows.

We conclude this section by noticing that the same rewriting machinery
is applicable not only to the goal, but also to hypotheses in the
assumption context using the [rewrite H1 in H2] syntax (where [H] is
the rewriting hypothesis and [H2] is a hypothesis, where the rewriting
should happen). There are many more tricks that can be done with
rewritings, and we address the reader to %Chapter~7 of SSReflect
manual~\cite{Gontier-al:TR}%.

*)


(** * Encoding custom rewriting rules


 *)


(* * Axioms about equality

TODO: K and friends

 *)

