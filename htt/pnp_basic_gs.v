From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat ssrfun.

(** * Programming with dependent types *)

Fixpoint my_plus n m :=
  if n is n'.+1 then (my_plus n' m) .+1 else m.

(** Point of the following definition:
   - case: n'.+1:
     the type of (sum_of_zero n') depends on n',
     hence should be considered explicitely.
 *)
Fixpoint sum_no_zero n :=
  let P := (fun n => if n is 0 then unit else nat) in
  match n as n0 return P n0 with
  | 0     => tt
  | n'.+1 => match n' return P n' -> _ with
               | 0 => fun _ => 1
               | n'' .+1 => fun m' => my_plus m' (n'.+1)
             end (sum_no_zero n')
  end.

(** One might have defined the same function using [nat_rec]. *)
Definition sum_no_zero' n :=
  let P := (fun n => if n is 0 then unit else nat)
  in nat_rec P tt
             (fun (n':nat) (m:P n') =>
                match n' return P n' -> _ with
                | 0      => fun _ => 1
                | n''.+1 => fun m' =>  my_plus m' (n'.+1)
                end m)
             n.

(** * Enhanced with Ssreflect *)

(** ** [Search] Command *)

(** [Search] command looks for definitions of functions
    and propositions that have a string as a part of 
    their name.
 *)

Search "filt".

(** [Search] command can filter names by adding a requirement 
    that the type of the function should include as a subtype.
 *)

Search "filt" (_ -> list _).

Search _ ((?X -> ?Y) -> _ ?X -> _ ?Y).

(** [Search] command can even make use of types of the patterns *)

Search _ (_ * _ : nat).

Search _ (_ * _ : Type).

(** ** [Locate] Command *)

(** [Locate] command can help finding the definition of
    notations.
 *)

Locate "_ + _".

(** [Locate] command can help finding the definition
    in the source modules they defined  *)

Locate map.

(** [Locate] command can even locate tactics.  *)

Locate simpl.

Locate apply.

Locate done.

(** * Inducticve Datatypes *)

(** Ssreflect provides more concise form for defining inductive types. *)

Inductive my_prod (A B : Type) : Type :=
  my_pair of A & B.

Arguments my_pair [A B].

Notation "X ** Y" := (my_prod X Y) (at level 2).
Notation "( x ,, y )" := (my_pair x y).

(** The [level] part in the first notation definition is mandatory 
    for potentially left-recursive notations, which is the case here, 
    in order to set up parsing priorities with respect to other notations. 
    The notation [_ ** _] for [my_pair] is by default set to be 
    left-associative.
 *)

Check (1 ,, 3).

Check (nat ** unit ** nat).

(** * Sections and Modules *)

(** Sections are the simplest way to structure the programs in Coq. 
    Sections allow the programmer to limit the scope of modules imported 
    to the current file (each compiled .v file in the scope of the 
    interpreter is considered as a module), as well as to defined 
    locally-scoped variables. 

    Unlike Haskell or Java’s modules, sections in Coq are transparent.
    However, sections' variables become parameters of definitions 
    they happened to be used in.
 *)

(** Modules can contain locally-declared variables, sections and modules 
    (but not modules within sections!). However, the internals of a module
    are not implicitly exposed to the outside, instead they should be
    either referred to by qualified names or exported explicitly 
    by means of putting them into a submodule and via the command [Export].  
 *)


(** ** [Definition] vs. [Theorem] *)

(** The value bound by [Definition] is transparent: it can be executed 
    by means of unfolding and subsequent evaluation of its body. 
    In contrast, a proof term bound by means of [Theorem] is opaque, 
    which means that its body cannot be evaluated and serves only 
    one purpose: establish the fact that the corresponding type 
    is inhabited, and, therefore is true. 

    This distinction between definitions and theorems arises from the
    notion of proof irrelevance, which, informally, states that 
    (ideally) one shouldn't be able to distinguish between two proofs 
    of the same statement as long as they both are valid.  

    Then [Eval] command behaves differently depending on whether it is 
    about [Definition] or about [Theorem].
 *)

(** * Uses of Tactics *)

(** ** [exact:] tactic *)

Theorem true_is_true: True.
Proof. exact: I. Qed.

(** ** [apply:] tactic *)

Theorem one_eq_two: False -> 1 = 2.
Proof. apply: False_ind. Qed.

(** The tactic [apply:] supplied with an argument [False_ind], 
    tried to figure out whether our goal [False -> (1 = 2)] matches 
    any _head_ type of the theorem [False_ind].
    By _head type_ we mean a component of type 
    (in this case, [forall P : Prop, False -> P]), 
    which is a type by itself and possibly contains free variables.
    For instance, recalling that
    [->] is right-associative, head-types of [False_ind] would be [P],
    [False -> P] and [forall P : Prop, False -> P] itself.
 *)

(** [apply.] is a synonym for: 
    
    [intro top; first [refine top | refine (top _) |  refine (top _ _) 
    | ...]; clear top.]

    SSReflect's [apply] has a special behaviour on goals containing
    existential metavariables of sort [Prop].
 *)

From Coq Require Import Arith.

Theorem toto_1: forall y, 1 < y -> y < 2 ->
                          exists x : { n | n < 3 }, proj1_sig x > 0.
Proof.
  move=> y y_gt1 y_lt2.
  apply: (ex_intro _ (exist _ y _)).
  by apply: ltn_trans y_lt2 _ .
  by move=> y_lt3; apply: ltn_trans _ y_gt1.
Qed.


(** ** [case] tactic *)

Theorem one_eq_two': False -> 1 = 2.
Proof. case. Qed.

(** The tactic [case] makes Coq to perform the case analysis. 
    In particular, it _deconstructs_ the _top assumption_ of the goal. 
    The top assumption in the goal is such that it comes first 
    before any arrows, and in this case it is a value of type [False]. 
    Then, for all constructors of the type, whose value is being 
    case-analysed, the tactic [case] constructs _subgoals_ to be proved. 
 *)

(** Since the result of the proof is just some program, we can 
    the same theorem with an exact proof term.
 *)

Theorem one_eq_two'': False -> 1 = 2.
Proof. exact: (fun (f : False) => match f with end). Qed.

(** ** [move] tactic [=>] tactical *)

(*
Theorem imp_trans: forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  move: a.

 *)

(** * CoInduction *)

CoInductive phantom T (p : T) := Phantom.
Implicit Arguments phantom [].
Implicit Arguments Phantom [].

CoInductive phant (p : Type) := Phant.

Section stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.

Arguments Cons [A].

CoFixpoint zeroes : stream nat := Cons 0 zeroes.

CoFixpoint ones : stream nat := Cons 1 ones.

CoFixpoint trues_falses : stream bool := Cons true falses_trues
with falses_trues : stream bool := Cons false trues_falses.

Fixpoint approx {A} (s : stream A) (n : nat) : list A :=
  match n with
    | O => nil
    | S n' =>
      match s with
        | Cons h t => h :: approx t n'
      end
  end.

Eval simpl in approx zeroes 10.

Eval simpl in approx trues_falses 10.

Section map.
  Variables A B : Type.
  Variable f : A -> B.

  CoFixpoint map (s : stream A) : stream B :=
    match s with
      | Cons h t => Cons (f h) (map t)
    end.
End map.

Arguments map [A B].

Section interleave.
  Variable A : Type.

  CoFixpoint interleave (s1 s2 : stream A) : stream A :=
    match s1, s2 with
      | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

Arguments interleave [A].


CoFixpoint zipWith {A} (f : A -> A -> A) (a : stream A)
           (b : stream A) : stream A :=
  match a, b with
  | Cons x xs, Cons y ys => Cons (f x y) (zipWith f xs ys)
  end.

Definition tl {A} (s : stream A) : stream A :=
  match s with
    | Cons _ tl' => tl'
  end.

(*
CoFixpoint bad : stream := tl (Cons 1 bad).

CoFixpoint fib : stream :=
  zipWith plus (Cons 1 fib) (Cons 1 (Cons 1 fib)).
 *)

Section stream_eq.
  Variable A : Type.

  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2,
    stream_eq t1 t2
    -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.

Arguments stream_eq [A].

Definition ones' := map S zeroes.

Definition frob {A} (s : stream A) : stream A :=
  match s with
    | Cons h t => Cons h t
  end.

Theorem frob_eq : forall {A} (s : stream A), s = frob s.
  destruct s. reflexivity.
Qed.

Theorem ones_eq : stream_eq ones ones'.
Proof.
  cofix.
  rewrite (frob_eq ones).
  rewrite (frob_eq ones').
  simpl.
  constructor.
  fold (map succn zeroes).
  assumption.
Qed.

Definition hd {A} (s : stream A) : A :=
  match s with
    | Cons x _ => x
  end.


Section stream_eq_coind.
  Variable A : Type.
  Variable R : stream A -> stream A -> Prop.

  Hypothesis Cons_case_hd : forall s1 s2, R s1 s2 -> hd s1 = hd s2.
  Hypothesis Cons_case_tl : forall s1 s2, R s1 s2 -> R (tl s1) (tl s2).

  Theorem stream_eq_coind : forall s1 s2, R s1 s2 -> stream_eq s1 s2.
  Proof.
    cofix; destruct s1; destruct s2; intro.
    generalize (Cons_case_hd _ _ H).
    intro Heq; simpl in Heq; rewrite Heq.
    constructor.
    apply stream_eq_coind.
    apply (Cons_case_tl _ _ H).
  Qed.
End stream_eq_coind.

Arguments stream_eq_coind [A].

Theorem ones_eq'' : stream_eq ones ones'.
  apply (stream_eq_coind (fun s1 s2 => s1 = ones /\ s2 = ones')); auto; intros s1 s2 hs; destruct hs as [hs1 hs2]; rewrite hs1; rewrite hs2; auto.
Qed.

From mathcomp.ssreflect
     Require Import eqtype.

Import Equality.

Print clone.
Print pack.

Print phant_id.
Print clone.
Import TheCanonical.
About put.
About Put.

Definition get' := 
fun (vT sT : Type) (v : vT) (s : sT) '(@Put _ _ _ _ _) => s
     : forall (vT sT : Type) (v : vT) (s : sT), put v v s -> sT.


Definition get' :=
  fun vT sT (v : vT) (s : sT) '(@Put _ _ _ _ _) => s
 : forall (vT sT : Type) (v : vT) (s : sT), put v v s -> sT.

About Phantom.
Print argumentType.
Print dependentReturnType.
Print returnType.