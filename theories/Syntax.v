(** * Syntax: intrinsically typed System T (Abel Ch. 2, Fig. 2.1)

    Types, contexts, variables, terms as an inductive family [tm : cxt -> ty ->
    Type], plus the running examples (numerals, addition, multiplication).

    Ill-typed terms do not exist, so there is no typing judgment to formalize:
    Abel's Fig. 2.1 rules are absorbed into the constructors of [tm]. In
    particular there will be no subject reduction lemma and no substitution
    lemmas anywhere in this development. *)

From Stdlib Require Import List.
Import ListNotations.

(** ** Types and contexts *)

Inductive ty : Type :=
| tN   : ty
| tarr : ty -> ty -> ty.

(* The one notation we allow ourselves; [S ⇒ T] is Abel's [S → T]. *)
Declare Scope ty_scope.
Infix "⇒" := tarr (at level 60, right associativity) : ty_scope.
Open Scope ty_scope.

(** A context is a list of types: the de Bruijn index of a variable is its
    position in the list, so we do not need Abel's freshness side condition
    [x ∉ Γ] (Fig. 2.1) — distinctness of names is not a thing that can fail. *)
Definition cxt := list ty.

(** ** Variables

    [var Γ T] is a proof-relevant "[(x:T) ∈ Γ]": a de Bruijn index that already
    knows its type. *)

Inductive var : cxt -> ty -> Type :=
| vz : forall {Γ S}, var (S :: Γ) S
| vs : forall {Γ S T}, var Γ T -> var (S :: Γ) T.

(** ** Terms

    [Γ] is an *index*, not a parameter: [tlam] stores a term in the extended
    context [S :: Γ], and we will need to do induction on terms with [Γ] varying
    (M4's fundamental lemma). A parameter would be pinned to a single [Γ] by the
    generated induction principle.

    Design decision (plan.md §2): [trec] is *fully applied*, taking all three of
    [z], [s] and the scrutinee. This matches the neutral grammar of Fig. 2.3,
    where [rec v_z v_s u] is neutral only when saturated. Abel instead has [rec]
    as a constant of type [Rec_T = T → (N → T → T) → N → T] (Fig. 2.1); partial
    applications of it are recovered here by η-expansion at the source level,
    e.g. [tlam (tlam (tlam (trec (tvar (vs (vs vz))) (tvar (vs vz)) (tvar vz))))]
    is the constant [rec] itself, and [add_fun] below is a smaller instance. *)

Inductive tm : cxt -> ty -> Type :=
| tzero : forall {Γ}, tm Γ tN
| tsuc  : forall {Γ}, tm Γ tN -> tm Γ tN
| trec  : forall {Γ T}, tm Γ T -> tm Γ (tN ⇒ T ⇒ T) -> tm Γ tN -> tm Γ T
| tvar  : forall {Γ T}, var Γ T -> tm Γ T
| tlam  : forall {Γ S T}, tm (S :: Γ) T -> tm Γ (S ⇒ T)
| tapp  : forall {Γ S T}, tm Γ (S ⇒ T) -> tm Γ S -> tm Γ T.

(** ** Running examples

    These are the terms Tests.v (M2) normalizes. They are *meta-level*
    combinators building object terms, which is what lets us instantiate them at
    open contexts, e.g. [tadd (tvar vz) (numeral 2)] in context [[tN]]. *)

Fixpoint numeral {Γ} (n : nat) : tm Γ tN :=
  match n with
  | O    => tzero
  | S n' => tsuc (numeral n')
  end.

(** [tadd m n = rec m (λ_ λr. suc r) n], i.e. recursion on [n] adding one for
    each successor. The step function ignores its first argument (the
    predecessor) and successors the recursive result. *)
Definition tadd {Γ} (m n : tm Γ tN) : tm Γ tN :=
  trec m (tlam (tlam (tsuc (tvar vz)))) n.

(** The curried addition function, [λm. λn. m + n]. This is also the example of
    "partial application of [rec] recovered by η-expansion": Abel can write the
    constant [rec] on its own, we write the η-expansion of the instance we want.
    Under the two binders, [vs vz] is [m] and [vz] is [n]. *)
Definition add_fun {Γ} : tm Γ (tN ⇒ tN ⇒ tN) :=
  tlam (tlam (tadd (tvar (vs vz)) (tvar vz))).

(** [λm. λn. rec zero (λ_ λr. m + r) n]. Multiplication needs its left factor
    under two extra binders, i.e. it needs *weakening* — which we do not have
    yet (renaming arrives with OPEs in OPE.v). Writing it as an object-level λ
    sidesteps that: inside the step function the context is [[r; p; n; m]], so
    [m] is reached by the de Bruijn index [vs (vs (vs vz))] and no meta-level
    weakening operation is required. *)
Definition mul_fun {Γ} : tm Γ (tN ⇒ tN ⇒ tN) :=
  tlam (tlam
    (trec tzero
          (tlam (tlam (tapp (tapp add_fun (tvar (vs (vs (vs vz))))) (tvar vz))))
          (tvar vz))).

(** Meta-level multiplication is then just application; the normalizer will
    β-reduce the redexes away. *)
Definition tmul {Γ} (m n : tm Γ tN) : tm Γ tN :=
  tapp (tapp mul_fun m) n.
