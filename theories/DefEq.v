(** * Definitional equality (Abel Ch. 2, Fig. 2.2)

    An inductive [defeq Γ T t t'] transcribing Fig. 2.2. Because our syntax is
    intrinsically typed, the figure's typing premises (e.g. [Γ, x:S ⊢ t : T]) are
    already carried by the term arguments, so each rule keeps only its
    *computational* content. Definitional equality is a [Prop]: it is the
    specification the normalizer is later proved sound and complete against
    (M4), never something the normalizer consumes. *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import Syntax OPE Subst.

Open Scope ty_scope.

Reserved Notation "Γ ⊢ t == t' :∈ T" (at level 70, t at level 69, t' at level 69).

Inductive defeq : forall (Γ : cxt) (T : ty), tm Γ T -> tm Γ T -> Prop :=

(** *** Computation rules (β) — Fig. 2.2, top block *)

(* (λx.t) s = t[s/x]. The capture-avoiding substitution [subst1] is exactly why
   Subst.v exists. *)
| deq_beta : forall {Γ S T} (t : tm (S :: Γ) T) (s : tm Γ S),
    Γ ⊢ tapp (tlam t) s == subst1 t s :∈ T

(* rec z s zero = z. *)
| deq_rec_zero : forall {Γ T} (z : tm Γ T) (s : tm Γ (tN ⇒ T ⇒ T)),
    Γ ⊢ trec z s tzero == z :∈ T

(* rec z s (suc n) = s n (rec z s n). *)
| deq_rec_suc : forall {Γ T} (z : tm Γ T) (s : tm Γ (tN ⇒ T ⇒ T)) (n : tm Γ tN),
    Γ ⊢ trec z s (tsuc n) == tapp (tapp s n) (trec z s n) :∈ T

(** *** Function extensionality (η) — Fig. 2.2, middle block

    λx. t x = t. The bound [t] must be weakened under the new binder before it is
    applied to the fresh variable [vz]; that weakening is [tm_ren wk] — the other
    reason Subst.v exists. *)
| deq_eta : forall {Γ S T} (t : tm Γ (S ⇒ T)),
    Γ ⊢ tlam (tapp (tm_ren wk t) (tvar vz)) == t :∈ (S ⇒ T)

(** *** Compatibility (congruence) — Fig. 2.2, bottom block

    Abel lists compatibility for constants, variables, λ and application. In his
    Fig. 2.1 presentation [zero]/[suc]/[rec] are *constants* eliminated by
    application, so application-compatibility already covers them. Our design
    decision #2 makes them term formers instead (a fully applied [trec]), so we
    add explicit congruences for [tsuc] and [trec]. [tzero] and [tvar] are
    nullary/atomic and covered by [deq_refl]. *)
| deq_lam : forall {Γ S T} (t t' : tm (S :: Γ) T),
    (S :: Γ) ⊢ t == t' :∈ T ->
    Γ ⊢ tlam t == tlam t' :∈ (S ⇒ T)

| deq_app : forall {Γ S T} (r r' : tm Γ (S ⇒ T)) (s s' : tm Γ S),
    Γ ⊢ r == r' :∈ (S ⇒ T) ->
    Γ ⊢ s == s' :∈ S ->
    Γ ⊢ tapp r s == tapp r' s' :∈ T

| deq_suc : forall {Γ} (n n' : tm Γ tN),
    Γ ⊢ n == n' :∈ tN ->
    Γ ⊢ tsuc n == tsuc n' :∈ tN

| deq_rec : forall {Γ T} (z z' : tm Γ T) (s s' : tm Γ (tN ⇒ T ⇒ T)) (n n' : tm Γ tN),
    Γ ⊢ z == z' :∈ T ->
    Γ ⊢ s == s' :∈ (tN ⇒ T ⇒ T) ->
    Γ ⊢ n == n' :∈ tN ->
    Γ ⊢ trec z s n == trec z' s' n' :∈ T

(** *** Equivalence — reflexivity, symmetry, transitivity *)

| deq_refl : forall {Γ T} (t : tm Γ T),
    Γ ⊢ t == t :∈ T

| deq_sym : forall {Γ T} (t t' : tm Γ T),
    Γ ⊢ t == t' :∈ T ->
    Γ ⊢ t' == t :∈ T

| deq_trans : forall {Γ T} (t1 t2 t3 : tm Γ T),
    Γ ⊢ t1 == t2 :∈ T ->
    Γ ⊢ t2 == t3 :∈ T ->
    Γ ⊢ t1 == t3 :∈ T

where "Γ ⊢ t == t' :∈ T" := (defeq Γ T t t').

(** A small hint database so the congruence-heavy derivations below (and the
    fundamental lemma in M4) can be discharged by [eauto with defeq]. *)
Create HintDb defeq.
#[export] Hint Constructors defeq : defeq.

(** ** Sanity derivations (plan.md M3: two or three [Example]s) *)

(** β on the identity: [(λx.x) zero = zero]. [subst1 (tvar vz) tzero] reduces to
    [tzero], so [deq_beta] applies up to conversion. *)
Example ex_beta_id :
  [] ⊢ tapp (tlam (tvar vz)) tzero == tzero :∈ tN.
Proof. apply deq_beta. Qed.

(** A [rec] step: [1 + 1 = 2] via [tadd]. [tadd m n = trec m (λ_λr. suc r) n], so
    this walks one [deq_rec_suc], one β to fire the step function, and one
    [deq_rec_zero], glued by transitivity. *)
Example ex_add_1_1 :
  [] ⊢ tadd (numeral 1) (numeral 1) == numeral 2 :∈ tN.
Proof.
  unfold tadd, numeral.
  eapply deq_trans.
  { apply deq_rec_suc. }                 (* rec z s (suc zero) = s zero (rec z s zero) *)
  eapply deq_trans.
  { apply deq_app.
    - apply deq_beta.                    (* fire the step's outer λ on [zero] *)
    - apply deq_rec_zero. }              (* inner rec z s zero = z = suc zero *)
  (* now: (λr. suc r) (suc zero) == suc (suc zero) — one more β *)
  eapply deq_trans.
  { apply deq_beta. }
  apply deq_refl.
Qed.

(** η at first order: [λx. f x = f] for [f : N ⇒ N] in context [[N ⇒ N]]. *)
Example ex_eta_fun :
  [tN ⇒ tN] ⊢ tlam (tapp (tm_ren wk (tvar vz)) (tvar vz)) == tvar vz :∈ (tN ⇒ tN).
Proof. apply deq_eta. Qed.
