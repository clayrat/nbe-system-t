(** * Deciding definitional equality (plan.md M6, packaging)

    The payoff of putting soundness and completeness together: definitional
    equality *is* equality of normal forms. Since [norm t] is a concrete,
    finite [nf Γ T] (computed with no proofs — [Compute norm t] runs), this
    turns the undecidable-looking judgment [Γ ⊢ t = t'] into a check on two
    normal forms.

      soundness    : Γ ⊢ nf_emb (norm t) = t
      completeness : Γ ⊢ t = t' -> norm t = norm t'

    give the two directions below.

    A full [Decidable (defeq Γ T t t')] instance needs decidable equality on
    [nf]/[ne]. That is intrinsically-typed dependent decidable equality (a
    no-confusion + UIP development on [var]/[nf]/[ne]); plain [decide equality]
    fails on the indexed families. It is separable from the metatheory and is
    left as noted in PROGRESS.md — [defeq_iff_norm] already reduces the question
    to a comparison of two computable normal forms. *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import Syntax OPE NormalForms Model DefEq Soundness Completeness.
Open Scope ty_scope.

Theorem defeq_iff_norm : forall {Γ T} (t t' : tm Γ T),
    defeq Γ T t t' <-> norm t = norm t'.
Proof.
  intros Γ T t t'. split; [ apply completeness | ].
  intros Heq.
  assert (Hs : defeq Γ T t (nf_emb (norm t'))).
  { rewrite <- Heq. apply deq_sym. apply (soundness t). }
  eapply deq_trans; [ exact Hs | apply (soundness t') ].
Qed.

(** A couple of worked checks (compare with Tests.v). [2+2] and [4] are
    definitionally equal iff they normalize to the same thing — and they do. *)
Example decide_2_2 :
  defeq [] tN (tadd (numeral 2) (numeral 2)) (numeral 4).
Proof. apply defeq_iff_norm. reflexivity. Qed.

Example decide_eta :
  defeq [tN ⇒ tN] (tN ⇒ tN)
    (tlam (tapp (tvar (vs vz)) (tvar vz))) (tvar vz).
Proof. apply defeq_iff_norm. reflexivity. Qed.
