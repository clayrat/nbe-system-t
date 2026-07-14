(** * Soundness of NbE (Abel Ch. 2, §2.6)

    The Kripke logical relation [LR] between terms and semantic values, defined
    by recursion on the type; monotonicity under OPEs; the two sandwich lemmas
    (reflection is logically related, reification is definitionally equal); the
    relation on environments; the fundamental lemma; and

      Theorem soundness : forall Γ T (t : tm Γ T), defeq Γ T (nf_emb (nf t)) t.

    Abel's side condition [∀Γ' ≤ Γ] becomes an explicit OPE argument.

    TODO(M4): contents. *)

From NbE Require Import Syntax OPE NormalForms Model Subst DefEq.
