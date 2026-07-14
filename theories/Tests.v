(** * Smoke tests for the normalizer (plan.md M2 acceptance)

    Each test first had its [norm] output eyeballed via [Compute], then frozen as
    an [Example ... reflexivity]. These are the regression suite: they run in the
    kernel, so they also witness that [norm] genuinely *computes* (no opaque
    definitions, no stuck [match]). Add freely. *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import Syntax OPE NormalForms Model.
Open Scope ty_scope.

(** Expected normal-form numerals, mirroring [numeral] on the [nf] side. *)
Fixpoint nnumeral {Γ} (n : nat) : nf Γ tN :=
  match n with
  | O    => nzero
  | S n' => nsuc (nnumeral n')
  end.

(** ** Closed base-type terms: arithmetic really runs *)

Example add_2_2 :
  norm (tadd (numeral 2) (numeral 2) : tm [] tN) = nnumeral 4.
Proof. reflexivity. Qed.

(** [3 * 2 = 6] additionally exercises β-reduction: [tmul] is [mul_fun] applied,
    so the normalizer must fire the two redexes and then run the inner [trec]. *)
Example mul_3_2 :
  norm (tmul (numeral 3) (numeral 2) : tm [] tN) = nnumeral 6.
Proof. reflexivity. Qed.

(** ** η at function type (open, functional)

    In context [[N ⇒ N]] the variable [f = vz]. Its η-expansion [λx. f x]
    (with [f] weakened to [vs vz] under the binder) must normalize to the same
    η-long normal form as [f] itself. This is the payoff of the reification-at-
    arrow clause: both sides become [λx. f x] in normal form. *)

Example eta_var :
  norm (tlam (tapp (tvar (vs vz)) (tvar vz)) : tm [tN ⇒ tN] (tN ⇒ tN))
  = norm (tvar vz : tm [tN ⇒ tN] (tN ⇒ tN)).
Proof. reflexivity. Qed.

Example eta_shape :
  norm (tvar vz : tm [tN ⇒ tN] (tN ⇒ tN))
  = nlam (nne (napp (nvar (vs vz)) (nne (nvar vz)))).
Proof. reflexivity. Qed.

(** ** A stuck recursor (open, base type)

    [tadd m n] recurses on [n], so the *scrutinee* is the variable in
    [tadd (numeral 2) (tvar vz)] (context [[N]]). Recursion cannot fire, and the
    normal form is a neutral [nrec] blocked on [nvar vz], with [z] and the step
    function reified underneath. (Note: this differs from plan.md's suggested
    [add (tvar vz) (numeral 2)], which is *not* stuck under recursion-on-the-
    second-argument — there the variable is the base value and recursion runs to
    [suc (suc vz)]. See PROGRESS.md.) *)

Example stuck_rec :
  norm (tadd (numeral 2) (tvar vz) : tm [tN] tN)
  = nne (nrec (nsuc (nsuc nzero))
              (nlam (nlam (nsuc (nne (nvar vz)))))
              (nvar vz)).
Proof. reflexivity. Qed.

(** The complementary non-stuck case, to document the asymmetry: here the
    variable is the base and the concrete [2] is consumed. *)
Example rec_runs :
  norm (tadd (tvar vz) (numeral 2) : tm [tN] tN)
  = nsuc (nsuc (nne (nvar vz))).
Proof. reflexivity. Qed.

(** ** Environment renaming under nested binders (plan.md risk #3)

    [K = λx. λy. x] must not capture: the result reads the *outer* bound
    variable [vs vz], not [vz]. A version of [eval] that captured a stale
    environment would get this wrong. *)

Example const_K :
  norm (tlam (tlam (tvar (vs vz))) : tm [] (tN ⇒ tN ⇒ tN))
  = nlam (nlam (nne (nvar (vs vz)))).
Proof. reflexivity. Qed.

(** ** Idempotence (Abel §2.2, soundness property 3): [norm (norm t) = norm t]

    Stated as [norm (nf_emb (norm t)) = norm t] since [norm] eats terms. Checks a
    representative closed term and a representative open/stuck one. *)

Example idem_closed :
  norm (nf_emb (norm (tmul (numeral 3) (numeral 2) : tm [] tN)))
  = norm (tmul (numeral 3) (numeral 2) : tm [] tN).
Proof. reflexivity. Qed.

Example idem_stuck :
  norm (nf_emb (norm (tadd (numeral 2) (tvar vz) : tm [tN] tN)))
  = norm (tadd (numeral 2) (tvar vz) : tm [tN] tN).
Proof. reflexivity. Qed.
