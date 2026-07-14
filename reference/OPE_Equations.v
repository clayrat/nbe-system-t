(** * OPE via the Equations plugin — REFERENCE ONLY, not part of the build

    plan.md forbids the Equations dependency, and the main development
    (theories/OPE.v) uses plain-Coq convoy patterns plus a hand-written
    dependent case principle [ope_cons_case]. This file records what the same
    definitions and category laws look like *with* Equations, so the trade-off
    is documented and re-checkable rather than a claim in PROGRESS.md.

    It is self-contained (re-declares [ty]/[cxt]/[var]/[ope] rather than
    importing NbE, so it needs no build order) and is NOT listed in _CoqProject.
    Compile ad hoc with:

        coqc reference/OPE_Equations.v

    Findings this file demonstrates (all verified):

    1. [ope_comp] and [var_ren] take Agda-style nested patterns — no convoy, no
       [hd]/[tl] motive.
    2. [funelim]/[depelim] replace the hand-written [ope_cons_case] motives; the
       five category / functoriality lemmas are 1–5 lines each.
    3. It is axiom-free AND leaves no obligations *provided* you derive only
       [Signature] + [NoConfusion]. Deriving [NoConfusionHom] for [ope] or [var]
       is what leaves unsolved obligations (it wants UIP on the indices); we do
       not need it. See [Print Assumptions] at the bottom.
    4. [Compute]/[vm_compute] reduce, and kernel [reflexivity] regression tests
       (the M2 acceptance pattern) still work — see the [Example]s at the end.
       Caveat: plain [cbv]/[simpl] get *stuck* on Equations-defined functions
       unless [Set Equations Transparent] is on, because Equations marks them
       opaque to tactic-level reduction. This is the one behavioural difference
       from the plain-Coq version. *)

From Stdlib Require Import List.
Import ListNotations.
From Equations Require Import Equations.

Inductive ty : Type := tN | tarr : ty -> ty -> ty.
Definition cxt := list ty.

Inductive var : cxt -> ty -> Type :=
| vz : forall {G S}, var (S :: G) S
| vs : forall {G S T}, var G T -> var (S :: G) T.

Inductive ope : cxt -> cxt -> Type :=
| ope_nil  : ope [] []
| ope_drop : forall {D G S}, ope D G -> ope (S :: D) G
| ope_keep : forall {D G S}, ope D G -> ope (S :: D) (S :: G).

(* [Signature] + [NoConfusion] are enough for [funelim]/[depelim] below.
   Deliberately NOT [NoConfusionHom] — see header note 3. *)
Derive Signature NoConfusion for ope.
Derive Signature NoConfusion for var.

(** ** Definitions — nested dependent patterns, no convoy pattern

    Contrast theories/OPE.v, where the [ope_keep] cases need an inner [match]
    with a [return forall Δ1, ope Δ1 (tl D) -> ope (hd S0 D :: Δ1) G] motive to
    push the index equation into the branches. Equations does that inference. *)

Equations ope_comp {D' D G} (o1 : ope D' D) (o2 : ope D G) : ope D' G :=
  ope_comp ope_nil        o2             := o2;
  ope_comp (ope_drop o1') o2             := ope_drop (ope_comp o1' o2);
  ope_comp (ope_keep o1') (ope_drop o2') := ope_drop (ope_comp o1' o2');
  ope_comp (ope_keep o1') (ope_keep o2') := ope_keep (ope_comp o1' o2').

Equations ope_id (G : cxt) : ope G G :=
  ope_id []       := ope_nil;
  ope_id (_ :: G) := ope_keep (ope_id G).
Arguments ope_id {G}.

Definition wk {G S} : ope (S :: G) G := ope_drop ope_id.

Equations var_ren {D G T} (o : ope D G) (x : var G T) : var D T :=
  var_ren ope_nil       x      := x;
  var_ren (ope_drop o') x      := vs (var_ren o' x);
  var_ren (ope_keep o')  vz    := vz;
  var_ren (ope_keep o') (vs y) := vs (var_ren o' y).

(** ** Category laws — [funelim] does the inversion [ope_cons_case] does by hand *)

Lemma ope_comp_id_l {D G} (o : ope D G) : ope_comp ope_id o = o.
Proof. induction o; simp ope_comp ope_id; congruence. Qed.

Lemma ope_comp_id_r {D G} (o : ope D G) : ope_comp o ope_id = o.
Proof. induction o; simp ope_comp ope_id; congruence. Qed.

Lemma ope_comp_assoc {D'' D' D G}
  (o1 : ope D'' D') (o2 : ope D' D) (o3 : ope D G) :
  ope_comp (ope_comp o1 o2) o3 = ope_comp o1 (ope_comp o2 o3).
Proof.
  funelim (ope_comp o1 o2); simp ope_comp; try reflexivity.
  - depelim o3; simp ope_comp; now rewrite H.
  - now rewrite H.
  - depelim o3; simp ope_comp; now rewrite H.
Qed.

(** ** A representative M4 functoriality lemma

    These ([var_ren]/[nf_ren]/[ne_ren]/[tm_ren] respect [ope_comp] and
    [ope_id]) are the ~10-lemma budget plan.md's risk #4 warns about. Shown here
    for [var_ren] to confirm the Equations style scales past [OPE.v] itself. *)

Lemma var_ren_id {G T} (x : var G T) : var_ren ope_id x = x.
Proof. induction x; simp ope_id var_ren; congruence. Qed.

Lemma var_ren_comp {D'' D' D T}
  (o1 : ope D'' D') (o2 : ope D' D) (x : var D T) :
  var_ren (ope_comp o1 o2) x = var_ren o1 (var_ren o2 x).
Proof.
  funelim (ope_comp o1 o2); simp ope_comp var_ren;
    try (depelim x; simp var_ren); try reflexivity; now rewrite H.
Qed.

(** ** Reduction and the M2 acceptance pattern still work *)

Compute var_ren (wk (S:=tN)) (vz : var [tN] tN).
(*  = vs vz  *)

Example freeze1 : var_ren (wk (S:=tN)) (vz : var [tN] tN) = vs vz.
Proof. reflexivity. Qed.

Example freeze2 :
  ope_comp (wk (S:=tN)) (ope_id (G:=[tN])) = ope_drop (ope_keep ope_nil).
Proof. reflexivity. Qed.

(** All axiom-free ("Closed under the global context") and obligation-free. *)
Print Assumptions ope_comp_assoc.
Print Assumptions var_ren_comp.
Print Assumptions var_ren_id.
