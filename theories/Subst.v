(** * Parallel substitution (definitions only)

    !! This file exists SOLELY so that the β-rule of definitional equality can
    !! be *stated* (Abel Fig. 2.2 needs [t[s/x]]) and so η can be stated (it
    !! needs [tm_ren wk]). The normalizer never substitutes: evaluation goes
    !! through environments (Model.v) instead. Nothing in Model.v depends on this
    !! file, and — per plan.md M3 — there are NO substitution lemmas here, only
    !! the definitions the metatheory statements consume.

    Structure mirrors the renamings already in NormalForms.v: recursion on the
    term, going under a binder with [ope_keep] / [sub_lift]. Because matching a
    term [t : tm Γ T] refines [Γ], which occurs in the type of the OPE or
    substitution argument, each traversal uses the same convoy
    [match t in tm G T0 return … -> tm Δ T0] we used for [eval]. *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import Syntax OPE.

Open Scope ty_scope.

(** ** Renaming of terms along OPEs

    The term-level counterpart of [var_ren]/[nf_ren]. Needed on its own to state
    η (which weakens [t] under a fresh binder) and as the transport used when a
    parallel substitution crosses a binder. *)

Fixpoint tm_ren {Δ Γ T} (o : ope Δ Γ) (t : tm Γ T) {struct t} : tm Δ T :=
  match t in tm G T0 return ope Δ G -> tm Δ T0 with
  | tzero      => fun _ => tzero
  | tsuc n     => fun o => tsuc (tm_ren o n)
  | trec z s n => fun o => trec (tm_ren o z) (tm_ren o s) (tm_ren o n)
  | tvar x     => fun o => tvar (var_ren o x)
  | tlam b     => fun o => tlam (tm_ren (ope_keep o) b)
  | tapp r s   => fun o => tapp (tm_ren o r) (tm_ren o s)
  end o.

(** ** Parallel substitutions

    [sub Δ Γ] replaces each variable of [Γ] by a term in [Δ] (compare [Env] in
    Model.v, which does the same for semantic values). *)

Definition sub (Δ Γ : cxt) : Type := forall T, var Γ T -> tm Δ T.

(** Lifting under a binder: the new variable [vz] maps to itself; every old
    variable is substituted and then weakened past the new binder with
    [tm_ren wk]. Same head/tail convoy as [env_ext]. *)
Definition sub_lift {Δ Γ S} (σ : sub Δ Γ) : sub (S :: Δ) (S :: Γ) :=
  fun T x =>
    (match x in var G T'
           return sub Δ (tl G) -> tm (hd S G :: Δ) T' with
     | vz   => fun _  => tvar vz
     | vs y => fun σ' => tm_ren wk (σ' _ y)
     end) σ.

(** Applying a parallel substitution. *)
Fixpoint subst {Δ Γ T} (σ : sub Δ Γ) (t : tm Γ T) {struct t} : tm Δ T :=
  match t in tm G T0 return sub Δ G -> tm Δ T0 with
  | tzero      => fun _ => tzero
  | tsuc n     => fun σ => tsuc (subst σ n)
  | trec z s n => fun σ => trec (subst σ z) (subst σ s) (subst σ n)
  | tvar x     => fun σ => σ _ x
  | tlam b     => fun σ => tlam (subst (sub_lift σ) b)
  | tapp r s   => fun σ => tapp (subst σ r) (subst σ s)
  end σ.

(** ** Single substitution [t[s/x]]

    The β-redex substitution: replace the outermost variable of [t] by [s],
    leaving the rest of the context alone. Built from a parallel substitution
    that sends [vz] to [s] and [vs y] to [tvar y]. The motive keeps the context
    as [tl G] (not the outer [Γ]) so both branches agree; for the real argument
    [x : var (S :: Γ) U] it reduces to [tm Γ U]. *)
Definition subst1 {Γ S T} (t : tm (S :: Γ) T) (s : tm Γ S) : tm Γ T :=
  subst (fun U (x : var (S :: Γ) U) =>
           (match x in var G U'
                  return tm (tl G) (hd S G) -> tm (tl G) U' with
            | vz   => fun s0 => s0
            | vs y => fun _  => tvar y
            end) s) t.
