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

(** * Renaming/substitution lemmas (M4)

    Everything below is proof infrastructure for soundness (M4), NOT part of the
    normalizer. It is the "lemma explosion" plan.md risk #4 budgets for: the
    autosubst-style fusion laws relating [tm_ren], [subst], [ope_comp] and the
    lifting operators. All are proved by induction on the term with a
    [var_cons_case] side-lemma for the lifting operator, and all are axiom-free
    (no functional extensionality — substitutions are compared pointwise via
    [subst_ext], never as functions). *)

(** [tm_ren] is functorial (the term-level [var_ren_id]/[var_ren_comp]). The
    binder cases hold because [ope_keep] commutes with [ope_id]/[ope_comp]
    definitionally, so [f_equal] closes them up to conversion. *)
Lemma tm_ren_id : forall {Γ T} (t : tm Γ T), tm_ren ope_id t = t.
Proof.
  intros Γ T t; induction t; simpl.
  - reflexivity.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2, IHt3.
  - now rewrite var_ren_id.
  - exact (f_equal tlam IHt).
  - now rewrite IHt1, IHt2.
Qed.

Lemma tm_ren_comp :
  forall {Γ T} (t : tm Γ T) {Δ Δ'} (o1 : ope Δ Δ') (o2 : ope Δ' Γ),
    tm_ren (ope_comp o1 o2) t = tm_ren o1 (tm_ren o2 t).
Proof.
  intros Γ T t; induction t; intros; simpl; try reflexivity.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2, IHt3.
  - now rewrite var_ren_comp.
  - exact (f_equal tlam (IHt _ _ (ope_keep o1) (ope_keep o2))).
  - now rewrite IHt1, IHt2.
Qed.

(** The single substitution [scons s] (send [vz] to [s], keep the rest) and its
    n-ary cousin [ext_sub σ s], used to state β below. [subst1 t s] is
    definitionally [subst (scons s) t]. *)
Definition scons {Γ S} (s : tm Γ S) : sub Γ (S :: Γ) :=
  fun U x =>
    (match x in var G U' return tm (tl G) (hd S G) -> tm (tl G) U' with
     | vz   => fun s0 => s0
     | vs y => fun _  => tvar y
     end) s.

Lemma subst1_scons : forall {Γ S T} (t : tm (S :: Γ) T) (s : tm Γ S),
    subst1 t s = subst (scons s) t.
Proof. reflexivity. Qed.

Definition ext_sub {Δ Γ S} (σ : sub Δ Γ) (s : tm Δ S) : sub Δ (S :: Γ) :=
  fun U x =>
    (match x in var G U' return tm Δ (hd S G) -> sub Δ (tl G) -> tm Δ U' with
     | vz   => fun s0 _  => s0
     | vs y => fun _  σ0 => σ0 _ y
     end) s σ.

(** Extensionality: [subst] depends on its substitution only pointwise. This is
    what lets the whole cascade stay funext-free. *)
Lemma sub_lift_ext : forall {Δ Γ S} (σ τ : sub Δ Γ),
    (forall U x, σ U x = τ U x) ->
    forall U x, sub_lift (S:=S) σ U x = sub_lift τ U x.
Proof.
  intros Δ Γ S σ τ H U x. revert U x.
  refine (var_cons_case S Γ _ _ _); [reflexivity | intros U y; simpl; now rewrite H].
Qed.

Lemma subst_ext : forall {Γ T} (t : tm Γ T) {Δ} (σ τ : sub Δ Γ),
    (forall U x, σ U x = τ U x) -> subst σ t = subst τ t.
Proof.
  intros Γ T t; induction t; intros Δ σ τ H; simpl; try reflexivity.
  - now rewrite (IHt _ _ _ H).
  - now rewrite (IHt1 _ _ _ H), (IHt2 _ _ _ H), (IHt3 _ _ _ H).
  - now rewrite H.
  - rewrite (IHt _ (sub_lift σ) (sub_lift τ)); [reflexivity | now apply sub_lift_ext].
  - now rewrite (IHt1 _ _ _ H), (IHt2 _ _ _ H).
Qed.

(** Substituting by the identity (variables-to-themselves) is the identity. The
    last step needed to read soundness off the fundamental lemma: [subst id t] is
    what the fundamental lemma produces at the identity substitution, and it must
    collapse back to [t]. *)
Lemma subst_id : forall {Γ T} (t : tm Γ T), subst (fun U (x : var Γ U) => tvar x) t = t.
Proof.
  intros Γ T t; induction t; simpl; try reflexivity.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2, IHt3.
  - f_equal. transitivity (subst (fun U (x : var _ U) => tvar x) t).
    { apply subst_ext. refine (var_cons_case _ _ _ _ _);
        [ reflexivity | intros U y; cbn; now rewrite var_ren_id ]. }
    exact IHt.
  - now rewrite IHt1, IHt2.
Qed.

(** Renaming is the substitution by variables, [sren o]. *)
Definition sren {Δ Γ} (o : ope Δ Γ) : sub Δ Γ := fun U x => tvar (var_ren o x).

Lemma sub_lift_sren : forall {Δ Γ S} (o : ope Δ Γ) U x,
    sub_lift (S:=S) (sren o) U x = sren (ope_keep o) U x.
Proof.
  intros Δ Γ S o U x. revert U x.
  refine (var_cons_case S Γ _ _ _).
  - reflexivity.
  - intros U y. simpl. unfold sren. simpl. now rewrite var_ren_id.
Qed.

Lemma ren_is_subst : forall {Γ T} (t : tm Γ T) {Δ} (o : ope Δ Γ),
    tm_ren o t = subst (sren o) t.
Proof.
  intros Γ T t; induction t; intros Δ o; simpl; try reflexivity.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2, IHt3.
  - rewrite IHt. f_equal. apply subst_ext. intros. now rewrite sub_lift_sren.
  - now rewrite IHt1, IHt2.
Qed.

(** The four fusion laws. [subst_ren]/[ren_subst] push a renaming through a
    substitution; [subst_subst] composes two substitutions. The binder cases use
    the [ope_comp_keep_wk]/[ope_comp_wk] weakening square from OPE.v. *)
Lemma subst_ren : forall {Γ T} (t : tm Γ T) {Δ Δ'} (o : ope Δ' Γ) (σ : sub Δ Δ'),
    subst σ (tm_ren o t) = subst (fun U x => σ U (var_ren o x)) t.
Proof.
  intros Γ T t; induction t; intros Δ Δ' o σ; simpl; try reflexivity.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2, IHt3.
  - rewrite IHt. f_equal. apply subst_ext.
    refine (var_cons_case _ _ _ _ _); [reflexivity | intros U y; reflexivity].
  - now rewrite IHt1, IHt2.
Qed.

Lemma ren_subst : forall {Γ T} (t : tm Γ T) {Δ Δ'} (σ : sub Δ' Γ) (o : ope Δ Δ'),
    tm_ren o (subst σ t) = subst (fun U x => tm_ren o (σ U x)) t.
Proof.
  intros Γ T t; induction t; intros Δ Δ' σ o; simpl; try reflexivity.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2, IHt3.
  - rewrite IHt. f_equal. apply subst_ext.
    refine (var_cons_case _ _ _ _ _).
    + reflexivity.
    + intros U y. simpl. unfold sub_lift; simpl.
      rewrite <- !tm_ren_comp. now rewrite ope_comp_keep_wk, ope_comp_wk.
  - now rewrite IHt1, IHt2.
Qed.

Lemma subst_subst : forall {Γ T} (t : tm Γ T) {Δ Δ'} (τ : sub Δ' Γ) (σ : sub Δ Δ'),
    subst σ (subst τ t) = subst (fun U x => subst σ (τ U x)) t.
Proof.
  intros Γ T t; induction t; intros Δ Δ' τ σ; simpl; try reflexivity.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2, IHt3.
  - rewrite IHt. f_equal. apply subst_ext.
    refine (var_cons_case _ _ _ _ _).
    + reflexivity.
    + intros U y. simpl. rewrite subst_ren, ren_subst. apply subst_ext.
      intros U0 z. simpl. now rewrite var_ren_id.
  - now rewrite IHt1, IHt2.
Qed.

(** The two consequences soundness actually consumes:
    - [ren_subst1]: renaming commutes with single substitution (needed to show
      [defeq] is stable under renaming — its β case, in Soundness.v);
    - [beta_sub]: firing a β-redex under a lifted substitution and a renaming
      equals substituting by the extended, renamed substitution (the crux of the
      fundamental lemma's λ-case). *)
Lemma ren_subst1 : forall {Γ S T} (t : tm (S :: Γ) T) (s : tm Γ S) {Δ} (o : ope Δ Γ),
    tm_ren o (subst1 t s) = subst1 (tm_ren (ope_keep o) t) (tm_ren o s).
Proof.
  intros. rewrite !subst1_scons, ren_subst, subst_ren. apply subst_ext.
  refine (var_cons_case _ _ _ _ _); [reflexivity | intros U y; reflexivity].
Qed.

Lemma beta_sub : forall {Γ S T} (body : tm (S :: Γ) T) {Δ Δ'}
                        (σ : sub Δ' Γ) (o : ope Δ Δ') (s : tm Δ S),
    subst1 (tm_ren (ope_keep o) (subst (sub_lift σ) body)) s
    = subst (ext_sub (fun U x => tm_ren o (σ U x)) s) body.
Proof.
  intros. rewrite subst1_scons, subst_ren, subst_subst. apply subst_ext.
  refine (var_cons_case _ _ _ _ _).
  - reflexivity.
  - intros U y. simpl. rewrite subst_ren, (ren_is_subst (σ U y) o). apply subst_ext.
    intros U0 z. simpl. unfold sren. now rewrite var_ren_id.
Qed.
