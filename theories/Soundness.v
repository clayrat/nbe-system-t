(** * Soundness of NbE (Abel Ch. 2, §2.6)

    The goal:

      Theorem soundness : forall Γ T (t : tm Γ T), defeq Γ T (nf_emb (norm t)) t.

    i.e. the normal form of [t] is definitionally equal to [t] — normalization
    does not change meaning. It is proved via a Kripke logical relation [LR]
    between a term and a semantic value, exactly as in Abel §2.6, with OPEs in
    place of his context-extension side conditions [Γ' ≤ Γ].

    The whole file is axiom-free (no functional extensionality): semantic
    functions are never compared as functions. The one deliberate design choice
    that buys this is in the reification "sandwich" lemma below — see [sandwich].

    Proof skeleton (Abel §2.6, in order):
      1. [LR] and the renaming laws it rests on ([defeq_ren], [LR_mono]).
      2. [LR_conv]: [LR] respects [defeq] on the term side.
      3. [sandwich]: reflection lands in [LR]; reification is [defeq] to the
         term. Proved by mutual induction on the type.
      4. [LR_semrec]: the recursor preserves [LR] (induction on the [SemNat]).
      5. [fundamental]: every term is [LR]-related to its evaluation.
      6. [soundness]: instantiate the fundamental lemma at the identity. *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import Syntax OPE NormalForms Model Subst DefEq.

Open Scope ty_scope.

(** The embeddings are natural w.r.t. renaming. (Stated here, not in
    NormalForms.v, because it relates [tm_ren] from Subst.v with [nf_emb].) *)
Lemma nf_ne_emb_natural :
  (forall Γ T (v : nf Γ T) Δ (o : ope Δ Γ), tm_ren o (nf_emb v) = nf_emb (nf_ren o v)) /\
  (forall Γ T (u : ne Γ T) Δ (o : ope Δ Γ), tm_ren o (ne_emb u) = ne_emb (ne_ren o u)).
Proof.
  apply nf_ne_mutind; intros; simpl; try reflexivity.
  - now rewrite H.
  - now rewrite H.
  - f_equal; apply H.
  - now rewrite H, H0.
  - now rewrite H, H0, H1.
Qed.
Definition nf_emb_natural {Γ T} := proj1 nf_ne_emb_natural Γ T.
Definition ne_emb_natural {Γ T} := proj2 nf_ne_emb_natural Γ T.

(** ** The Kripke logical relation (Abel §2.6's [Γ ⊢ t : T Ⓡ a])

    By recursion on the type. At base type, [t] is related to a semantic natural
    [n] iff, in *every* extension, [t] is definitionally equal to the term read
    back from [n] — Abel's [∀Γ' ≤ Γ. Γ' ⊢ t = v̂(Γ') : N], with the OPE [o]
    playing the role of the extension. At function type it is "related arguments
    to related results", again quantified over extensions. *)
Fixpoint LR (T : ty) : forall {Γ}, tm Γ T -> sem T Γ -> Prop :=
  match T as T0 return forall Γ, tm Γ T0 -> sem T0 Γ -> Prop with
  | tN =>
      fun Γ t n =>
        forall Δ (o : ope Δ Γ),
          defeq Δ tN (tm_ren o t) (nf_emb (reify_nat (semnat_ren o n)))
  | A ⇒ B =>
      fun Γ r f =>
        forall Δ (o : ope Δ Γ) (s : tm Δ A) (a : sem A Δ),
          LR A s a -> LR B (tapp (tm_ren o r) s) (f Δ o a)
  end.

(** ** [defeq] is stable under renaming

    The only substantial case is β, which needs [ren_subst1] (renaming commutes
    with single substitution); η uses the weakening square; the rest are
    congruences that commute with [tm_ren] definitionally. *)
Lemma defeq_ren : forall {Γ T} {t t' : tm Γ T},
    defeq Γ T t t' -> forall {Δ} (o : ope Δ Γ), defeq Δ T (tm_ren o t) (tm_ren o t').
Proof.
  intros Γ T t t' H; induction H; intros Δ o; simpl.
  - rewrite ren_subst1. apply deq_beta.
  - apply deq_rec_zero.
  - apply deq_rec_suc.
  - rewrite <- tm_ren_comp, ope_comp_keep_wk, <- ope_comp_wk, tm_ren_comp.
    apply deq_eta.
  - apply deq_lam. apply (IHdefeq _ (ope_keep o)).
  - apply deq_app; [ apply IHdefeq1 | apply IHdefeq2 ].
  - apply deq_suc. apply IHdefeq.
  - apply deq_rec; [ apply IHdefeq1 | apply IHdefeq2 | apply IHdefeq3 ].
  - apply deq_refl.
  - apply deq_sym. apply IHdefeq.
  - eapply deq_trans; [ apply IHdefeq1 | apply IHdefeq2 ].
Qed.

(** Monotonicity: [LR] survives renaming both sides. No recursion is needed —
    the Kripke structure of [LR] does the work — so we case on the type. *)
Lemma LR_mono : forall T {Γ Δ} (o : ope Δ Γ) (t : tm Γ T) (a : sem T Γ),
    LR T t a -> LR T (tm_ren o t) (sem_ren T o a).
Proof.
  destruct T as [| A B]; intros Γ Δ o t a H.
  - intros Δ' o'. cbn in *. rewrite <- tm_ren_comp, <- semnat_ren_comp. apply H.
  - intros Δ' o' s a' Ha. cbn in *. rewrite <- tm_ren_comp.
    apply (H _ (ope_comp o' o) s a' Ha).
Qed.

(** [LR] respects definitional equality on the term side (the base case is why
    [defeq_ren] is needed). *)
Lemma LR_conv : forall T {Γ} (t t' : tm Γ T) (a : sem T Γ),
    defeq Γ T t t' -> LR T t' a -> LR T t a.
Proof.
  induction T as [| A IHA B IHB]; intros Γ t t' a Hdefeq H.
  - intros Δ o. cbn in *. eapply deq_trans; [ apply (defeq_ren Hdefeq) | apply H ].
  - intros Δ o s a' Ha.
    apply (IHB _ (tapp (tm_ren o t) s) (tapp (tm_ren o t') s)).
    + apply deq_app; [ apply defeq_ren; exact Hdefeq | apply deq_refl ].
    + apply H; exact Ha.
Qed.

(** ** The sandwich (Abel §2.6): reflection ⊆ [LR] ⊆ reification

    Proved by mutual induction on the type — the two halves are interdependent
    (reify-at-arrow needs that variables reflect into [LR]; reflect-at-arrow
    needs reify at the domain).

    Note the reification half is stated as [defeq (tm_ren o t) (nf_emb (nf_ren o
    (reify T a)))]: the renaming is applied *outside* [reify], as [nf_ren o
    (reify T a)], rather than inside as [reify T (sem_ren o a)]. Those two are
    equal only when [a] is natural (a Kripke naturality condition), which
    arbitrary semantic values need not satisfy — proving that equality would
    require functional extensionality. Pushing the [nf_ren] out avoids it
    entirely and keeps soundness axiom-free. *)
Lemma sandwich : forall T,
  (forall Γ (u' : tm Γ T) (u : ne Γ T),
     (forall Δ (o : ope Δ Γ), defeq Δ T (tm_ren o u') (ne_emb (ne_ren o u))) ->
     LR T u' (reflect T u))
  /\
  (forall Γ (t : tm Γ T) (a : sem T Γ),
     LR T t a ->
     forall Δ (o : ope Δ Γ),
       defeq Δ T (tm_ren o t) (nf_emb (nf_ren o (reify T a)))).
Proof.
  induction T as [| A [IHPA IHQA] B [IHPB IHQB]]; split.
  - (* reflect, base *) intros Γ u' u H Δ o. cbn. apply H.
  - (* reify, base *) intros Γ t a H Δ o. cbn. rewrite reify_nat_natural. apply H.
  - (* reflect, arrow *) intros Γ u' u H Δ o s a Ha. cbn.
    apply (IHPB _ (tapp (tm_ren o u') s) (napp (ne_ren o u) (reify A a))).
    intros Δ' o'. cbn. rewrite <- tm_ren_comp, <- ne_ren_comp.
    apply deq_app; [ apply (H _ (ope_comp o' o)) | apply (IHQA _ s a Ha) ].
  - (* reify, arrow *) intros Γ r f H Δ o. cbn.
    eapply deq_trans; [ apply deq_sym; apply deq_eta | ].
    apply deq_lam.
    assert (LRvar : LR A (tvar (@vz Γ A)) (reflect A (nvar (@vz Γ A)))).
    { apply (IHPA (A :: Γ) (tvar (@vz Γ A)) (nvar (@vz Γ A))).
      intros Δ'' o''. cbn. apply deq_refl. }
    pose proof (IHQB _ (tapp (tm_ren wk r) (tvar (@vz Γ A)))
                       (f (A :: Γ) wk (reflect A (nvar (@vz Γ A))))
                       (H (A :: Γ) wk (tvar (@vz Γ A)) (reflect A (nvar (@vz Γ A))) LRvar)
                       _ (ope_keep o)) as Hq.
    cbn in Hq. rewrite <- tm_ren_comp, ope_comp_keep_wk in Hq.
    cbn. rewrite <- tm_ren_comp, ope_comp_wk. exact Hq.
Qed.

Definition LR_reflect T := proj1 (sandwich T).
Definition LR_reify T := proj2 (sandwich T).

(** A variable is logically related to its own reflection (the identity
    environment, below, is built from this). *)
Lemma LR_var : forall {Γ T} (x : var Γ T), LR T (tvar x) (reflect T (nvar x)).
Proof. intros. apply LR_reflect. intros Δ o. cbn. apply deq_refl. Qed.

(** ** The recursor preserves [LR] (Abel §2.5's updated [rec], soundly)

    [emb_nat na] is the term read back from a semantic natural. First: any
    semantic natural is [LR]-related to its own readback ([LR_emb_nat]). The core
    lemma [LR_semrec_emb] then goes by induction on the [SemNat] with the
    scrutinee fixed to [emb_nat na]; [LR_semrec] bridges from an arbitrary
    [LR]-related scrutinee via [LR_conv] (a related [n] is [defeq] to
    [emb_nat na]). *)
Definition emb_nat {Γ} (na : SemNat Γ) : tm Γ tN := nf_emb (reify_nat na).

Lemma LR_emb_nat : forall {Γ} (na : SemNat Γ), LR tN (emb_nat na) na.
Proof.
  intros Γ na Δ o. cbn. unfold emb_nat.
  rewrite nf_emb_natural, reify_nat_natural. apply deq_refl.
Qed.

Lemma LR_semrec_emb : forall {Γ T} (z : tm Γ T) (za : sem T Γ)
    (s : tm Γ (tN ⇒ T ⇒ T)) (sa : sem (tN ⇒ T ⇒ T) Γ),
    LR T z za -> LR (tN ⇒ T ⇒ T) s sa ->
    forall (na : SemNat Γ), LR T (trec z s (emb_nat na)) (semrec za sa na).
Proof.
  intros Γ T z za s sa Hz Hs na; induction na as [| na' IH | u].
  - (* zero *) apply (LR_conv _ _ z); [ apply deq_rec_zero | exact Hz ].
  - (* suc *)
    apply (LR_conv _ _ (tapp (tapp s (emb_nat na')) (trec z s (emb_nat na')))).
    { apply deq_rec_suc. }
    pose proof (Hs Γ ope_id (emb_nat na') na' (LR_emb_nat na')) as Hs1.
    rewrite tm_ren_id in Hs1.
    pose proof (Hs1 Γ ope_id (trec z s (emb_nat na')) (semrec za sa na') IH) as Hs2.
    rewrite tm_ren_id in Hs2. exact Hs2.
  - (* stuck on a neutral: reify z and s, reflect a neutral [nrec] *)
    apply (LR_reflect T _ (trec z s (ne_emb u))
             (nrec (reify T za) (reify (tN ⇒ T ⇒ T) sa) u)).
    intros Δ o. cbn. rewrite ne_emb_natural. apply deq_rec.
    + apply (LR_reify T _ z za Hz).
    + apply (LR_reify (tN ⇒ T ⇒ T) _ s sa Hs).
    + apply deq_refl.
Qed.

Lemma LR_semrec : forall {Γ T} (z : tm Γ T) (za : sem T Γ)
    (s : tm Γ (tN ⇒ T ⇒ T)) (sa : sem (tN ⇒ T ⇒ T) Γ),
    LR T z za -> LR (tN ⇒ T ⇒ T) s sa ->
    forall (n : tm Γ tN) (na : SemNat Γ), LR tN n na ->
      LR T (trec z s n) (semrec za sa na).
Proof.
  intros Γ T z za s sa Hz Hs n na Hn.
  apply (LR_conv _ _ (trec z s (emb_nat na))).
  - apply deq_rec; [ apply deq_refl | apply deq_refl | ].
    pose proof (Hn Γ ope_id) as Hn0. rewrite tm_ren_id, semnat_ren_id in Hn0.
    exact Hn0.
  - apply LR_semrec_emb; assumption.
Qed.

(** ** The fundamental lemma

    A substitution [σ] and an environment [ρ] are related when they are
    pointwise [LR]-related. Every term is then [LR]-related to its evaluation.
    The λ-case is the heart: after firing β ([beta_sub]) it reduces to the IH on
    the body under the extended substitution/environment, whose relatedness comes
    from [LR_mono] (for the old variables) and the argument hypothesis (for the
    new one). *)
Definition LRenv {Δ Γ} (σ : sub Δ Γ) (ρ : Env Δ Γ) : Prop :=
  forall T (x : var Γ T), LR T (σ T x) (ρ T x).

Lemma fundamental : forall {Γ T} (t : tm Γ T) {Δ} (σ : sub Δ Γ) (ρ : Env Δ Γ),
    LRenv σ ρ -> LR T (subst σ t) (eval t ρ).
Proof.
  intros Γ T t; induction t; intros Δ σ ρ Hσ.
  - (* tzero *) intros Δ' o. cbn. apply deq_refl.
  - (* tsuc *) intros Δ' o. cbn. apply deq_suc. apply (IHt _ σ ρ Hσ).
  - (* trec *)
    apply (LR_semrec _ _ _ _ (IHt1 _ σ ρ Hσ) (IHt2 _ σ ρ Hσ) _ _ (IHt3 _ σ ρ Hσ)).
  - (* tvar *) apply Hσ.
  - (* tlam *) intros Δ' o s a Ha.
    apply (LR_conv _ _ (subst (ext_sub (fun U x => tm_ren o (σ U x)) s) t)).
    + simpl. rewrite <- beta_sub. apply deq_beta.
    + apply (IHt _ (ext_sub (fun U x => tm_ren o (σ U x)) s) (env_ext (env_ren o ρ) a)).
      intros U x. revert U x. refine (var_cons_case _ _ _ _ _).
      * exact Ha.
      * intros U y. cbn. apply LR_mono. apply Hσ.
  - (* tapp *)
    pose proof (IHt1 _ σ ρ Hσ Δ ope_id (subst σ t2) (eval t2 ρ) (IHt2 _ σ ρ Hσ)) as Ha.
    rewrite tm_ren_id in Ha. exact Ha.
Qed.

(** ** Soundness

    Instantiate the fundamental lemma at the identity substitution (whose
    relatedness to the reflected identity environment [env_id] is [LR_var]),
    collapse [subst id t] to [t] ([subst_id]), then read off the [defeq] via the
    reification half of the sandwich at the identity OPE. *)
Theorem soundness : forall {Γ T} (t : tm Γ T),
    defeq Γ T (nf_emb (norm t)) t.
Proof.
  intros Γ T t.
  assert (Hid : LRenv (fun U (x : var Γ U) => tvar x) (@env_id Γ)).
  { intros U x. apply LR_var. }
  pose proof (fundamental t (fun U x => tvar x) env_id Hid) as HLR.
  rewrite subst_id in HLR.
  pose proof (LR_reify T _ t (eval t env_id) HLR Γ ope_id) as Hr.
  rewrite tm_ren_id, nf_ren_id in Hr.
  apply deq_sym. exact Hr.
Qed.
