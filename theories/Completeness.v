(** * Completeness of NbE via the Kripke natural-PER (plan_amendment2.md, M4')

    [defeq t t' -> nf t = nf t'], AXIOM-FREE (the PER replaces the funext route
    of the old M4). Built on theories/PER.v. This file holds items 6-9 of the
    amendment's checklist: the fundamental lemma of the PER model, the semantic
    substitution lemma up to [SEq], the fundamental lemma for [defeq], and
    [completeness].

    All of items 6-9 done and axiom-free: completeness is proved. *)

From Stdlib Require Import List. Import ListNotations.
From NbE Require Import Syntax OPE NormalForms Model Subst DefEq PER.
Open Scope ty_scope.

Lemma SEq_ren_comp : forall T {Γ Δ Δ'} (o1 : ope Δ Δ') (o2 : ope Δ' Γ) (a a' : sem T Γ),
    SEq T a a' -> SEq T (sem_ren T (ope_comp o1 o2) a) (sem_ren T o1 (sem_ren T o2 a')).
Proof.
  induction T as [| A IHA B IHB]; intros Γ Δ Δ' o1 o2 a a' H.
  - cbn in *. rewrite semnat_ren_comp. now rewrite H.
  - intros Δ0 o0 b b' Hb.
    destruct (H Δ0 (ope_comp o0 (ope_comp o1 o2)) b b' Hb) as [Hc Hs]. split.
    + cbn. rewrite !ope_comp_assoc. exact Hc.
    + intros Δ'' o''. cbn. rewrite !ope_comp_assoc. specialize (Hs Δ'' o''). exact Hs.
Qed.

Lemma SEnv_refl_l : forall {Δ Γ} (ρ ρ' : Env Δ Γ), SEnv ρ ρ' -> SEnv ρ ρ.
Proof. intros Δ Γ ρ ρ' H T x. apply (SEq_refl_l T _ _ (H T x)). Qed.
Lemma SEnv_ren_comp : forall {Δ Δ' Δ'' Γ} (o0 : ope Δ'' Δ') (o : ope Δ' Δ) (ρ ρ' : Env Δ Γ),
    SEnv ρ ρ' -> SEnv (env_ren o0 (env_ren o ρ)) (env_ren (ope_comp o0 o) ρ').
Proof.
  intros Δ Δ' Δ'' Γ o0 o ρ ρ' H T x.
  apply (SEq_sym T). apply SEq_ren_comp. apply (SEq_sym T). apply H.
Qed.

Lemma eval_fund : forall {Γ T} (t : tm Γ T) {Δ} (ρ ρ' : Env Δ Γ),
    SEnv ρ ρ' ->
    SEq T (eval t ρ) (eval t ρ')
    /\ forall Δ' (o : ope Δ' Δ), SEq T (eval t (env_ren o ρ)) (sem_ren T o (eval t ρ')).
Proof.
  intros Γ T t; induction t; intros Δ ρ ρ' Hρ.
  - split; [ reflexivity | intros; reflexivity ].
  - split.
    + cbn. f_equal. exact (proj1 (IHt _ _ _ Hρ)).
    + intros Δ' o. cbn. f_equal. exact (proj2 (IHt _ _ _ Hρ) Δ' o).
  - split.
    + cbn. destruct (IHt3 _ _ _ Hρ) as [Hn _]. cbn in Hn. rewrite Hn.
      apply SEq_semrec; [ exact (proj1 (IHt1 _ _ _ Hρ)) | exact (proj1 (IHt2 _ _ _ Hρ)) ].
    + intros Δ' o. cbn.
      destruct (IHt1 _ _ _ Hρ) as [Hz1 Hzc]. destruct (IHt2 _ _ _ Hρ) as [Hs1 Hsc].
      destruct (IHt3 _ _ _ Hρ) as [_ Hnc]. specialize (Hnc Δ' o). cbn in Hnc. rewrite Hnc.
      apply (semrec_SEq_ren o _ _ (eval t1 ρ') (eval t2 ρ') (eval t3 ρ')).
      * exact (Hzc Δ' o).
      * exact (Hsc Δ' o).
      * exact (SEq_refl_r _ _ _ Hz1).
      * exact (SEq_refl_r _ _ _ Hs1).
  - split; [ apply Hρ | intros Δ' o; apply SEq_ren; apply Hρ ].
  - split.
    + intros Δ0 o a a' Ha. split.
      * exact (proj1 (IHt _ _ _ (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ Hρ) Ha))).
      * intros Δ' o'.
        assert (HSE : SEnv (env_ren o' (env_ext (env_ren o ρ) a))
                       (env_ext (env_ren (ope_comp o' o) ρ') (sem_ren _ o' a'))).
        { intros U x. revert U x. refine (var_cons_case _ _ _ _ _).
          - apply SEq_ren; exact Ha.
          - intros U y. apply (SEnv_ren_comp o' o ρ ρ' Hρ). }
        eapply (SEq_trans _).
        { apply (SEq_sym _).
          apply (proj2 (IHt _ (env_ext (env_ren o ρ) a) (env_ext (env_ren o ρ) a)
                    (SEnv_refl_l _ _ (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ Hρ) Ha))) Δ' o'). }
        exact (proj1 (IHt _ _ _ HSE)).
    + intros Δ' o Δ0 o0 a a' Ha. split.
      * apply (proj1 (IHt _ (env_ext (env_ren o0 (env_ren o ρ)) a)
                          (env_ext (env_ren (ope_comp o0 o) ρ') a')
                          (SEnv_ext _ _ _ _ (SEnv_ren_comp o0 o ρ ρ' Hρ) Ha))).
      * intros Δ'' o''.
        assert (HSE : SEnv (env_ren o'' (env_ext (env_ren o0 (env_ren o ρ)) a))
                       (env_ext (env_ren (ope_comp (ope_comp o'' o0) o) ρ') (sem_ren _ o'' a'))).
        { intros U x. revert U x. refine (var_cons_case _ _ _ _ _).
          - apply SEq_ren; exact Ha.
          - intros U y.
            apply (SEq_sym U). eapply (SEq_trans U).
            + apply (SEq_ren_comp U (ope_comp o'' o0) o (ρ' U y) (ρ U y)).
              apply (SEq_sym U). apply Hρ.
            + apply (SEq_ren_comp U o'' o0 (sem_ren U o (ρ U y)) (sem_ren U o (ρ U y))).
              apply SEq_ren. apply (SEq_refl_l _ _ _ (Hρ U y)). }
        eapply (SEq_trans _).
        { apply (SEq_sym _).
          apply (proj2 (IHt _ (env_ext (env_ren o0 (env_ren o ρ)) a)
                    (env_ext (env_ren o0 (env_ren o ρ)) a)
                    (SEnv_refl_l _ _ (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ (SEnv_ren _ _ _ Hρ)) Ha)))
                    Δ'' o''). }
        exact (proj1 (IHt _ _ _ HSE)).
  - destruct (IHt1 _ _ _ Hρ) as [H1c H1m]. destruct (IHt2 _ _ _ Hρ) as [H2c H2m].
    split.
    + cbn. exact (proj1 (H1c Δ ope_id (eval t2 ρ) (eval t2 ρ') H2c)).
    + intros Δ' o. cbn.
      eapply (SEq_trans T).
      * exact (proj1 ((H1m Δ' o) Δ' ope_id (eval t2 (env_ren o ρ))
                        (sem_ren S o (eval t2 ρ')) (H2m Δ' o))).
      * cbn. rewrite ope_comp_id_l. apply (SEq_sym T).
        destruct ((SEq_refl_r _ _ _ H1c) Δ ope_id (eval t2 ρ') (eval t2 ρ')
                    (SEq_refl_r _ _ _ H2c)) as [_ Hsq].
        specialize (Hsq Δ' o). rewrite ope_comp_id_r in Hsq. exact Hsq.
Qed.

Lemma var_ren_wk : forall {Γ S T} (x : var Γ T), var_ren (wk (S:=S)) x = vs x.
Proof. intros. cbn. now rewrite var_ren_id. Qed.

Lemma SEnv_ext_keep : forall {Γ' Γ Δ Δ0 S} (o : ope Γ' Γ) (oo : ope Δ0 Δ)
    (ρ ρ' : Env Δ Γ') (a a' : sem S Δ0),
    SEnv ρ ρ' -> SEq S a a' ->
    SEnv (fun U x => (env_ext (env_ren oo ρ') a') U (var_ren (ope_keep o) x))
         (env_ext (env_ren oo (fun U x => ρ' U (var_ren o x))) a').
Proof.
  intros Γ' Γ Δ Δ0 S o oo ρ ρ' a a' Hρ Ha U x. revert U x.
  refine (var_cons_case _ _ _ _ _).
  - apply (SEq_refl_r _ _ _ Ha).
  - intros U y. apply SEq_ren. apply (SEq_refl_r _ _ _ (Hρ U (var_ren o y))).
Qed.

Lemma eval_ren : forall {Γ T} (t : tm Γ T) {Γ' Δ} (o : ope Γ' Γ) (ρ ρ' : Env Δ Γ'),
    SEnv ρ ρ' -> SEq T (eval (tm_ren o t) ρ) (eval t (fun U x => ρ' U (var_ren o x))).
Proof.
  intros Γ T t; induction t; intros Γ' Δ o ρ ρ' Hρ.
  - reflexivity.
  - cbn. f_equal. exact (IHt _ _ o _ _ Hρ).
  - cbn. pose proof (IHt3 _ _ o _ _ Hρ) as Hn3. cbn in Hn3. rewrite Hn3.
    apply SEq_semrec; [ exact (IHt1 _ _ o _ _ Hρ) | exact (IHt2 _ _ o _ _ Hρ) ].
  - cbn. apply Hρ.
  - intros Δ0 oo a a' Ha. split.
    + eapply (SEq_trans T).
      * exact (IHt _ _ (ope_keep o) (env_ext (env_ren oo ρ) a) (env_ext (env_ren oo ρ') a')
                 (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ Hρ) Ha)).
      * exact (proj1 (eval_fund t _ _ (SEnv_ext_keep o oo ρ ρ' a a' Hρ Ha))).
    + intros Δ1 o1.
      assert (HSQ : SEnv (fun U x =>
                  (env_ren o1 (env_ext (env_ren oo ρ') a')) U (var_ren (ope_keep o) x))
                  (env_ext (env_ren (ope_comp o1 oo) (fun U x => ρ' U (var_ren o x)))
                           (sem_ren _ o1 a'))).
      { intros U x. revert U x. refine (var_cons_case _ _ _ _ _).
        - apply SEq_ren. apply (SEq_refl_r _ _ _ Ha).
        - intros U y. apply (SEq_sym _). apply SEq_ren_comp.
          apply (SEq_refl_r _ _ _ (Hρ U (var_ren o y))). }
      eapply (SEq_trans T).
      { apply (SEq_sym T).
        apply (proj2 (eval_fund (tm_ren (ope_keep o) t) (env_ext (env_ren oo ρ) a)
                  (env_ext (env_ren oo ρ) a)
                  (SEnv_refl_l _ _ (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ Hρ) Ha))) Δ1 o1). }
      eapply (SEq_trans T).
      { exact (IHt _ _ (ope_keep o) (env_ren o1 (env_ext (env_ren oo ρ) a))
                 (env_ren o1 (env_ext (env_ren oo ρ') a'))
                 (SEnv_ren _ _ _ (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ Hρ) Ha))). }
      exact (proj1 (eval_fund t _ _ HSQ)).
  - cbn. exact (proj1 ((IHt1 _ _ o _ _ Hρ) Δ ope_id _ _ (IHt2 _ _ o _ _ Hρ))).
Qed.


Corollary eval_wk : forall {Γ S T} (t : tm Γ T) {Δ} (ρ ρ' : Env Δ (S :: Γ)),
    SEnv ρ ρ' -> SEq T (eval (tm_ren wk t) ρ) (eval t (fun U x => ρ' U (vs x))).
Proof.
  intros Γ S T t Δ ρ ρ' H.
  eapply (SEq_trans T); [ exact (eval_ren t wk ρ ρ' H) | ].
  assert (HSE : SEnv (fun U x => ρ' U (var_ren wk x)) (fun U x => ρ' U (vs x))).
  { intros U x. rewrite var_ren_wk. apply (SEq_refl_r _ _ _ (H U (vs x))). }
  exact (proj1 (eval_fund t _ _ HSE)).
Qed.

Lemma SEnv_refl_r : forall {Δ Γ} (ρ ρ' : Env Δ Γ), SEnv ρ ρ' -> SEnv ρ' ρ'.
Proof. intros Δ Γ ρ ρ' H U x. apply (SEq_refl_r _ _ _ (H U x)). Qed.

Lemma eval_subst : forall {Γ T} (t : tm Γ T) {Δ' Δ} (σ : sub Δ' Γ) (ρ ρ' : Env Δ Δ'),
    SEnv ρ ρ' -> SEq T (eval (subst σ t) ρ) (eval t (fun U x => eval (σ U x) ρ')).
Proof.
  intros Γ T t; induction t; intros Δ' Δ σ ρ ρ' Hρ.
  - reflexivity.
  - cbn. f_equal. exact (IHt _ _ σ _ _ Hρ).
  - cbn. pose proof (IHt3 _ _ σ _ _ Hρ) as Hn3. cbn in Hn3. rewrite Hn3.
    apply SEq_semrec; [ exact (IHt1 _ _ σ _ _ Hρ) | exact (IHt2 _ _ σ _ _ Hρ) ].
  - cbn. exact (proj1 (eval_fund _ ρ ρ' Hρ)).
  - intros Δ0 oo a a' Ha.
    assert (BR : SEnv (fun U x => eval (sub_lift σ U x) (env_ext (env_ren oo ρ') a'))
                 (env_ext (env_ren oo (fun U x => eval (σ U x) ρ')) a')).
    { intros U x. revert U x. refine (var_cons_case _ _ _ _ _).
      - apply (SEq_refl_r _ _ _ Ha).
      - intros U y.
        eapply (SEq_trans U).
        + exact (eval_wk (σ U y) (env_ext (env_ren oo ρ') a') (env_ext (env_ren oo ρ') a')
                   (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ (fun U0 z => SEq_refl_r _ _ _ (Hρ U0 z)))
                             (SEq_refl_r _ _ _ Ha))).
        + exact (proj2 (eval_fund (σ U y) ρ' ρ' (fun U0 z => SEq_refl_r _ _ _ (Hρ U0 z))) Δ0 oo). }
    split.
    + eapply (SEq_trans T).
      * exact (IHt _ _ (sub_lift σ) (env_ext (env_ren oo ρ) a) (env_ext (env_ren oo ρ') a')
                 (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ Hρ) Ha)).
      * exact (proj1 (eval_fund t _ _ BR)).
    + intros Δ1 o1.
      assert (HSQ : SEnv (fun U x => eval (sub_lift σ U x) (env_ren o1 (env_ext (env_ren oo ρ') a')))
                  (env_ext (env_ren (ope_comp o1 oo) (fun U x => eval (σ U x) ρ')) (sem_ren _ o1 a'))).
      { intros U x. revert U x. refine (var_cons_case _ _ _ _ _).
        - apply (SEq_refl_r _ _ _ (SEq_ren _ _ _ _ Ha)).
        - intros U y.
          eapply (SEq_trans U).
          { exact (eval_wk (σ U y) (env_ren o1 (env_ext (env_ren oo ρ') a'))
                     (env_ren o1 (env_ext (env_ren oo ρ') a'))
                     (SEnv_ren _ _ _ (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ (SEnv_refl_r _ _ Hρ))
                                         (SEq_refl_r _ _ _ Ha)))). }
          eapply (SEq_trans U).
          { exact (proj2 (eval_fund (σ U y) (env_ren oo ρ') (env_ren oo ρ')
                     (SEnv_ren _ _ _ (SEnv_refl_r _ _ Hρ))) Δ1 o1). }
          eapply (SEq_trans U).
          { apply SEq_ren. exact (proj2 (eval_fund (σ U y) ρ' ρ' (SEnv_refl_r _ _ Hρ)) Δ0 oo). }
          apply (SEq_sym U). apply SEq_ren_comp.
          exact (proj1 (eval_fund (σ U y) ρ' ρ' (SEnv_refl_r _ _ Hρ))). }
      eapply (SEq_trans T).
      { apply (SEq_sym T).
        apply (proj2 (eval_fund (subst (sub_lift σ) t) (env_ext (env_ren oo ρ) a)
                  (env_ext (env_ren oo ρ) a)
                  (SEnv_refl_l _ _ (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ Hρ) Ha))) Δ1 o1). }
      eapply (SEq_trans T).
      { exact (IHt _ _ (sub_lift σ) (env_ren o1 (env_ext (env_ren oo ρ) a))
                 (env_ren o1 (env_ext (env_ren oo ρ') a'))
                 (SEnv_ren _ _ _ (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ Hρ) Ha))). }
      exact (proj1 (eval_fund t _ _ HSQ)).
  - cbn. exact (proj1 ((IHt1 _ _ σ _ _ Hρ) Δ ope_id _ _ (IHt2 _ _ σ _ _ Hρ))).
Qed.

Lemma SEnv_sym : forall {Δ Γ} (ρ ρ' : Env Δ Γ), SEnv ρ ρ' -> SEnv ρ' ρ.
Proof. intros Δ Γ ρ ρ' H U x. apply (SEq_sym U). apply H. Qed.

Lemma defeq_fund : forall {Γ T} (t t' : tm Γ T), defeq Γ T t t' ->
    forall {Δ} (ρ ρ' : Env Δ Γ), SEnv ρ ρ' -> SEq T (eval t ρ) (eval t' ρ').
Proof.
  intros Γ T t t' H; induction H; intros Δ ρ ρ' Hρ.
  - (* beta *) cbn.
    assert (HSE : SEnv (env_ext (env_ren ope_id ρ) (eval s ρ)) (fun U x => eval (scons s U x) ρ')).
    { intros U x. revert U x. refine (var_cons_case _ _ _ _ _).
      - exact (proj1 (eval_fund s ρ ρ' Hρ)).
      - intros U y. apply SEq_ren_id. apply Hρ. }
    eapply (SEq_trans T).
    + exact (proj1 (eval_fund t _ _ HSE)).
    + apply (SEq_sym T). exact (eval_subst t (scons s) ρ' ρ' (SEnv_refl_r _ _ Hρ)).
  - (* rec_zero *) exact (proj1 (eval_fund z ρ ρ' Hρ)).
  - (* rec_suc *) exact (proj1 (eval_fund (tapp (tapp s n) (trec z s n)) ρ ρ' Hρ)).
  - (* eta *) intros Δ0 o a a' Ha.
    assert (Hwk : SEq (S ⇒ T) (eval (tm_ren wk t) (env_ext (env_ren o ρ) a))
                    (eval t (env_ren o ρ))).
    { eapply (SEq_trans (S ⇒ T)).
      - exact (eval_wk t (env_ext (env_ren o ρ) a) (env_ext (env_ren o ρ) a)
                 (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ (SEnv_refl_l _ _ Hρ)) (SEq_refl_l _ _ _ Ha))).
      - assert (HS : SEnv (fun U x => env_ext (env_ren o ρ) a U (vs x)) (env_ren o ρ)).
        { intros U z. apply SEq_ren. apply (SEq_refl_l _ _ _ (Hρ U z)). }
        exact (proj1 (eval_fund t _ _ HS)). }
    pose proof (proj2 (eval_fund t ρ ρ' Hρ)) as Hc.
    split.
    + cbn.
      eapply (SEq_trans T); [ exact (proj1 (Hwk Δ0 ope_id a a' Ha)) | ].
      pose proof (proj1 ((Hc Δ0 o) Δ0 ope_id a' a' (SEq_refl_r _ _ _ Ha))) as Hstep.
      cbn in Hstep. rewrite ope_comp_id_l in Hstep. exact Hstep.
    + intros Δ1 o1. cbn.
      eapply (SEq_trans T).
      { pose proof (proj2 (Hwk Δ0 ope_id a a' Ha) Δ1 o1) as Hsq.
        rewrite ope_comp_id_r in Hsq. exact Hsq. }
      pose proof (proj1 ((Hc Δ0 o) Δ1 o1 (sem_ren _ o1 a') (sem_ren _ o1 a')
                    (SEq_refl_r _ _ _ (SEq_ren _ _ _ _ Ha)))) as Hstep.
      cbn in Hstep. exact Hstep.
  - (* lam *) intros Δ0 o a a' Ha. split.
    + exact (IHdefeq _ (env_ext (env_ren o ρ) a) (env_ext (env_ren o ρ') a')
               (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ Hρ) Ha)).
    + intros Δ1 o1.
      assert (HSQ : SEnv (env_ren o1 (env_ext (env_ren o ρ') a'))
                  (env_ext (env_ren (ope_comp o1 o) ρ') (sem_ren _ o1 a'))).
      { intros U x. revert U x. refine (var_cons_case _ _ _ _ _).
        - apply (SEq_refl_r _ _ _ (SEq_ren _ _ _ _ Ha)).
        - intros U y. apply (SEq_sym _). apply SEq_ren_comp.
          apply (SEq_refl_r _ _ _ (Hρ U y)). }
      eapply (SEq_trans T).
      { apply (SEq_sym T). exact (proj2 (eval_fund t (env_ext (env_ren o ρ) a)
                (env_ext (env_ren o ρ) a)
                (SEnv_refl_l _ _ (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ Hρ) Ha))) Δ1 o1). }
      eapply (SEq_trans T).
      { exact (IHdefeq _ (env_ren o1 (env_ext (env_ren o ρ) a))
                 (env_ren o1 (env_ext (env_ren o ρ') a'))
                 (SEnv_ren _ _ _ (SEnv_ext _ _ _ _ (SEnv_ren _ _ _ Hρ) Ha))). }
      exact (proj1 (eval_fund t' _ _ HSQ)).
  - (* app *)
    exact (proj1 ((IHdefeq1 _ ρ ρ' Hρ) Δ ope_id _ _ (IHdefeq2 _ ρ ρ' Hρ))).
  - (* suc *) cbn. f_equal. exact (IHdefeq _ ρ ρ' Hρ).
  - (* rec *) cbn. pose proof (IHdefeq3 _ ρ ρ' Hρ) as Hn. cbn in Hn. rewrite Hn.
    apply SEq_semrec; [ exact (IHdefeq1 _ ρ ρ' Hρ) | exact (IHdefeq2 _ ρ ρ' Hρ) ].
  - (* refl *) exact (proj1 (eval_fund t ρ ρ' Hρ)).
  - (* sym *) apply (SEq_sym T). exact (IHdefeq _ ρ' ρ (SEnv_sym _ _ Hρ)).
  - (* trans *) eapply (SEq_trans T);
      [ exact (IHdefeq1 _ ρ ρ' Hρ) | exact (IHdefeq2 _ ρ' ρ' (SEnv_refl_r _ _ Hρ)) ].
Qed.

Theorem completeness : forall {Γ T} (t t' : tm Γ T),
    defeq Γ T t t' -> norm t = norm t'.
Proof.
  intros Γ T t t' H. unfold norm.
  apply (reify_SEq T).
  apply (defeq_fund t t' H).
  intros U x. apply reflect_SEq. reflexivity.
Qed.
