(** * Kripke natural-PER for completeness (plan_amendment2.md, M4')

    [SEq] is a *natural* PER on semantic values: at arrows it carries both a
    congruence clause and a naturality *square*. Amendment 1's congruence-only
    relation was insufficient for System T — [semrec]'s [SSuc] clause applies
    semantic values at an algorithm-chosen [ope_id] inside a structural
    recursion, so [eval_fund]'s commuting conjunct needs the square of those
    values, which congruence-only self-relatedness cannot carry.

    Countermodel (why the square must be *in* the relation, not derived): the
    type-correct [f Δ o a := match o with ope_drop _ => SZero | _ => a end] is
    congruence-self-related (both sides of the clause share one [o]) yet fails
    the square. Pure STLC never applies a semantic value at an algorithm-chosen
    OPE, so congruence-only would suffice there; [semrec]'s [ope_id] applications
    are what force the square into the relation for System T.

    Everything at [tN] and everything syntactic (Nf/Ne/var/tm) stays raw
    equality; [SEq] replaces [=] only at higher [sem] types. Axiom-free. *)

From Stdlib Require Import List. Import ListNotations.
From NbE Require Import Syntax OPE NormalForms Model Subst DefEq.
Open Scope ty_scope.

(* Natural PER: congruence AND the naturality square at arrows. *)
Fixpoint SEq (T : ty) : forall {Γ}, sem T Γ -> sem T Γ -> Prop :=
  match T as T0 return forall Γ, sem T0 Γ -> sem T0 Γ -> Prop with
  | tN => fun _ n n' => n = n'
  | A ⇒ B => fun Γ f f' =>
      forall Δ (o : ope Δ Γ) (a a' : sem A Δ), SEq A a a' ->
        SEq B (f Δ o a) (f' Δ o a')
        /\ forall Δ' (o' : ope Δ' Δ),
             SEq B (sem_ren B o' (f Δ o a))
                   (f' Δ' (ope_comp o' o) (sem_ren A o' a'))
  end.

(* (2) sem_ren preserves SEq. No PER laws used, so item (1) may use this. *)
Lemma SEq_ren : forall T {Γ Δ} (o : ope Δ Γ) (a a' : sem T Γ),
    SEq T a a' -> SEq T (sem_ren T o a) (sem_ren T o a').
Proof.
  induction T as [| A IHA B IHB]; intros Γ Δ o a a' H.
  - cbn in *. now rewrite H.
  - intros Δ0 o0 b b' Hb.
    destruct (H Δ0 (ope_comp o0 o) b b' Hb) as [Hc Hs]. split.
    + cbn. exact Hc.
    + intros Δ' o'. cbn. rewrite ope_comp_assoc. apply Hs.
Qed.

Lemma SEq_ren_id : forall T {Γ} (a a' : sem T Γ),
    SEq T a a' -> SEq T (sem_ren T ope_id a) a'.
Proof.
  destruct T as [| A B]; intros Γ a a' H.
  - cbn in *. now rewrite semnat_ren_id.
  - intros Δ o b b' Hb.
    destruct (H Δ (ope_comp o ope_id) b b' Hb) as [Hc Hs].
    split.
    + cbn. rewrite ope_comp_id_r. rewrite ope_comp_id_r in Hc. exact Hc.
    + intros Δ' o'. cbn. rewrite ope_comp_id_r. specialize (Hs Δ' o').
      rewrite ope_comp_id_r in Hs. exact Hs.
Qed.

(* (1) PER laws: symmetry and transitivity, mutual induction on the type. *)
Lemma SEq_PER : forall T,
  (forall Γ (a a' : sem T Γ), SEq T a a' -> SEq T a' a) /\
  (forall Γ (a a' a'' : sem T Γ), SEq T a a' -> SEq T a' a'' -> SEq T a a'').
Proof.
  induction T as [| A [symA transA] B [symB transB]].
  - split; intros Γ; cbn; [ congruence | intros a a' a''; congruence ].
  - assert (refllA : forall Γ (a a' : sem A Γ), SEq A a a' -> SEq A a a).
    { intros G x y Hxy. apply (transA _ _ _ _ Hxy (symA _ _ _ Hxy)). }
    assert (reflrA : forall Γ (a a' : sem A Γ), SEq A a a' -> SEq A a' a').
    { intros G x y Hxy. apply (transA _ _ _ _ (symA _ _ _ Hxy) Hxy). }
    split.
    + (* symmetry *)
      intros Γ f f' H Δ o a a' Ha. split.
      * (* congruence *)
        apply symB. apply (proj1 (H Δ o a' a (symA _ _ _ Ha))).
      * (* square *)
        intros Δ' o'.
        (* goal: SEq B (ren o' (f' Δ o a)) (f Δ' (o'∘o) (ren o' a')) *)
        apply (transB _ _ (sem_ren B o' (f Δ o a))).
        { (* step 1: ren o' (f' o a) ~ ren o' (f o a) *)
          apply SEq_ren. apply symB.
          apply (proj1 (H Δ o a a (refllA _ _ _ Ha))). }
        apply (transB _ _ (f' Δ' (ope_comp o' o) (sem_ren A o' a'))).
        { (* step 2: ren o' (f o a) ~ f' (o'∘o) (ren o' a') *)
          apply (proj2 (H Δ o a a' Ha)). }
        { (* step 3: f' (o'∘o) (ren o' a') ~ f (o'∘o) (ren o' a') *)
          apply symB. apply (proj1 (H Δ' (ope_comp o' o) (sem_ren A o' a') (sem_ren A o' a')
                                       (SEq_ren A o' _ _ (reflrA _ _ _ Ha)))). }
    + (* transitivity *)
      intros Γ f g h H1 H2 Δ o a a' Ha. split.
      * apply (transB _ _ (g Δ o a')).
        { apply (proj1 (H1 Δ o a a' Ha)). }
        { apply (proj1 (H2 Δ o a' a' (reflrA _ _ _ Ha))). }
      * intros Δ' o'.
        apply (transB _ _ (g Δ' (ope_comp o' o) (sem_ren A o' a'))).
        { apply (proj2 (H1 Δ o a a' Ha)). }
        { apply (proj1 (H2 Δ' (ope_comp o' o) (sem_ren A o' a') (sem_ren A o' a')
                          (SEq_ren A o' _ _ (reflrA _ _ _ Ha)))). }
Qed.

Definition SEq_sym T := proj1 (SEq_PER T).
Definition SEq_trans T := proj2 (SEq_PER T).
Lemma SEq_refl_l : forall T {Γ} (a a' : sem T Γ), SEq T a a' -> SEq T a a.
Proof. intros T Γ a a' H. eapply SEq_trans; [ exact H | apply SEq_sym; exact H ]. Qed.
Lemma SEq_refl_r : forall T {Γ} (a a' : sem T Γ), SEq T a a' -> SEq T a' a'.
Proof. intros T Γ a a' H. eapply SEq_trans; [ apply SEq_sym; exact H | exact H ]. Qed.


Lemma sandwich : forall T,
  (forall Γ (u u' : ne Γ T), u = u' -> SEq T (reflect T u) (reflect T u'))
  /\ (forall Γ Δ (o : ope Δ Γ) (u : ne Γ T),
        SEq T (sem_ren T o (reflect T u)) (reflect T (ne_ren o u)))
  /\ (forall Γ (a a' : sem T Γ), SEq T a a' -> reify T a = reify T a')
  /\ (forall Γ Δ (o : ope Δ Γ) (a : sem T Γ),
        SEq T a a -> nf_ren o (reify T a) = reify T (sem_ren T o a)).
Proof.
  induction T as [| A [iA [iiA [iiiA ivA]]] B [iB [iiB [iiiB ivB]]]].
  - split; [| split; [| split ]].
    + intros Γ u u' E. cbn. now rewrite E.
    + intros Γ Δ o u. reflexivity.
    + intros Γ a a' E. cbn in E. subst. reflexivity.
    + intros Γ Δ o a _. cbn. apply reify_nat_natural.
  - split; [| split; [| split ]].
    + (* (i) reflect_SEq, arrow *)
      intros Γ u u' E; subst u'. intros Δ o a a' Ha. split.
      * cbn. rewrite (iiiA _ _ _ Ha). apply iB. reflexivity.
      * intros Δ' o'. cbn.
        eapply (SEq_trans B); [ apply iiB | ].
        apply iB. cbn. f_equal.
        -- now rewrite ne_ren_comp.
        -- rewrite (ivA _ _ o' a (SEq_refl_l A _ _ Ha)). apply iiiA. now apply SEq_ren.
    + (* (ii) reflect_natural, arrow *)
      intros Γ Δ o u Δ0 o0 a a' Ha. split.
      * cbn. rewrite ne_ren_comp, (iiiA _ _ _ Ha). apply iB. reflexivity.
      * intros Δ' o'. cbn.
        eapply (SEq_trans B); [ apply iiB | ].
        apply iB. cbn. f_equal.
        -- rewrite <- ne_ren_comp, <- ne_ren_comp. f_equal. now rewrite ope_comp_assoc.
        -- rewrite (ivA _ _ o' a (SEq_refl_l A _ _ Ha)). apply iiiA. now apply SEq_ren.
    + (* (iii) reify_SEq, arrow *)
      intros Γ a a' H. cbn. f_equal. apply iiiB.
      apply (proj1 (H (A :: Γ) wk (reflect A (nvar vz)) (reflect A (nvar vz)) (iA _ _ _ eq_refl))).
    + (* (iv) reify_natural, arrow *)
      intros Γ Δ o a H. cbn. f_equal.
      rewrite (ivB _ _ (ope_keep o) (a (A :: Γ) wk (reflect A (nvar vz)))
                 (proj1 (H (A::Γ) wk (reflect A (nvar vz)) (reflect A (nvar vz)) (iA _ _ _ eq_refl)))).
      apply iiiB.
      destruct (H (A::Γ) wk (reflect A (nvar vz)) (reflect A (nvar vz)) (iA _ _ _ eq_refl)) as [_ Hsq].
      specialize (Hsq (A::Δ) (ope_keep o)). rewrite ope_comp_keep_wk in Hsq.
      rewrite ope_comp_id_l.
      eapply (SEq_trans B); [ exact Hsq | ].
      apply (proj1 (H (A::Δ) (ope_drop o) (sem_ren A (ope_keep o) (reflect A (nvar vz)))
                        (reflect A (nvar vz)) (iiA _ _ (ope_keep o) (nvar vz)))).
Qed.

Definition reflect_SEq T := proj1 (sandwich T).
Definition reflect_natural T := proj1 (proj2 (sandwich T)).
Definition reify_SEq T := proj1 (proj2 (proj2 (sandwich T))).
Definition reify_natural T := proj2 (proj2 (proj2 (sandwich T))).

Lemma SEq_semrec : forall {Γ T} (z z' : sem T Γ) (s s' : sem (tN ⇒ T ⇒ T) Γ),
    SEq T z z' -> SEq (tN ⇒ T ⇒ T) s s' -> forall n, SEq T (semrec z s n) (semrec z' s' n).
Proof.
  intros Γ T z z' s s' Hz Hs n; induction n as [| n' IH | u].
  - exact Hz.
  - exact (proj1 ((proj1 (Hs Γ ope_id n' n' eq_refl)) Γ ope_id _ _ IH)).
  - cbn [semrec]. rewrite (reify_SEq _ _ _ _ Hz), (reify_SEq _ _ _ _ Hs).
    apply reflect_SEq. reflexivity.
Qed.

Lemma semrec_SEq_ren : forall {Γ Δ T} (o : ope Δ Γ)
    (z1 : sem T Δ) (s1 : sem (tN ⇒ T ⇒ T) Δ) (z2 : sem T Γ) (s2 : sem (tN ⇒ T ⇒ T) Γ) n2,
    SEq T z1 (sem_ren T o z2) ->
    SEq (tN ⇒ T ⇒ T) s1 (sem_ren (tN ⇒ T ⇒ T) o s2) ->
    SEq T z2 z2 -> SEq (tN ⇒ T ⇒ T) s2 s2 ->
    SEq T (semrec z1 s1 (semnat_ren o n2)) (sem_ren T o (semrec z2 s2 n2)).
Proof.
  intros Γ Δ T o z1 s1 z2 s2 n2 Hz1 Hs1 Hz2 Hs2; induction n2 as [| n2' IH | u].
  - exact Hz1.
  - cbn [semnat_ren semrec].
    (* Hg : SEq (T⇒T) (s1 Δ ope_id (semnat_ren o n2')) (sem_ren _ o (s2 Γ ope_id n2')) *)
    assert (Hg : SEq (tN ⇒ T ⇒ T) s1 s1 -> True) by (intros; exact I). clear Hg.
    assert (Hg : SEq (tarr T T) (s1 Δ ope_id (semnat_ren o n2'))
                     (sem_ren (tarr T T) o (s2 Γ ope_id n2'))).
    { eapply (SEq_trans (tarr T T)).
      - exact (proj1 (Hs1 Δ ope_id (semnat_ren o n2') (semnat_ren o n2') eq_refl)).
      - apply (SEq_sym (tarr T T)).
        destruct (Hs2 Γ ope_id n2' n2' eq_refl) as [_ Hsq]. specialize (Hsq Δ o).
        rewrite ope_comp_id_r in Hsq. cbn. rewrite ope_comp_id_l. exact Hsq. }
    (* now: SEq T (g1 Δ ope_id inner_L) (sem_ren o (g2 Γ ope_id inner_R)) *)
    eapply (SEq_trans T).
    + exact (proj1 (Hg Δ ope_id (semrec z1 s1 (semnat_ren o n2'))
                       (sem_ren T o (semrec z2 s2 n2')) IH)).
    + (* (sem_ren o g2) Δ ope_id (sem_ren o inner_R) ~ sem_ren o (g2 Γ ope_id inner_R) *)
      assert (Hg2 : SEq (tarr T T) (s2 Γ ope_id n2') (s2 Γ ope_id n2'))
        by exact (proj1 (Hs2 Γ ope_id n2' n2' eq_refl)).
      apply (SEq_sym T).
      destruct (Hg2 Γ ope_id (semrec z2 s2 n2') (semrec z2 s2 n2')
                    (SEq_semrec z2 z2 s2 s2 Hz2 Hs2 n2')) as [_ Hsq2].
      specialize (Hsq2 Δ o). rewrite ope_comp_id_r in Hsq2.
      cbn. rewrite ope_comp_id_l. exact Hsq2.
  - cbn [semnat_ren semrec].
    eapply (SEq_trans T).
    2:{ apply (SEq_sym T). apply reflect_natural. }
    apply reflect_SEq. cbn [ne_ren]. f_equal.
    + rewrite (reify_SEq T _ _ _ Hz1). symmetry. apply (reify_natural T). exact Hz2.
    + rewrite (reify_SEq (tN ⇒ T ⇒ T) _ _ _ Hs1). symmetry.
      apply (reify_natural (tN ⇒ T ⇒ T)). exact Hs2.
Qed.

Definition SEnv {Δ Γ} (ρ ρ' : Env Δ Γ) : Prop := forall T (x : var Γ T), SEq T (ρ T x) (ρ' T x).
Lemma SEnv_ext : forall {Δ Γ S} (ρ ρ' : Env Δ Γ) (a a' : sem S Δ),
    SEnv ρ ρ' -> SEq S a a' -> SEnv (env_ext ρ a) (env_ext ρ' a').
Proof.
  intros Δ Γ S ρ ρ' a a' Hρ Ha T x. revert T x.
  refine (var_cons_case _ _ _ _ _); [ exact Ha | intros T y; apply Hρ ].
Qed.
Lemma SEnv_ren : forall {Δ Δ' Γ} (o : ope Δ' Δ) (ρ ρ' : Env Δ Γ),
    SEnv ρ ρ' -> SEnv (env_ren o ρ) (env_ren o ρ').
Proof. intros Δ Δ' Γ o ρ ρ' H T x. apply SEq_ren, H. Qed.

