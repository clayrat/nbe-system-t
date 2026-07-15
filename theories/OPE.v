(** * Order-preserving embeddings

    OPEs are our replacement for Abel's context-extension relation [Γ' ≤ Γ]
    (§2.6) and, more importantly, for the *liftable terms* of §2.5: instead of
    making semantic objects total functions on all contexts (with a [⊥] for the
    contexts where they make no sense), we index them by a context and let them
    travel along embeddings [ope Δ Γ]. This is the Kripke/presheaf approach that
    Abel attributes to Coquand in his §2.4 survey.

    An [ope Δ Γ] says: [Γ] is a sub-context of [Δ], preserving order. Reading it
    as a function, it maps each variable of [Γ] to a variable of [Δ]. *)

From Stdlib Require Import List Eqdep_dec.
Import ListNotations.
From NbE Require Import Syntax.

Inductive ope : cxt -> cxt -> Type :=
| ope_nil  : ope [] []
| ope_drop : forall {Δ Γ S}, ope Δ Γ -> ope (S :: Δ) Γ   (* skip a variable of Δ *)
| ope_keep : forall {Δ Γ S}, ope Δ Γ -> ope (S :: Δ) (S :: Γ). (* match them up *)

(** The identity embedding, by recursion on the context. *)
Fixpoint ope_id (Γ : cxt) : ope Γ Γ :=
  match Γ with
  | []      => ope_nil
  | _ :: Γ' => ope_keep (ope_id Γ')
  end.

Arguments ope_id {Γ}.

(** Weakening: [Γ] embeds into [S :: Γ] by dropping the new variable. This is
    the only OPE the normalizer builds by hand — it is what lets reification at
    function type (Model.v) go under a binder while keeping the fresh variable
    as plain [vz]. *)
Definition wk {Γ S} : ope (S :: Γ) Γ := ope_drop ope_id.

(** ** The convoy pattern, once

    Both [ope_comp] and [var_ren] recurse on an OPE and, in the [ope_keep] case,
    must invert a *second* dependent argument ([o2 : ope (S :: Γ0) _], resp.
    [x : var (S :: Γ0) T]) whose context index is known to be a cons. Plain Rocq
    will not push that index equation into the branches on its own, so we use the
    convoy pattern (plan.md, "Pitfall" in M1): the inner [match] abstracts over
    the outer OPE and returns a *function*, with a motive that reconstructs the
    context from the scrutinee's own index via [hd]/[tl].

    The [ope_nil] branches of the inner matches are unreachable (the index is a
    cons, never [[]]) but, pleasantly, they are still fillable with a sensible
    total value — no [False_rect], no junk. *)

(** Composition. The [ope_keep] case is where it is easy to get the equations
    wrong: [keep] followed by [drop] must be a [drop] (the variable [o2] skips is
    skipped overall), while [keep] after [keep] is a [keep].

    The [ope_nil] branch of the *outer* match returns [o2] rather than [ope_nil]:
    there [Δ' = []] already, so [o2 : ope [] Γ] is exactly the result type. *)
Fixpoint ope_comp {Δ' Δ Γ} (o1 : ope Δ' Δ) {struct o1} : ope Δ Γ -> ope Δ' Γ :=
  match o1 in ope D' D return ope D Γ -> ope D' Γ with
  | ope_nil      => fun o2 => o2
  | ope_drop o1' => fun o2 => ope_drop (ope_comp o1' o2)
  | @ope_keep Δ0 _ S0 o1' =>
      fun o2 =>
        (match o2 in ope D G
               return forall Δ1, ope Δ1 (tl D) -> ope (hd S0 D :: Δ1) G with
         | ope_nil      => fun _ o => ope_drop o          (* unreachable *)
         | ope_drop o2' => fun _ o => ope_drop (ope_comp o o2')
         | ope_keep o2' => fun _ o => ope_keep (ope_comp o o2')
         end) Δ0 o1'
  end.

(** The action of an OPE on variables: the "OPE as a function on variables"
    reading, made real. *)
Fixpoint var_ren {Δ Γ T} (o : ope Δ Γ) {struct o} : var Γ T -> var Δ T :=
  match o in ope D G return var G T -> var D T with
  | ope_nil     => fun x => x
  | ope_drop o' => fun x => vs (var_ren o' x)
  | @ope_keep Δ0 _ S0 o' =>
      fun x =>
        (match x in var G T'
               return forall Δ1, ope Δ1 (tl G) -> var (hd S0 G :: Δ1) T' with
         | vz     => fun _ _ => vz
         | vs y   => fun _ o => vs (var_ren o y)
         end) Δ0 o'
  end.

(** ** Small inversion: case analysis on an OPE out of a non-empty context

    The convoy pattern above lets us *define* functions that invert an
    [ope (S :: Δ) Γ]. Proofs need the same power, and there [destruct] is not
    enough: it wants to abstract over the index [S :: Δ], which is a constructor
    application rather than a variable, and fails ("...leads to a term which is
    ill-typed"). [inversion] does case-split, but it leaves the OPE itself
    un-substituted in the goal, so nothing reduces. Agda's pattern matcher does
    this inversion for free — which is why the corresponding Agda proofs are four
    lines — and Coq's [dependent destruction] would too, at the price of the
    [JMeq_eq] axiom.

    We get it axiom-free instead. [cxt = list ty] has decidable equality, so UIP
    on contexts is a *theorem* ([Eqdep_dec.UIP_dec]), not an axiom, and that is
    exactly what is needed to turn the index equation [e : D = S :: Δ] produced
    by the match into a rewrite. Note the statement below mentions no transports;
    they are confined to the proof. [Print Assumptions] on everything downstream
    reports "Closed under the global context".

    This principle is the workhorse for the functoriality lemmas of M4
    ([var_ren]/[nf_ren]/[ne_ren]/[tm_ren] over [ope_comp]), which all need to
    case on an OPE under a [keep]. *)

Definition ty_eq_dec : forall x y : ty, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition cxt_eq_dec : forall x y : cxt, {x = y} + {x <> y}.
Proof. apply list_eq_dec, ty_eq_dec. Defined.

(* Transport of an OPE along an equation between its source contexts. *)
Definition ope_cast {D D' G} (e : D = D') (o : ope D G) : ope D' G :=
  eq_rect D (fun X => ope X G) o D' e.

Lemma ope_cons_case (S : ty) (Δ : cxt) (P : forall G, ope (S :: Δ) G -> Prop)
  (Hdrop : forall G (o : ope Δ G), P G (ope_drop o))
  (Hkeep : forall G (o : ope Δ G), P (S :: G) (ope_keep o))
  : forall G (o : ope (S :: Δ) G), P G o.
Proof.
  intros G o.
  refine ((match o in ope D G' return forall (e : D = S :: Δ), P G' (ope_cast e o) with
           | ope_nil              => fun e => _
           | @ope_drop D0 G0 S0 o' => fun e => _
           | @ope_keep D0 G0 S0 o' => fun e => _
           end) eq_refl).
  - discriminate e.                              (* source [[]] is not a cons *)
  - injection e as e1 e2; subst S0 D0.
    rewrite (UIP_dec cxt_eq_dec e eq_refl). apply Hdrop.
  - injection e as e1 e2; subst S0 D0.
    rewrite (UIP_dec cxt_eq_dec e eq_refl). apply Hkeep.
Qed.

(** ** OPEs form a category

    Contexts and OPEs are a category: these are the laws that make [sem] (M2) a
    presheaf and that M4's renaming-functoriality lemmas rest on (plan.md, risk
    #4: "budget for them up front"). Compare [ope-id-l], [ope-id-r], [ope-assoc]
    in the Agda OPE library. *)

Lemma ope_comp_id_l : forall {Δ Γ} (o : ope Δ Γ), ope_comp ope_id o = o.
Proof. induction o; simpl; try rewrite IHo; reflexivity. Qed.

Lemma ope_comp_id_r : forall {Δ Γ} (o : ope Δ Γ), ope_comp o ope_id = o.
Proof. induction o; simpl; try rewrite IHo; reflexivity. Qed.

(** Associativity. Note where the work is: after [induction o1], the [ope_keep]
    case must case on [o2] (and, under a second [keep], on [o3]) — which is
    precisely what [ope_cons_case] is for. *)
Lemma ope_comp_assoc :
  forall {Δ'' Δ' Δ Γ} (o1 : ope Δ'' Δ') (o2 : ope Δ' Δ) (o3 : ope Δ Γ),
    ope_comp (ope_comp o1 o2) o3 = ope_comp o1 (ope_comp o2 o3).
Proof.
  intros Δ'' Δ' Δ Γ o1. revert Δ Γ.
  induction o1 as [| Δ0 Γ0 S0 o1 IH | Δ0 Γ0 S0 o1 IH]; intros Δ1 Γ1 o2 o3.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - revert Γ1 o3.
    refine (ope_cons_case S0 Γ0
              (fun G o2 => forall Γ1 (o3 : ope G Γ1),
                   ope_comp (ope_comp (ope_keep o1) o2) o3
                   = ope_comp (ope_keep o1) (ope_comp o2 o3)) _ _ Δ1 o2).
    + (* o2 = drop *) intros G o' Γ1 o3. simpl. rewrite IH. reflexivity.
    + (* o2 = keep: now case on o3 *)
      intros G o' Γ1 o3.
      refine (ope_cons_case S0 G
                (fun G2 o3 => ope_comp (ope_comp (ope_keep o1) (ope_keep o')) o3
                              = ope_comp (ope_keep o1) (ope_comp (ope_keep o') o3))
                _ _ Γ1 o3).
      * intros G2 o''. simpl. rewrite IH. reflexivity.
      * intros G2 o''. simpl. rewrite IH. reflexivity.
Qed.

(** ** Variable case principle and [var_ren] functoriality (M4)

    [var_cons_case] is to [var] what [ope_cons_case] is to [ope]: the axiom-free
    inversion of a variable out of a cons context, needed in the proofs below
    (and in [nf_ren]/[tm_ren] functoriality) wherever a [var (S :: Γ) T] must be
    case-split at proof level. Same UIP-via-decidable-equality trick. *)

Definition var_cast {G G' T} (e : G = G') (x : var G T) : var G' T :=
  eq_rect G (fun X => var X T) x G' e.

Lemma var_cons_case (S : ty) (Γ : cxt) (P : forall T, var (S :: Γ) T -> Prop)
  (Hz : P S vz)
  (Hs : forall T (y : var Γ T), P T (vs y))
  : forall T (x : var (S :: Γ) T), P T x.
Proof.
  intros T x.
  refine ((match x in var G T'
                 return forall (e : G = S :: Γ), P T' (var_cast e x) with
           | vz   => fun e => _
           | vs y => fun e => _
           end) eq_refl).
  - injection e as e1 e2; subst. rewrite (UIP_dec cxt_eq_dec e eq_refl). exact Hz.
  - injection e as e1 e2; subst. rewrite (UIP_dec cxt_eq_dec e eq_refl). apply Hs.
Qed.

(** [var_ren] is functorial: it takes [ope_id]/[ope_comp] to identity/composition.
    These are the base cases of the corresponding [tm_ren]/[nf_ren] laws. *)

Lemma var_ren_id : forall {Γ T} (x : var Γ T), var_ren ope_id x = x.
Proof. intros Γ T x. induction x; simpl; [reflexivity | now rewrite IHx]. Qed.

Lemma var_ren_comp :
  forall {Δ Δ' Γ} (o1 : ope Δ Δ') (o2 : ope Δ' Γ) {T} (x : var Γ T),
    var_ren (ope_comp o1 o2) x = var_ren o1 (var_ren o2 x).
Proof.
  intros Δ Δ' Γ o1. revert Γ.
  induction o1 as [| Δ0 Δ'0 S0 o1 IH | Δ0 Δ'0 S0 o1 IH]; intros Γ o2 T x.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - revert T x.
    refine (ope_cons_case S0 Δ'0
              (fun G o2 => forall T (x : var G T),
                   var_ren (ope_comp (ope_keep o1) o2) x
                   = var_ren (ope_keep o1) (var_ren o2 x)) _ _ Γ o2).
    + intros G o2' T x. simpl. rewrite IH. reflexivity.
    + intros G o2' T x.
      revert T x.
      refine (var_cons_case S0 G (fun T x =>
        var_ren (ope_comp (ope_keep o1) (ope_keep o2')) x
        = var_ren (ope_keep o1) (var_ren (ope_keep o2') x)) _ _).
      * reflexivity.
      * intros T0 y. simpl. rewrite IH. reflexivity.
Qed.

(** The weakening naturality square: pushing a [wk] past a [keep] is the same as
    pushing it past nothing — both drop the fresh variable. This is the OPE
    identity the reification-at-arrow case of the soundness sandwich turns on
    ([reify] goes under a binder with [wk]). Both sides equal [ope_drop o]. *)
Lemma ope_comp_keep_wk : forall {Δ Γ S} (o : ope Δ Γ),
    ope_comp (ope_keep (S:=S) o) wk = ope_drop o.
Proof. intros. simpl. now rewrite ope_comp_id_r. Qed.

Lemma ope_comp_wk : forall {Δ Γ S} (o : ope Δ Γ),
    ope_comp (wk (S:=S)) o = ope_drop o.
Proof. intros. simpl. now rewrite ope_comp_id_l. Qed.
