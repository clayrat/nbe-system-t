(** * The Kripke model and the normalizer (Abel Ch. 2, §2.3 and §2.5)

    This is Abel's §2.5 NbE algorithm with liftable terms replaced by a
    Kripke/presheaf model over OPEs. The one idea that drives everything:

      a semantic function at [Γ] is not a single function, but a *family* of
      functions, one for every context [Δ] reachable from [Γ] by an embedding
      [ope Δ Γ].

    Because a semantic value already knows how to travel to bigger contexts,
    reflection and reification never need Abel's freshness gymnastics: the fresh
    variable in [reify] at function type is literally [vz] in the context
    extended by [wk] (contrast Abel §2.4–2.5, where a fresh name must be invented
    and the whole liftable-term / [⊥] apparatus exists to make that safe). There
    is no [⊥] and no junk clause [↓Nat(û)(Γ) = zero] anywhere below.

    Order of definitions follows plan.md M2. *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import Syntax OPE NormalForms.

Open Scope ty_scope.

(** ** Semantic naturals

    Abel's updated base type (§2.5): a unary natural number that may be *stuck*
    on a neutral. [SNe u] is a natural whose value is blocked on the neutral [u]
    — this is what lets recursion get stuck on an unknown (§2.3, "an unknown
    number blocks recursion") without any [⊥]. [Γ] is a parameter: a [SemNat Γ]
    is a semantic natural *in context [Γ]*. *)

Inductive SemNat (Γ : cxt) : Type :=
| SZero : SemNat Γ
| SSuc  : SemNat Γ -> SemNat Γ
| SNe   : ne Γ tN -> SemNat Γ.

Arguments SZero {Γ}.
Arguments SSuc {Γ}.
Arguments SNe {Γ}.

(** ** The type interpretation, by recursion on the type

    [sem T Γ] is Abel's [[[T]]] refined to "at context [Γ]". At base type it is a
    semantic natural; at function type it is a Kripke function — quantifying over
    all extensions [Δ] of [Γ]. This is a [Fixpoint] returning [Type], not an
    inductive; see plan.md pitfall (a) about universes (we keep [Type]). *)

Fixpoint sem (T : ty) (Γ : cxt) : Type :=
  match T with
  | tN     => SemNat Γ
  | A ⇒ B  => forall Δ, ope Δ Γ -> sem A Δ -> sem B Δ
  end.

(** ** Renaming of semantic values along OPEs

    This is what makes each [sem T] a presheaf. On [SemNat] we rename the
    embedded neutral; at function type we simply *precompose* the stored OPE with
    the incoming one — a Kripke function already carries its own renaming, so
    transporting it is composition, not a traversal. Note [sem_ren] does not
    recurse on itself: the base case is [semnat_ren], the arrow case is
    [ope_comp]. *)

Fixpoint semnat_ren {Δ Γ} (o : ope Δ Γ) (n : SemNat Γ) : SemNat Δ :=
  match n with
  | SZero    => SZero
  | SSuc n'  => SSuc (semnat_ren o n')
  | SNe u    => SNe (ne_ren o u)
  end.

Definition sem_ren (T : ty) {Δ Γ} (o : ope Δ Γ) : sem T Γ -> sem T Δ :=
  match T return sem T Γ -> sem T Δ with
  | tN     => semnat_ren o
  | A ⇒ B  => fun f => fun Δ' (o' : ope Δ' Δ) a => f Δ' (ope_comp o' o) a
  end.

(** ** Reflection and reification (Abel §2.3, the [↑]/[↓] pair)

    Defined by mutual recursion on the *type* (plan.md pitfall (b): the type must
    be the decreasing argument of both, and Coq checks this syntactically — hence
    the [{struct T}] on each and the calls on the subterms [S] / [T0]).

      - [reflect] maps a neutral [u : ne Γ T] to a semantic value. At [tN] a
        neutral is a stuck natural [SNe u]; at [S ⇒ T0] it becomes the Kripke
        function that, given an argument, reifies it and blocks [u] on it —
        Abel's [↑^{S→T}(u)(a) = ↑^T(u (↓^S a))].
      - [reify] maps a semantic value to a normal form. At [tN] it walks the
        [SemNat]; at [S ⇒ T0] it goes under a binder — and here is the payoff:
        the fresh argument is [reflect S (nvar vz)] in the context [S :: Γ]
        reached by [wk]. No freshness side condition, no liftable variable. *)

Fixpoint reify_nat {Γ} (n : SemNat Γ) : nf Γ tN :=
  match n with
  | SZero   => nzero
  | SSuc n' => nsuc (reify_nat n')
  | SNe u   => nne u
  end.

Fixpoint reflect (T : ty) {Γ} (u : ne Γ T) {struct T} : sem T Γ :=
  match T as T0 return ne Γ T0 -> sem T0 Γ with
  | tN     => fun u => SNe u
  | A ⇒ B  => fun u => fun Δ (o : ope Δ Γ) a =>
                reflect B (napp (ne_ren o u) (reify A a))
  end u

with reify (T : ty) {Γ} (v : sem T Γ) {struct T} : nf Γ T :=
  match T as T0 return sem T0 Γ -> nf Γ T0 with
  | tN     => fun v => reify_nat v
  | A ⇒ B  => fun v => nlam (reify B (v (A :: Γ) wk (reflect A (nvar vz))))
  end v.

(** ** Environments

    [Env Δ Γ] valuates the variables of [Γ] by semantic values in [Δ]
    (plan.md §4: environments as functions, not heterogeneous lists — extension
    and lookup are then trivial). *)

Definition Env (Δ Γ : cxt) : Type := forall T, var Γ T -> sem T Δ.

(** Pointwise renaming, and extension by one value (the [tlam] case of [eval]
    builds exactly [env_ext (env_ren o ρ) a]). *)
Definition env_ren {Δ' Δ Γ} (o : ope Δ' Δ) (ρ : Env Δ Γ) : Env Δ' Γ :=
  fun T x => sem_ren T o (ρ T x).

Definition env_ext {Δ Γ S} (ρ : Env Δ Γ) (a : sem S Δ) : Env Δ (S :: Γ) :=
  fun T x =>
    match x in var G T'
          return sem (hd S G) Δ -> Env Δ (tl G) -> sem T' Δ with
    | vz   => fun a _ => a
    | vs y => fun _ ρ' => ρ' _ y
    end a ρ.

(** ** The semantic recursor (Abel §2.5's updated [rec])

    Structural recursion on the [SemNat]. The [SNe] case is where the algorithm
    "produces the code of the recursive function" (§2.3): it reifies [z] and [s]
    and reflects a neutral [nrec], with no [⊥] plumbing. In the [SSuc] case,
    applying the step function [s] to the predecessor and the recursive result
    uses identity OPEs (plan.md: "Mind the identity OPEs when applying [s]"). *)

Fixpoint semrec {T Γ} (z : sem T Γ) (s : sem (tN ⇒ T ⇒ T) Γ)
                (n : SemNat Γ) {struct n} : sem T Γ :=
  match n with
  | SZero   => z
  | SSuc n' => s Γ ope_id n' Γ ope_id (semrec z s n')
  | SNe u   => reflect T (nrec (reify T z) (reify (tN ⇒ T ⇒ T) s) u)
  end.

(** ** Evaluation (Abel §2.1's [[[t]]ρ], now producing NbE values)

    Structural recursion on the term. The [tlam] case is the one that beginners
    get wrong by capturing a stale environment (plan.md risk #3); the fix is to
    *rename* the captured environment to the use-site context with [env_ren o]
    before extending it. The convoy [match t in tm G T0 return Env Δ G -> ...]
    is needed because matching [t] refines [Γ], which appears in [ρ]'s type. *)

Fixpoint eval {Γ T Δ} (t : tm Γ T) (ρ : Env Δ Γ) {struct t} : sem T Δ :=
  match t in tm G T0 return Env Δ G -> sem T0 Δ with
  | tzero      => fun _ => SZero
  | tsuc t'    => fun ρ => SSuc (eval t' ρ)
  | trec z s n => fun ρ => semrec (eval z ρ) (eval s ρ) (eval n ρ)
  | tvar x     => fun ρ => ρ _ x
  | tlam t'    => fun ρ => fun Δ' o a => eval t' (env_ext (env_ren o ρ) a)
  | tapp r u   => fun ρ => (eval r ρ) Δ ope_id (eval u ρ)
  end ρ.

(** ** The normalizer

    The reflected identity environment sends each variable to the reflection of
    itself as a neutral (Abel's [↑^Γ]); normalizing is then "evaluate in it, then
    reify". Note the deliverable in plan.md calls this [nf]; that name is taken
    by the normal-form type (NormalForms.v), so the function is [norm]. It is
    total and proof-free — [Compute norm t] runs. *)

Definition env_id {Γ} : Env Γ Γ := fun T x => reflect T (nvar x).

Definition norm {Γ T} (t : tm Γ T) : nf Γ T := reify T (eval t env_id).

(** * Semantic-nat lemmas for soundness (M4)

    [semnat_ren] is functorial, and [reify_nat] is natural in the OPE. The
    latter is what the base case of the reification sandwich (Soundness.v) needs
    to commute [nf_ren] past [reify_nat]. Both by induction on the [SemNat];
    axiom-free. *)

Lemma semnat_ren_id : forall {Γ} (n : SemNat Γ), semnat_ren ope_id n = n.
Proof.
  intros Γ n; induction n; simpl.
  - reflexivity.
  - now rewrite IHn.
  - now rewrite ne_ren_id.
Qed.

Lemma semnat_ren_comp :
  forall {Δ Δ' Γ} (o1 : ope Δ Δ') (o2 : ope Δ' Γ) (n : SemNat Γ),
    semnat_ren (ope_comp o1 o2) n = semnat_ren o1 (semnat_ren o2 n).
Proof.
  intros Δ Δ' Γ o1 o2 n; induction n; simpl.
  - reflexivity.
  - now rewrite IHn.
  - now rewrite ne_ren_comp.
Qed.

Lemma reify_nat_natural :
  forall {Δ Γ} (o : ope Δ Γ) (n : SemNat Γ),
    nf_ren o (reify_nat n) = reify_nat (semnat_ren o n).
Proof.
  intros Δ Γ o n; induction n; simpl.
  - reflexivity.
  - now rewrite IHn.
  - reflexivity.
Qed.
