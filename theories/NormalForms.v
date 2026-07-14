(** * Normal and neutral terms (Abel Ch. 2, Fig. 2.3)

    Two mutually defined families:

      - [nf Γ T] is Abel's [Γ ⊢ v ⇐ T]: a term in normal form. At function type
        a normal form is a λ; at [N] it is [zero], a successor, or a *neutral*.
      - [ne Γ T] is Abel's [Γ ⊢ u ⇒ T]: a *blocked* term — a variable, or a
        blocked elimination of one. §2.3: "an unknown function blocks
        application, an unknown number blocks recursion", which is exactly the
        [napp] and [nrec] constructors.

    Note the neutral recursor [nrec] is fully applied (plan.md §2): its
    scrutinee is a *neutral* natural, its [z] and [s] arguments are already
    normal. And note [nne] embeds neutrals into normal forms only at base type
    [tN] — a neutral of function type must still be η-expanded, which is what
    makes the normal forms η-long. *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import Syntax OPE.

Inductive nf : cxt -> ty -> Type :=
| nzero : forall {Γ}, nf Γ tN
| nsuc  : forall {Γ}, nf Γ tN -> nf Γ tN
| nne   : forall {Γ}, ne Γ tN -> nf Γ tN
| nlam  : forall {Γ S T}, nf (S :: Γ) T -> nf Γ (S ⇒ T)

with ne : cxt -> ty -> Type :=
| nvar  : forall {Γ T}, var Γ T -> ne Γ T
| napp  : forall {Γ S T}, ne Γ (S ⇒ T) -> nf Γ S -> ne Γ T
| nrec  : forall {Γ T}, nf Γ T -> nf Γ (tN ⇒ T ⇒ T) -> ne Γ tN -> ne Γ T.

(** ** Renaming along OPEs

    This is what makes [nf] and [ne] *presheaves* on the category of OPEs, and
    it is the operation that replaces Abel's liftable terms (§2.5): rather than
    a neutral being a function [(Γ ∈ Cxt) → Ne_Γ ⊎ {⊥}] that must cope with
    every context, a neutral lives in one context and is *transported* along an
    embedding into a bigger one. Nothing is ever undefined. *)

Fixpoint nf_ren {Δ Γ T} (o : ope Δ Γ) (v : nf Γ T) {struct v} : nf Δ T :=
  match v in nf G T' return ope Δ G -> nf Δ T' with
  | nzero    => fun _ => nzero
  | nsuc v'  => fun o => nsuc (nf_ren o v')
  | nne u    => fun o => nne (ne_ren o u)
  | nlam v'  => fun o => nlam (nf_ren (ope_keep o) v')
  end o

with ne_ren {Δ Γ T} (o : ope Δ Γ) (u : ne Γ T) {struct u} : ne Δ T :=
  match u in ne G T' return ope Δ G -> ne Δ T' with
  | nvar x        => fun o => nvar (var_ren o x)
  | napp u' v     => fun o => napp (ne_ren o u') (nf_ren o v)
  | nrec vz' vs' u' => fun o => nrec (nf_ren o vz') (nf_ren o vs') (ne_ren o u')
  end o.

(** Going under the binder in [nlam] uses [ope_keep], which is the OPE
    counterpart of "shift the free variables to make room for a new bound one" —
    compare Abel's liftable-term machinery in §2.5, which has to shift free
    variables explicitly. *)

(** ** Embedding back into terms

    Normal forms are terms; this inclusion is what lets us *state* soundness
    ([Γ ⊢ nf_emb (nf t) = t], M4). It is not used by the normalizer. *)

Fixpoint nf_emb {Γ T} (v : nf Γ T) {struct v} : tm Γ T :=
  match v with
  | nzero   => tzero
  | nsuc v' => tsuc (nf_emb v')
  | nne u   => ne_emb u
  | nlam v' => tlam (nf_emb v')
  end

with ne_emb {Γ T} (u : ne Γ T) {struct u} : tm Γ T :=
  match u with
  | nvar x          => tvar x
  | napp u' v       => tapp (ne_emb u') (nf_emb v)
  | nrec vz' vs' u' => trec (nf_emb vz') (nf_emb vs') (ne_emb u')
  end.
