# Normalization by Evaluation for Gödel's System T, in Rocq

A small, pedagogically transparent formalization of **Normalization by
Evaluation (NbE)** for Gödel's System T — simply-typed λ-calculus with natural
numbers and primitive recursion — following the structure of Chapter 2 of
Andreas Abel's habilitation thesis *"Normalization by Evaluation: Dependent
Types and Impredicativity"*, but replacing his *liftable terms* (§2.5) with a
**Kripke/presheaf model over order-preserving embeddings (OPEs)**.

Everything is **plain Rocq** (tested with Rocq 9.1 / Coq-style) — no Equations,
MathComp, Autosubst, or any opam package. Both metatheorems are proved
**axiom-free** (no functional extensionality anywhere):

```coq
Theorem soundness    : forall Γ T (t : tm Γ T),    defeq Γ T (nf_emb (norm t)) t.
Theorem completeness : forall Γ T (t t' : tm Γ T), defeq Γ T t t' -> norm t = norm t'.
```

and their combination decides definitional equality by comparing normal forms:

```coq
Theorem defeq_iff_norm : forall Γ T (t t' : tm Γ T), defeq Γ T t t' <-> norm t = norm t'.
```

The normalizer `norm : tm Γ T -> nf Γ T` is **executable and total**, defined
with no proofs: `Compute norm t` runs, and it also extracts to runnable OCaml.

## Building

```sh
coq_makefile -f _CoqProject -o Makefile   # once
make                                       # builds everything
```

`_CoqProject` maps the `theories/` directory to the `NbE` logical prefix
(`-Q theories NbE`) and lists the files in dependency order.

## Guided tour (mapping to Abel Ch. 2)

Read the files in this order; each is a companion to a part of the chapter.

| File | Abel §  | What's in it |
|------|---------|--------------|
| `Syntax.v` | 2.1 (Fig. 2.1) | Intrinsically-typed syntax: `ty`, `cxt`, `var`, `tm`. Ill-typed terms don't exist, so there is no typing judgment. Running examples: `numeral`, `tadd`, `mul_fun`. |
| `OPE.v` | replaces 2.5 / 2.6's `Γ' ≤ Γ` | Order-preserving embeddings: `ope`, `ope_id`, `wk`, `ope_comp`, `var_ren`; the category laws; the `ope_cons_case`/`var_cons_case` inversion principles (axiom-free via decidable equality). |
| `NormalForms.v` | 2.3 (Fig. 2.3) | Mutual `nf`/`ne` with a fully-applied neutral `nrec`; renaming `nf_ren`/`ne_ren`; embeddings `nf_emb`/`ne_emb`. |
| `Model.v` | 2.3 + 2.5 | The Kripke model: `SemNat`, `sem : ty -> cxt -> Type`, `reflect`/`reify`, environments, `semrec`, `eval`, and the normalizer `norm`. This is Abel's §2.5 algorithm with OPEs in place of liftable terms — **no `⊥`, no junk clause**. |
| `Tests.v` | 2.2 | `Compute`-based smoke tests frozen as `reflexivity` (2+2=4, 3×2=6, η, a stuck recursor, `K`, idempotence). |
| `Subst.v` | 2.2 | Parallel substitution `tm_ren`/`subst`/`subst1`, used **only to state** β and η. The normalizer never substitutes. Plus the renaming/substitution fusion lemmas the metatheory needs (funext-free). |
| `DefEq.v` | 2.2 (Fig. 2.2) | Definitional equality `defeq` (β, the two `rec` rules, η, congruences, equivalence), with sanity derivations. |
| `Soundness.v` | 2.6 | The Kripke logical relation `LR`, the sandwich lemmas, the fundamental lemma, and `soundness`. Axiom-free. |
| `PER.v` | (see below) | The Kripke **natural PER** `SEq` used for completeness: congruence + a naturality square, PER laws, the sandwich, `semrec_SEq_ren`, and the environment relation `SEnv`. |
| `Completeness.v` | (see below) | `eval_fund` (fundamental lemma of the PER model), `eval_ren`/`eval_subst` up to `SEq`, `defeq_fund`, and `completeness`. Axiom-free. |
| `Decide.v` | 2.2, M6 | `defeq_iff_norm` and worked decision examples. |

Roughly 2000 lines of Rocq across these files.

## The two design ideas worth knowing

1. **Kripke model over OPEs, not liftable terms.** A semantic function at
   context `Γ` is a *family* of functions, one for every extension `Δ` reachable
   by an embedding `ope Δ Γ`. This eliminates Abel's `⊥` cases and the junk
   clause `↓Nat(û)(Γ) = zero` entirely: every function in the development is
   total with no impossible branches, and reification at function type uses the
   fresh variable as plain `vz` in the context extended by `wk`. Abel credits
   this style to Coquand (his §2.4 survey).

2. **Completeness needs a *natural* PER, and funext does not help.** The original
   plan followed Abel's split — a funext-based completeness first, an axiom-free
   PER later. In practice the funext version turns out to be *impossible* for the
   naive Kripke exponential: the semantic substitution lemma is false as a raw
   equality (its λ-case recurses under an environment extended by an arbitrary
   Kripke argument, and arbitrariness breaks it), and functional extensionality
   does not rescue it. So the relation is unavoidable. `PER.v`'s `SEq` bakes the
   naturality *square* into the arrow clause (a countermodel in its header shows
   why congruence alone is insufficient for System T's `rec`), and completeness
   comes out **axiom-free** in one milestone. This is the design that scales to
   dependent types.

See `PROGRESS.md` for the full milestone log, including this deviation and its
justification.

## Running the normalizer as OCaml

`extraction/` extracts `norm` to OCaml and runs it on the `Tests.v` examples:

```sh
make -C extraction        # coqc-extract, dune-build, run
```

`extraction/DESIGN.md` explains why the extracted code carries `Obj.magic` and
per-node type/context indices (both intrinsic to extracting a type-directed,
intrinsically-typed normalizer), and `reference/nbe_native.ml` is a hand-written,
`Obj.magic`-free version for comparison.
