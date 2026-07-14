# Why the extracted OCaml looks the way it does

The extracted `nbe.ml` has two cosmetic warts: `Obj.magic` casts around semantic
values, and a `cxt`/`ty` field on essentially every constructor of `var`, `tm`,
`nf`, `ne`. This note records why they are there, whether they can be removed,
and the decision we took. Short version: **leave the Coq development as-is; the
warts are the price of staying faithful to Abel Ch. 2, and removing them means a
different algorithm and re-doing the M4/M5 proofs.** The clean, `Obj.magic`-free
hand-written version already lives at `../reference/nbe_native.ml`.

## The two problems have independent root causes

They are not one issue and cannot be fixed together by any clever Coq phrasing.
Each is tied to one of plan.md's core design decisions.

### 1. `Obj.magic` ⟸ the Kripke higher-order semantics

`sem` in `Model.v` is

```coq
Fixpoint sem (T : ty) (Γ : cxt) : Type :=
  match T with
  | tN     => SemNat Γ
  | A ⇒ B  => forall Δ, ope Δ Γ -> sem A Δ -> sem B Δ
  end.
```

The function case puts `sem` to the *left* of an arrow — a **negative
occurrence**. The native OCaml `VFun of (ctx -> ope -> value -> value)` is exactly
that non-positive type, and OCaml accepts it. Coq does not: writing the semantic
values as an honest inductive is rejected by the positivity checker.

```coq
Inductive value : cxt -> ty -> Type :=
| VNat : forall Γ, nat -> value Γ tN
| VFun : forall Γ A B,
    (forall Δ, ope Δ Γ -> value Δ A -> value Δ B) -> value Γ (tarr A B).
(* Error: Non strictly positive occurrence of "value" in
     (forall Δ, ope Δ Γ -> value Δ A -> value Δ B) -> value Γ (tarr A B). *)
```

So Coq *forces* `sem` to be a `Fixpoint` into `Type` (a large elimination), and a
type computed by recursion is exactly what extraction cannot render as an OCaml
type. It sets `type sem = Obj.t` and inserts `Obj.magic` where semantic values
flow. **No restructuring keeps the Kripke higher-order model and removes
`Obj.magic`.** The only escape is to make functions *first-order data* —
defunctionalize them into **closures** (`VClos of env * tm`), which is strictly
positive (Coq accepts it) and extracts with no casts, but is a *different
algorithm* (an abstract machine, not presheaf exponentials) and reverses plan.md
decision #3.

### 2. `cxt`/`ty` on every constructor ⟸ intrinsic typing

The indices come from intrinsically-typed syntax (`tm : cxt -> ty -> Type`,
`var`, `nf`, `ne`). Extraction keeps them because they are informative
`Set`-data, not `Prop` and not type schemes — the only things it erases — and it
does no forcing/redundancy analysis (Agda and Idris 2 would drop them; Coq does
not). `Extraction Implicit` cannot remove them either: the `SafeImplicits` guard
rejects it because the indices are genuinely used at run time (NbE is
type-directed; the OPE formulation recurses on contexts). See the header of
`Extract.v` for that discussion in full.

The only way to make them disappear is **extrinsic** syntax: an untyped
`tm : Type` plus a typing judgment in `Prop`, which extraction erases. That
reverses plan.md decision #1 — and is exactly the switch Abel makes *after* this
chapter (§2.7: intrinsic typing "does not scale... we switch to an extrinsic,
terms-first style").

## The design space is a 2×2

|                       | Kripke functions (`sem`)            | Closures (defunctionalized)          |
| --------------------- | ----------------------------------- | ------------------------------------ |
| **Intrinsic** (now)   | `Obj.magic` + indices ← *we are here* | no magic, still indices              |
| **Extrinsic**         | `Obj.magic`, no indices             | **no magic, no indices** ← `nbe_native.ml` |

- Kill `Obj.magic` ⟺ defunctionalize functions (changes the *semantic model*).
- Kill carried indices ⟺ go extrinsic (changes the *syntax/typing discipline*).

The two wins are independent, each costs a specific model change, and getting
both means the bottom-right cell — which is precisely the architecture of
`../reference/nbe_native.ml` (untyped terms + a closure model). Making
*extraction* produce that means reimplementing it in Coq with a `Prop` typing
relation and proving it — a genuinely different development from Abel Ch. 2.

## Why it is not worth it here

The cost is not just rewriting `Model.v`. The logical relation, the sandwich
lemmas, and the fundamental lemma of **M4/M5 are defined by recursion on the
intrinsic `sem` and over intrinsically-typed terms**. Going extrinsic + closures
redoes every one of those proofs against the new model (now also carrying
well-typedness side conditions that intrinsic typing gives for free). That trades
the plan's priorities — pedagogical clarity, fidelity to Abel — for extraction
quality, and re-spends most of the M4/M5 effort.

## Decision

Keep the Coq development as-is. The extracted `nbe.ml` is a *demonstration that
the verified code runs*, not a shipping artifact; its `Obj.magic`/index noise is
cosmetic and correct. Anyone wanting idiomatic, cast-free OCaml should read (or
run) `../reference/nbe_native.ml` instead.

If clean extraction ever becomes a primary goal, the sensible middle option is
the **intrinsic + closures** cell (top-right): it removes `Obj.magic` for a
moderate `Model.v` rewrite, keeps the indices, and — crucially — keeps intrinsic
typing so the M4/M5 proof architecture survives largely intact. Full
extrinsic + closures is warranted only if extraction quality outranks fidelity to
the chapter.
