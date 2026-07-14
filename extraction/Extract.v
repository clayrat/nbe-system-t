(** * Extraction of the NbE procedure to OCaml (plan.md M2a)

    The computational core (Model.v: eval, reflect/reify, semrec, norm) is total
    and proof-free, so it extracts to runnable OCaml. This is a standalone
    driver, NOT part of the `make` build (not in _CoqProject). Regenerate with:

        coqc -Q ../theories NbE Extract.v      (run from the extraction/ dir)

    which writes nbe.ml / nbe.mli here. Later milestones (M3+) only add proofs
    and never touch the extracted definitions, so this output is stable.

    Because [sem : ty -> cxt -> Type] is a large elimination (a Fixpoint into
    Type), extraction cannot give semantic values an OCaml type: it sets
    [type sem = Obj.t] and inserts [Obj.magic] where they flow. This is expected
    and harmless — the algorithm is still evaluated by OCaml normally. A native,
    [Obj.magic]-free rewrite is in reference/nbe_native.ml: it replaces the
    computed type family [sem] with one ordinary variant [value = VNat | VFun],
    at the cost of an [assert false] in the branches the dependent type used to
    rule out (value shape vs. type). See its header for the full discussion.

    Two other artefacts of extracting dependently typed code, both benign:

    - The variant constructors of [var]/[tm]/[nf]/[ne] carry their context/type
      *indices* as ordinary fields (e.g. [Nsuc of cxt * nf], [Tvar of cxt * ty *
      var]). They are NOT erased because they are informative data — inhabitants
      of the Set-inductives [ty] and [list ty] — not [Prop] content and not type
      schemes, which are the only things Coq extraction drops. Coq performs no
      forcing / redundancy analysis (unlike Agda or Idris 2), so an index that is
      recoverable from an erased type is still kept.

      Nor can we simply erase them with [Extraction Implicit]: the [SafeImplicits]
      guard rejects it ("An implicit occurs after extraction : ... (S) of vs"),
      because these indices are genuinely used at run time. NbE is *type-directed*
      — [reflect]/[reify] branch on the type, [eval]'s lambda case needs the
      domain type to build the context it later reifies under — and the OPE
      formulation additionally recurses on the *context* ([ope_id]/[wk] in
      [reify] at arrow). So the data is load-bearing, not phantom; there is only
      a redundant second copy (e.g. [eval] both receives its type argument and
      re-reads it from the constructor) that extraction cannot prove dead and
      dedupe.

    - [nat] is mapped to native [int] below, purely for readable numeral output. *)

From NbE Require Import Syntax OPE NormalForms Model.
From Stdlib Require Import List Extraction.
Import ListNotations.

Extraction Language OCaml.

(* Map Coq's [nat] onto native OCaml ints so numerals read as ordinary integers
   on the OCaml side. [numeral]/[reify_nat] build/consume unary [nat]; whole
   numbers that survive normalization then print as [int]s. *)
Extract Inductive nat => "int" [ "0" "(fun n -> n + 1)" ]
  "(fun zero succ n -> if n = 0 then zero () else succ (n - 1))".

Open Scope ty_scope.

(** Example programs, defined here (with concrete contexts and types) so the
    OCaml driver never has to hand-build de Bruijn terms. These mirror Tests.v.
    We export the *normalized* results as [nf] constants: OCaml just prints them.
    (They are thunks in the extracted code — OCaml runs the normalizer at module
    load, so this genuinely exercises the extracted [norm].) *)

Definition ex_add   : tm [] tN               := tadd (numeral 2) (numeral 2).
Definition ex_mul   : tm [] tN               := tmul (numeral 3) (numeral 2).
Definition ex_eta   : tm [tN ⇒ tN] (tN ⇒ tN) := tlam (tapp (tvar (vs vz)) (tvar vz)).
Definition ex_f     : tm [tN ⇒ tN] (tN ⇒ tN) := tvar vz.
Definition ex_stuck : tm [tN] tN             := tadd (numeral 2) (tvar vz).
Definition ex_K     : tm [] (tN ⇒ tN ⇒ tN)   := tlam (tlam (tvar (vs vz))).

Definition nf_add   := norm ex_add.
Definition nf_mul   := norm ex_mul.
Definition nf_eta   := norm ex_eta.
Definition nf_f     := norm ex_f.
Definition nf_stuck := norm ex_stuck.
Definition nf_K     := norm ex_K.

Set Extraction Output Directory ".".

(* Export the normalizer and the numeral/arithmetic builders as a usable little
   library, plus the precomputed example results the driver prints. *)
Extraction "nbe.ml"
  norm nf_emb
  numeral tadd tmul add_fun mul_fun
  nf_add nf_mul nf_eta nf_f nf_stuck nf_K.
