(** * Completeness of NbE: [defeq t t' -> nf t = nf t']

    !! AXIOM WARNING: the M4 version of this file is the only place in the
    !! development that uses an axiom (functional extensionality, needed to
    !! equate semantic functions). M5 replaces it with a Kripke PER model and
    !! deletes the axiom. No other file may Require this one.

    TODO(M4): contents. *)

From NbE Require Import Syntax OPE NormalForms Model Subst DefEq.
