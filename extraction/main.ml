(* Driver for the extracted System T normalizer.

   Prints the normal forms of the example programs from Extract.v (which mirror
   theories/Tests.v). Each [nf_*] value is produced by the *extracted* [norm]
   running in OCaml, so this is an end-to-end check that the extracted procedure
   works, not just that it compiles.

   Normal forms are shown with de Bruijn indices ([#0] is the innermost bound
   variable), runs of successors collapsed to integers, and [λ.] for binders. *)

open Nbe

let rec var_idx : var -> int = function
  | Vz _ -> 0
  | Vs (_, _, _, y) -> 1 + var_idx y

let rec pp_nf (n : nf) : string =
  let rec count k = function
    | Nsuc (_, v) -> count (k + 1) v
    | base -> (k, base)
  in
  match n with
  | Nzero _ -> "0"
  | Nsuc _ ->
    let k, base = count 0 n in
    (match base with
     | Nzero _ -> string_of_int k
     | Nne (_, u) -> Printf.sprintf "%d + %s" k (pp_ne u)
     | other -> Printf.sprintf "%d + %s" k (pp_nf other))
  | Nne (_, u) -> pp_ne u
  | Nlam (_, _, _, v) -> "λ. " ^ pp_nf v

and pp_ne (u : ne) : string =
  match u with
  | Nvar (_, _, x) -> "#" ^ string_of_int (var_idx x)
  | Napp (_, _, _, u, v) -> "(" ^ pp_ne u ^ " " ^ pp_nf v ^ ")"
  | Nrec (_, _, z, s, u) ->
    Printf.sprintf "rec(%s, %s, %s)" (pp_nf z) (pp_nf s) (pp_ne u)

let () =
  let show name nf expected =
    Printf.printf "  %-10s  ~>  %-22s  (expect %s)\n" name (pp_nf nf) expected
  in
  print_endline "System T normalizer (extracted from Coq), on the Tests.v examples:";
  print_newline ();
  show "2 + 2" nf_add "4";
  show "3 * 2" nf_mul "6";
  show "\206\187x. f x" nf_eta "\206\187. (#1 #0)";
  show "f" nf_f "\206\187. (#1 #0)  [= eta above]";
  show "2 + x" nf_stuck "rec(2, ..., #0)  [stuck]";
  show "K" nf_K "\206\187. \206\187. #1"
