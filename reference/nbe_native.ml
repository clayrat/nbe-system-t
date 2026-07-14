(* Hand-written, Obj.magic-free NbE for System T — REFERENCE ONLY.

   This is the answer to "how would one write the [sem] part in OCaml without the
   Obj.magic hack?" (contrast the extracted extraction/nbe.ml).

   The hack exists because Coq's [sem : ty -> cxt -> Type] is a *type computed by
   recursion on the type expression* — [sem tN Γ] is [SemNat Γ], [sem (A⇒B) Γ] is
   a Kripke function type — and OCaml has no type-level computation, so extraction
   collapses the whole family to [Obj.t] and casts.

   The native fix: stop treating [sem] as a computed type and make it one ordinary
   variant with a constructor per *shape* of type:

       VNat  for values at base type      (was [sem tN Γ])
       VFun  for values at function type  (was [sem (A⇒B) Γ])

   No type index to erase-and-recover, so no [Obj.magic]. The price is visible
   below as the [assert false] branches: facts the Coq dependent type proved
   statically ("a value at type [A⇒B] is a function", "a [keep] OPE never meets a
   [nil] one") become run-time invariants OCaml cannot check, so the "impossible"
   match arms must be written out. That trade — no casts, but manual dead
   branches — is the whole story. Everything else mirrors theories/Model.v.

   Note what run-time data survives and what does not. Contexts are kept only as
   [ty list]s, and only because [ope_id]/[wk] recurse on them; types survive only
   at [Trec] (its motive, needed when recursion gets stuck) and threaded into
   [reify]/[reflect] (NbE is type-directed). Everything else the extracted code
   carried — the context/type index on every [Tvar]/[Nsuc]/… node — is simply
   gone, because a hand-written version stores only what it actually uses.

   Run it:  ocaml reference/nbe_native.ml *)

(* ===== Syntax ===== *)

type ty = TN | Tarr of ty * ty
type var = Vz | Vs of var

type tm =
  | Tzero
  | Tsuc of tm
  | Trec of ty * tm * tm * tm      (* motive type, z, s, scrutinee *)
  | Tvar of var
  | Tlam of tm
  | Tapp of tm * tm

(* ===== Order-preserving embeddings (contexts erased to lengths of the list) === *)

type ope = Ope_nil | Ope_drop of ope | Ope_keep of ope
type ctx = ty list

let rec ope_id (g : ctx) : ope =
  match g with [] -> Ope_nil | _ :: g' -> Ope_keep (ope_id g')

let wk (g : ctx) : ope = Ope_drop (ope_id g)

let rec ope_comp (o1 : ope) (o2 : ope) : ope =
  match o1, o2 with
  | Ope_nil, o2 -> o2
  | Ope_drop o1', o2 -> Ope_drop (ope_comp o1' o2)
  | Ope_keep o1', Ope_drop o2' -> Ope_drop (ope_comp o1' o2')
  | Ope_keep o1', Ope_keep o2' -> Ope_keep (ope_comp o1' o2')
  | Ope_keep _, Ope_nil -> assert false   (* Coq: ruled out by the OPE indices *)

let rec var_ren (o : ope) (x : var) : var =
  match o, x with
  | Ope_nil, x -> x
  | Ope_drop o', x -> Vs (var_ren o' x)
  | Ope_keep _, Vz -> Vz
  | Ope_keep o', Vs y -> Vs (var_ren o' y)

(* ===== Normal / neutral forms ===== *)

type nf = Nzero | Nsuc of nf | Nne of ne | Nlam of nf
and ne = Nvar of var | Napp of ne * nf | Nrec of nf * nf * ne

let rec nf_ren (o : ope) : nf -> nf = function
  | Nzero -> Nzero
  | Nsuc v -> Nsuc (nf_ren o v)
  | Nne u -> Nne (ne_ren o u)
  | Nlam v -> Nlam (nf_ren (Ope_keep o) v)
and ne_ren (o : ope) : ne -> ne = function
  | Nvar x -> Nvar (var_ren o x)
  | Napp (u, v) -> Napp (ne_ren o u, nf_ren o v)
  | Nrec (z, s, u) -> Nrec (nf_ren o z, nf_ren o s, ne_ren o u)

(* ===== The model: one variant [value] in place of the computed [sem] ===== *)

type value =
  | VNat of snat
  | VFun of (ctx -> ope -> value -> value)   (* Kripke: forall Δ, ope Δ Γ -> … *)
and snat = SZero | SSuc of snat | SNe of ne

let rec snat_ren (o : ope) : snat -> snat = function
  | SZero -> SZero
  | SSuc n -> SSuc (snat_ren o n)
  | SNe u -> SNe (ne_ren o u)

(* sem_ren dispatches on the *value*, not the type — so, unlike the Coq
   [sem_ren], it needs no type argument. *)
let sem_ren (o : ope) : value -> value = function
  | VNat n -> VNat (snat_ren o n)
  | VFun f -> VFun (fun d o' a -> f d (ope_comp o' o) a)

let rec reify_nat : snat -> nf = function
  | SZero -> Nzero
  | SSuc n -> Nsuc (reify_nat n)
  | SNe u -> Nne u

(* reflect needs no context; reify needs it to form [wk] under a binder. *)
let rec reflect (t : ty) (u : ne) : value =
  match t with
  | TN -> VNat (SNe u)
  | Tarr (a, b) ->
    VFun (fun _d o arg -> reflect b (Napp (ne_ren o u, reify a _d arg)))

and reify (t : ty) (g : ctx) (v : value) : nf =
  match t, v with
  | TN, VNat n -> reify_nat n
  | Tarr (a, b), VFun f ->
    Nlam (reify b (a :: g) (f (a :: g) (wk g) (reflect a (Nvar Vz))))
  | _ -> assert false          (* Coq: value shape matches type by construction *)

(* ===== Environments (a list of values, de Bruijn indexed) ===== *)

type env = value list

let rec lookup (env : env) (x : var) : value =
  match x, env with
  | Vz, v :: _ -> v
  | Vs y, _ :: env' -> lookup env' y
  | _ -> assert false

let env_ren (o : ope) (env : env) : env = List.map (sem_ren o) env

let rec semrec (t : ty) (g : ctx) (z : value) (s : value) (n : snat) : value =
  match n with
  | SZero -> z
  | SSuc n' ->
    (match s with
     | VFun f ->
       (match f g (ope_id g) (VNat n') with
        | VFun step -> step g (ope_id g) (semrec t g z s n')
        | _ -> assert false)
     | _ -> assert false)
  | SNe u ->
    reflect t (Nrec (reify t g z, reify (Tarr (TN, Tarr (t, t))) g s, u))

(* eval is NOT type-directed: it recurses on the term only. The one type it needs
   is the [Trec] motive, which the constructor carries. [g] is the target
   context, needed for the identity/weakening OPEs. *)
let rec eval (g : ctx) (env : env) (t : tm) : value =
  match t with
  | Tzero -> VNat SZero
  | Tsuc t' -> (match eval g env t' with VNat n -> VNat (SSuc n) | _ -> assert false)
  | Trec (ty, z, s, n) ->
    (match eval g env n with
     | VNat nn -> semrec ty g (eval g env z) (eval g env s) nn
     | _ -> assert false)
  | Tvar x -> lookup env x
  | Tlam t' -> VFun (fun d o arg -> eval d (arg :: env_ren o env) t')
  | Tapp (r, u) ->
    (match eval g env r with
     | VFun f -> f g (ope_id g) (eval g env u)
     | _ -> assert false)

(* Reflected identity environment: variable i ↦ reflect (nth i g) (Nvar i). *)
let env_id (g : ctx) : env =
  let rec dbvar i = if i = 0 then Vz else Vs (dbvar (i - 1)) in
  List.mapi (fun i t -> reflect t (Nvar (dbvar i))) g

let norm (g : ctx) (t : ty) (tm : tm) : nf = reify t g (eval g (env_id g) tm)

(* ===== Examples (mirroring theories/Tests.v) and a pretty-printer ===== *)

let rec numeral n = if n = 0 then Tzero else Tsuc (numeral (n - 1))
let tadd m n = Trec (TN, m, Tlam (Tlam (Tsuc (Tvar Vz))), n)

let rec var_idx = function Vz -> 0 | Vs y -> 1 + var_idx y
let rec pp_nf n =
  let rec count k = function Nsuc v -> count (k + 1) v | b -> (k, b) in
  match n with
  | Nzero -> "0"
  | Nsuc _ ->
    let k, b = count 0 n in
    (match b with
     | Nzero -> string_of_int k
     | Nne u -> Printf.sprintf "%d + %s" k (pp_ne u)
     | other -> Printf.sprintf "%d + %s" k (pp_nf other))
  | Nne u -> pp_ne u
  | Nlam v -> "\206\187. " ^ pp_nf v
and pp_ne = function
  | Nvar x -> "#" ^ string_of_int (var_idx x)
  | Napp (u, v) -> "(" ^ pp_ne u ^ " " ^ pp_nf v ^ ")"
  | Nrec (z, s, u) -> Printf.sprintf "rec(%s, %s, %s)" (pp_nf z) (pp_nf s) (pp_ne u)

let () =
  let show name g t tm = Printf.printf "  %-10s ~> %s\n" name (pp_nf (norm g t tm)) in
  print_endline "Native (Obj.magic-free) System T normalizer:\n";
  show "2 + 2" [] TN (tadd (numeral 2) (numeral 2));
  show "2 + x" [ TN ] TN (tadd (numeral 2) (Tvar Vz));
  show "\206\187x. f x" [ Tarr (TN, TN) ] (Tarr (TN, TN))
    (Tlam (Tapp (Tvar (Vs Vz), Tvar Vz)));
  show "f" [ Tarr (TN, TN) ] (Tarr (TN, TN)) (Tvar Vz);
  show "K" [] (Tarr (TN, Tarr (TN, TN))) (Tlam (Tlam (Tvar (Vs Vz))))
