(*
 * SNU 4190.310 Programming Languages 2015 Fall
 * Type Checker Skeleton
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

open M

type var = string

type typ = TInt
         | TBool
         | TString
         | TPair of typ * typ
         | TLoc of typ
         | TFun of typ * typ
         | TVar of var
(* Modify, or add more if needed *)

type typ_scheme = SimpleTyp of typ 
                | GenTyp of (var list * typ)

type typ_env = (M.id * typ_scheme) list

let count = ref 0 

let new_var () = 
  let _ = count := !count +1 in
  "x_" ^ (string_of_int !count)

(* Definitions related to free type variable *)

let union_ftv ftv_1 ftv_2 = 
  let ftv_1' = List.filter (fun v -> not (List.mem v ftv_2)) ftv_1 in
  ftv_1' @ ftv_2
  
let sub_ftv ftv_1 ftv_2 =
  List.filter (fun v -> not (List.mem v ftv_2)) ftv_1

let rec ftv_of_typ : typ -> var list = function
  | TPair (t1, t2) -> union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TLoc t -> ftv_of_typ t
  | TFun (t1, t2) ->  union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TVar v -> [v]
  | _ -> []

let ftv_of_scheme : typ_scheme -> var list = function
  | SimpleTyp t -> ftv_of_typ t
  | GenTyp (alphas, t) -> sub_ftv (ftv_of_typ t) alphas 

let ftv_of_env : typ_env -> var list = fun tyenv ->
  List.fold_left 
    (fun acc_ftv (id, tyscm) -> union_ftv acc_ftv (ftv_of_scheme tyscm))
    [] tyenv 

(* Generalize given type into a type scheme *)
let generalize : typ_env -> typ -> typ_scheme = fun tyenv t ->
  let env_ftv = ftv_of_env tyenv in
  let typ_ftv = ftv_of_typ t in
  let ftv = sub_ftv typ_ftv env_ftv in
  if List.length ftv = 0 then
    SimpleTyp t
  else
    GenTyp(ftv, t)

(* Definitions related to substitution *)

type subst = typ -> typ

let empty_subst : subst = fun t -> t

let make_subst : var -> typ -> subst = fun x t ->
  let rec subs t' = 
    match t' with
    | TVar x' -> if (x = x') then t else t'
    | TPair (t1, t2) -> TPair (subs t1, subs t2)
    | TLoc t'' -> TLoc (subs t'')
    | TFun (t1, t2) -> TFun (subs t1, subs t2)
    | _ -> t'
  in subs

let (@@) s1 s2 = (fun t -> s1 (s2 t)) (* substitution composition *)

let subst_scheme : subst -> typ_scheme -> typ_scheme = fun subs tyscm ->
  match tyscm with
  | SimpleTyp t -> SimpleTyp (subs t)
  | GenTyp (alphas, t) ->
    (* S (\all a.t) = \all b.S{a->b}t  (where b is new variable) *)
    let betas = List.map (fun _ -> new_var()) alphas in
    let s' =
      List.fold_left2
        (fun acc_subst alpha beta -> make_subst alpha (TVar beta) @@ acc_subst)
        empty_subst alphas betas
    in
    GenTyp (betas, subs (s' t))

let subst_env : subst -> typ_env -> typ_env = fun subs tyenv ->
  List.map (fun (x, tyscm) -> (x, subst_scheme subs tyscm)) tyenv

let rec occurs: string -> typ -> bool = fun str t ->
  match t with
  | TVal x -> str = x
  | TPair (t1, t2) -> occurs str t1 || occurs str t2
  | TLoc t' -> occurs str t'
  | TFun (t1, t2) -> occurs str t1 || occurs str t2
  | _ -> false

let rec apply: subst -> typ -> typ = fun s t ->
  match t with
  | TVal x -> if List.mem_assoc x s then List.assoc x s else t
  | TPair (t1, t2) -> TPair (apply s t1, apply s t2)
  | TLoc t' -> TLoc (apply s t')
  | TFun (t1, t2) -> TFun (apply s t1, apply s t2)
  | _ -> t
  
let rec unify: typ -> typ -> subst = fun t t' ->
  match (t, t') with
  | (TVal x, TVal y) -> if x = y then empty_subst else make_subst x t'
  | (TVal x, TPair (t1, t2))
  | (TVal x, TLoc t'')
  | (TVal x, TFun (t1, t2)) -> if occurs x t' then raise (M.TypeError "Impossible") else make_subst x t'
  | (TPair (t1, t2), TVal y)
  | (TLoc t'', TVal y)
  | (TFun (t1, t2), TVal y) -> if occurs y t then raise (M.TypeError "Impossible") else make_subst y t
  | (TVal x, _) -> make_subst x t
  | (_, TVal y) -> make_subst y t'
  | (TPair (t1, t2), TPair (t1', t2')) ->
    let s = unify t1 t1' in
    let s' = unify t2 t2' in
    ((@@) s' s)
  | (TLoc t1, TLoc t2) -> unify t1 t2
  | (TFun (t1, t2), TFun (t1', t2')) ->
    let s = unify t1 t1' in
    let s' = unify t2 t2' in
    ((@@) s' s)
  | (TPair (t1, t2), _)
  | (TLoc t'', _)
  | (TFun (t1, t2), _)
  | (_, TPair (t1, t2))
  | (_, TLoc t'')
  | (_, TFun (t1, t2)) -> raise (M.TypeError "Impossible")
  | (_, _) -> empty_subst

let rec expansive: M.exp -> bool = fun exp ->
  match exp with
  | CONST const -> false
  | VAR x -> false
  | FN (x, e) -> false
  | APP (e1, e2) -> true
  | LET (VAL (x, e), e') -> expansive e || expansive e'
  | LET (REC (f, x, e)) -> false
  | IF (e1, e2, e3) -> expansive e1 || expansive e2 || expansive e3
  | BOP (_, e1, e2) -> expansive e1 || expansive e2
  | READ -> false
  | WRITE e -> expansive e
  | MALLOC e -> true
  | ASSIGN (e1, e2) -> expansive e1 || expansive e2
  | BANG e -> expansive e
  | SEQ (e1, e2) -> expansive e1 || expansive e2
  | PAIR (e1, e2) -> expansive e1 || expansive e2
  | FST e -> expansive e
  | SND e -> expansive e

let rec solve: typ_env * M.exp -> (subst * typ) = fun (env, exp) ->
  match exp with
  | CONST const ->
   (match const with
    | N n -> (empty_subst, SimpleTyp TInt)
    | B b -> (empty_subst, SimpleTyp TBool)
    | S str -> (empty_subst, SimpleTyp TString))
  | VAR x ->
    if (List.mem_assoc x typ_env)
      then
       (let tysch = List.assoc x typ_env in
         (match tysch with
          | SimpleTyp t -> (empty_subst, t)
          | Gentyp (alphas * t) ->
            let newgen = subst_scheme empty_subs (Gentyp (alphas * t)) in
           (match newgen with
            | SimpleTyp t -> raise (M.TypeError "No SimpleTyp")
            | Gentyp (betas * t') -> (empty_subst, t'))))
    else
      (empty_subst, (x, (* ahffk tlqkf *) ))
  | FN (x, e) ->
    let beta = TVar new_var () in
    let (s, t) = solve ((x, beta)::env, exp) in
    (s, TFun (s beta, t))
  | APP (e1, e2) ->
    let beta = TVar new_var () in
    let (s, t) = solve (env, e1) in
    let (s', t') = solve (subst_env s env, e2) in
    let s'' = unify (s' t, TFun (t', beta)) in
    (((@@) ((@@) s'' s') s), s'' beta)
  | LET (VAL (x, e), e') ->
    let (s, t) = solve (env, e) in
    let (s', t') = solve ((x, (generalize (subst_env s env) t))::(subst_env s env), e') in
    ((@@) s' s, t')
  | LET (REC (f, x, e), e') ->
    let beta = TVar new_var () in
    let (s, t) = solve ((f, SimpleTyp beta)::env, FN (x, e)) in
    let s' = unify (s beta, t) in
    ((@@) s' s, s' t)
  | IF (e1, e2, e3)
  | BOP (_, e1, e2)
  | READ -> (empty_subst, SimpleTyp TInt)
  | WRITE e
  | MALLOC e
  | ASSIGN (e1, e2)
  | BANG e
  | SEQ (e1, e2)
  | PAIR (e1, e2)
  | FST e
  | SND e

(* TODO : Implement this function *)
let check : M.exp -> M.typ =
  raise (M.TypeError "Type Checker Unimplemented")
