exception TLQKF

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
         | TWrite of var
         | TEq of var
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
  | TVar v
  | TWrite v
  | TEq v -> [v]
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
    | TVar x'
    | TWrite x'
    | TEq x' -> if (x = x') then t else t'
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
  | TVar x
  | TWrite x
  | TEq x -> str = x
  | TPair (t1, t2) -> occurs str t1 || occurs str t2
  | TLoc t' -> occurs str t'
  | TFun (t1, t2) -> occurs str t1 || occurs str t2
  | _ -> false
  
let rec unify: typ -> typ -> subst = fun t t' ->
  match (t, t') with
  | (TInt, TInt)
  | (TBool, TBool)
  | (TString, TString) -> empty_subst
  | (TVar x, TVar y)
  | (TWrite x, TWrite y)
  | (TEq x, TEq y)
  | (TVar x, TWrite y)
  | (TWrite x, TVar y)
  | (TWrite x, TEq y)
  | (TEq x, TWrite y)
  | (TEq x, TVar y)
  | (TVar x, TEq y) -> if x = y then empty_subst else make_subst x t'
  | (TVar x, _) -> if occurs x t' then raise (M.TypeError "Impossible") else make_subst x t'
  | (_, TVar y) -> if occurs y t then raise (M.TypeError "Impossible") else make_subst y t
  | (TPair (t1, t2), TPair (t1', t2')) ->
    let s = unify t1 t1' in
    let s' = unify (s t2) (s t2') in
    s' @@ s
  | (TLoc t1, TLoc t2) -> unify t1 t2
  | (TFun (t1, t2), TFun (t1', t2')) ->
    let s = unify t1 t1' in
    let s' = unify (s t2) (s t2') in
    s' @@ s
  | (TWrite x, TInt)
  | (TWrite x, TBool)
  | (TWrite x, TString)
  | (TEq x, TInt)
  | (TEq x, TBool)
  | (TEq x, TString) -> make_subst x t'
  | (TInt, TWrite y)
  | (TBool, TWrite y)
  | (TString, TWrite y)
  | (TInt, TEq y)
  | (TBool, TEq y)
  | (TString, TEq y) -> make_subst y t
  | (TEq x, TLoc t2) -> if occurs x t' then raise (M.TypeError "Impossible") else make_subst x t'
  | (TLoc t1, TEq y) -> if occurs y t then raise (M.TypeError "Impossible") else make_subst y t
  | (_, _) -> raise (M.TypeError "fail")

let rec expansive: M.exp -> bool = fun exp ->
  match exp with
  | M.CONST const -> false
  | M.VAR x -> false
  | M.FN (x, e) -> false
  | M.APP (e1, e2) -> true
  | M.LET (M.VAL (x, e), e') -> expansive e || expansive e'
  | M.LET (M.REC (f, x, e), e') -> false
  | M.IF (e1, e2, e3) -> expansive e1 || expansive e2 || expansive e3
  | M.BOP (_, e1, e2) -> expansive e1 || expansive e2
  | M.READ -> false
  | M.WRITE e -> expansive e
  | M.MALLOC e -> true
  | M.ASSIGN (e1, e2) -> expansive e1 || expansive e2
  | M.BANG e -> expansive e
  | M.SEQ (e1, e2) -> expansive e1 || expansive e2
  | M.PAIR (e1, e2) -> expansive e1 || expansive e2
  | M.FST e -> expansive e
  | M.SND e -> expansive e

let rec sol: typ_env * M.exp -> (subst * typ) = fun (env, exp) ->
  match exp with
  | M.CONST const ->
   (match const with
    | M.N n -> (empty_subst, TInt)
    | M.B b -> (empty_subst, TBool)
    | M.S str -> (empty_subst, TString))
  | M.VAR x ->
    if (List.mem_assoc x env)
      then
       (let tysch = List.assoc x env in
         (match tysch with
          | SimpleTyp t -> (empty_subst, t)
          | GenTyp (alphas, t) ->
            let newgen = subst_scheme empty_subst (GenTyp (alphas, t)) in
           (match newgen with
            | SimpleTyp t -> raise (M.TypeError "No SimpleTyp")
            | GenTyp (betas, t') -> (empty_subst, t'))))
    else raise (M.TypeError "Unbound variable")
  | M.FN (x, e) ->
    let beta = new_var () in
    let (s, t) = sol ((x, SimpleTyp (TVar beta))::env, e) in
    (s, TFun (s (TVar beta), t))
  | M.APP (e1, e2) ->
    let beta = new_var () in
    let (s, t) = sol (env, e1) in
    let (s', t') = sol (subst_env s env, e2) in
    let s'' = unify (s' t) (TFun (t', TVar beta)) in
    (s'' @@ s' @@ s, s'' (TVar beta))
  | M.LET (M.VAL (x, e), e') ->
    let (s, t) = sol (env, e) in
    if expansive(e)
      then
       (let (s', t') = sol ((x, SimpleTyp t)::(subst_env s env), e') in
        (s' @@ s, t'))
      else
       (let (s', t') = sol ((x, generalize (subst_env s env) t)::(subst_env s env), e') in
        (s' @@ s, t'))
  | M.LET (M.REC (f, x, e), e') ->
    let beta = new_var () in
    let (s, t) = sol ((f, SimpleTyp (TVar beta))::env, M.FN (x, e)) in
    let s' = unify (s (TVar beta)) t in
    if expansive(e)
      then
       (let (s'', t') = sol ((x, SimpleTyp (s' t))::(subst_env s env), e') in
        (s'' @@ s' @@ s, t'))
    else
     (let (s'', t') = sol ((x, generalize (subst_env s env) (s' t))::(subst_env s env), e') in
      (s'' @@ s' @@ s, t'))
  | M.IF (e1, e2, e3) ->
    let (s, t) = sol (env, e1) in
    let s' = unify t TBool in
    let (s1, t1) = sol (subst_env (s' @@ s) env, e2) in
    let (s2, t2) = sol (subst_env (s' @@ s) env, e3) in
    let s'' = unify t1 t2 in
    (s'' @@ s2 @@ s1 @@ s' @@ s, t2)
  | M.BOP (M.EQ, e1, e2) ->
    let (s, t) = sol (env, e1) in
    let (s', t') = sol (subst_env s env, e2) in
    let v = new_var () in
    let s1 = unify (s' t) t' in
    let s2 = unify (s1 t') (TEq v) in
    (s2 @@ s1 @@ s' @@ s, TBool)
  | M.BOP (M.ADD, e1, e2)
  | M.BOP (M.SUB, e1, e2) ->
    let (s, t) = sol (env, e1) in
    let (s', t') = sol (subst_env s env, e2) in
    let s1 = unify (s' t) TInt in
    let s2 = unify (s1 t') TInt in
    (s2 @@ s1 @@ s' @@ s, t')
  | M.BOP (M.AND, e1, e2)
  | M.BOP (M.OR, e1, e2) ->
    let (s, t) = sol (env, e1) in
    let (s', t') = sol (subst_env s env, e2) in
    let s1 = unify (s' t) TBool in
    let s2 = unify t' TBool in
    (s2 @@ s1 @@ s' @@ s, s2 t')
  | M.READ -> (empty_subst, TInt)
  | M.WRITE e ->
    let (s, t) = sol (env, e) in
    let v = new_var () in
    let s' = unify t (TWrite v) in
    (s' @@ s, s' (TWrite v))
  | M.MALLOC e ->
    let (s, t) = sol (env, e) in
    (s, TLoc t)
  | M.ASSIGN (e1, e2) ->
    let (s, t) = sol (env, e1) in
    let (s', t') = sol (subst_env s env, e2) in
    let s'' = unify (s' t) (TLoc t') in
    (s'' @@ s' @@ s, s'' t')
  | M.BANG e ->
    let (s, t) = sol (env, e) in
    let v = new_var () in
    let s' = unify t (TLoc (TVar v)) in
    (s' @@ s, s' (TVar v))
  | M.SEQ (e1, e2) ->
    let (s, t) = sol (env, e1) in
    let (s', t') = sol (subst_env s env, e2) in
    (s' @@ s, t')
  | M.PAIR (e1, e2) ->
    let (s, t) = sol (env, e1) in
    let (s', t') = sol (subst_env s env, e2) in
    (s' @@ s, TPair (s' t, t'))
  | M.FST e ->
    let (s, t) = sol (env, e) in
    let v1 = new_var () in
    let v2 = new_var () in
    let s' = unify t (TPair (TVar v1, TVar v2)) in
    (s' @@ s, s' (TVar v1))
  | M.SND e ->
    let (s, t) = sol (env, e) in
    let v1 = new_var () in
    let v2 = new_var () in
    let s' = unify t (TPair (TVar v1, TVar v2)) in
    (s' @@ s, s' (TVar v2))

let rec typtomtyp: typ -> M.typ = fun t ->
  match t with
  | TInt -> M.TyInt
  | TBool -> M.TyBool
  | TString -> M.TyString
  | TPair (t1, t2) -> M.TyPair (typtomtyp t1, typtomtyp t2)
  | TLoc t' -> M.TyLoc (typtomtyp t')
  | _ -> raise (M.TypeError "Impossible")

(* TODO : Implement this function *)
let check : M.exp -> M.typ = fun e ->
  let (s, t) = sol ([], e) in
  typtomtyp t
