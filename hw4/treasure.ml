exception IMPOSSIBLE

type treasure = StarBox
              | NameBox of string

type key = Bar
         | Node of key * key

type map = End of treasure
         | Branch of map * map
         | Guide of string * map

type ty = BAR
        | VAL of string
        | PAIR of ty * ty

let subst: treasure -> ty -> (ty -> ty) = fun x t ->
  let rec s: ty -> ty = fun t' ->
    match t' with
    | BAR ->
     (match x with
      | StarBox -> t
      | NameBox str -> t')
    | VAL y ->
     (match x with
      | StarBox -> t'
      | NameBox str -> if str = y then t else t')
    | PAIR (t1, t2) -> PAIR (s t1, s t2)

let id = (fun x -> x)

let value = ref 0

let rec occurs: ty -> ty -> bool = fun x tau ->
  match tau with
  | PAIR (t1, t2) -> occurs x t1 | occurs x t2
  | _ -> x = tau

let rec unify: ty -> ty -> (ty -> ty) = fun t1 t2 ->
  match (t1, t2) with
  | (BAR, BAR) -> id
  | (VAL x, tau) ->
    if VAL x = tau then id
    else if not (occurs x tau) then subst x tau
    else raise IMPOSSIBLE
  | (tau, VAL x) -> unify (VAL x) tau
  | (PAIR (a, b), PAIR (c, d)) -> unifypair (a, b) (c, d)
  | (tau, tau') ->
    if tau = tau' then id
    else raise IMPOSSIBLE 
and unifypair (t1, t2) (t1', t2') =
  let s = unify t1 t1' in
  let s' = unify (s t2) (s t2') in
  s' @@ s 

let rec naming: map -> (int * map) list = fun m ->
  match m with
  | End t ->
    value := !value + 1;
    (!value, m)
  | Branch (m1, m2) ->
    value := !value + 1;
    (!value, m) :: naming m1 @ naming m2
  | Guide (str, m') ->
    value := !value + 1;
    (!value, m) :: naming m'

let rec sol: (string * ty) list * map * ty -> (ty -> ty) = fun env m t ->
  match m with
  | End treasure ->
   (match treasure with
    | StarBox -> unify (BAR, t)
    | NameBox str -> 
      if List.mem_assoc str env then unify (t, List.assoc str env))
  | Branch (m1, m2) ->
    let s = sol (env, m1, PAIR (?, t) in
    let s' = sol (List.iter s env, m2, s ?) in
    s' @@ s
  | Guide (str, m') ->
    let s = unify 

let rec getReady: map -> key list = fun m ->
  let explist = naming m in
  match explist with
  
