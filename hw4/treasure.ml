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

let subst: string -> ty -> (ty -> ty) = fun x t ->
  let rec s: ty -> ty = fun t' ->
    match t' with
    | BAR -> t'
    | VAL y -> if x = y then t else t'
    | PAIR (t1, t2) -> PAIR (s t1, s t2) in
  s

let id = (fun x -> x)

let compfun g f = (fun t -> g (f t))

let rec occurs: ty -> ty -> bool = fun x tau ->
  match tau with
  | PAIR (t1, t2) -> occurs x t1 || occurs x t2
  | _ -> x = tau

let rec unify: ty -> ty -> (ty -> ty) = fun t1 t2 ->
  match (t1, t2) with
  | (BAR, BAR) -> id
  | (VAL x, tau) ->
    if VAL x = tau then id
    else if not (occurs (VAL x) tau) then subst x tau
    else raise IMPOSSIBLE
  | (tau, VAL x) -> unify (VAL x) tau
  | (PAIR (a, b), PAIR (c, d)) -> unifypair (a, b) (c, d)
  | (tau, tau') ->
    if tau = tau' then id
    else raise IMPOSSIBLE 
and unifypair: (ty * ty) -> (ty * ty) -> (ty -> ty) = fun (t1, t2) (t1', t2') ->
  let s = unify t1 t1' in
  let s' = unify (s t2) (s t2') in
  compfun s' s

let value = ref 0
let treasurelist = ref []
let typeenv = ref []

let maptl: (ty-> ty) -> (string * ty) list -> (string * ty) list = fun f env ->
  let strl = fst (List.split env) in
  let tyl = snd (List.split env) in
  let ftyl = List.map f tyl in
  List.combine strl ftyl

let rec sol: (string * ty) list * map * ty -> (ty -> ty) = fun (env, m, t) ->
  match m with
  | End treasure ->
    treasurelist := treasure::!treasurelist;
   (match treasure with
    | StarBox -> unify BAR t
    | NameBox str -> 
      if (List.mem_assoc str env) then unify t (List.assoc str env)
      else
        (typeenv := (str, t)::!typeenv;
        unify t (VAL str)))
  | Branch (m1, m2) ->
    let newty = VAL (string_of_int !value) in
    value := !value + 1;
    let s = sol (env, m1, PAIR (newty, t)) in
    typeenv := maptl s env;
    let s' = sol (maptl s env, m2, s newty) in
    compfun s' s
  | Guide (str, m') ->
    let newty1 = VAL (string_of_int !value) in
    let newty2 = VAL (string_of_int (!value + 1)) in
    value := !value + 1;
    let s = unify (PAIR(newty1, newty2)) t in
    typeenv := maptl s env @ [(str, s newty1)];
    let s' = sol (maptl s env @ [(str, s newty1)], m', s newty2) in
    compfun s' s

let rec tytokey: ty -> key = fun t ->
  match t with
  | BAR -> Bar
  | VAL str -> Bar
  | PAIR (t1, t2) -> Node (tytokey t1, tytokey t2)

let rec extract: (string * ty) list -> treasure list -> key list = fun env trl ->
  match trl with
  | [] -> []
  | hd::tl ->
   (match hd with
    | StarBox -> Bar::(extract env tl)
    | NameBox str ->
      if List.mem_assoc str env then (tytokey (List.assoc str env))::(extract env tl)
      else raise IMPOSSIBLE)

let remove_elt: key -> key list -> key list = fun k kl ->
  let rec go l acc =
    match l with
    | [] -> List.rev acc
    | x::xs when k = x -> go xs acc
    | x::xs -> go xs (x::acc) in
  go kl []

let remove_duplicate: key list -> key list = fun kl ->
  let rec go l acc =
    match l with
    | [] -> List.rev acc
    | x::xs -> go (remove_elt x xs) (x::acc) in
  go kl []

let getReady: map -> key list = fun m ->
  treasurelist := [];
  typeenv := [];
  let initty = VAL (string_of_int !value) in
  value := !value + 1;
  let _ = sol ([], m, initty) in
  remove_duplicate (extract !typeenv !treasurelist)
