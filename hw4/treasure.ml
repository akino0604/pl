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

type substitution = (string * ty) list

let rec occurs: string -> ty -> bool = fun str t ->
  match t with
  | BAR -> false
  | VAL x -> str = x
  | PAIR (t1, t2) -> occurs str t1 || occurs str t2

let rec subst: string -> ty -> ty -> ty = fun x t t' ->
  match t' with
  | BAR -> t'
  | VAL y -> if x = y then t else t'
  | PAIR (t1, t2) -> PAIR (subst x t t1, subst x t t2)

let rec apply: substitution -> ty -> ty = fun s t ->
  match t with
  | BAR -> BAR
  | VAL x -> if List.mem_assoc x s then List.assoc x s else t
  | PAIR (t1, t2) -> apply s t

let rec unify: ty -> ty -> substitution = fun t t' ->
  match (t, t') with
  | (BAR, BAR) -> []
  | (BAR, VAL y) -> [(y, t')]
  | (VAL x, BAR) -> [(x, t)]
  | (VAL x, VAL y) -> if x = y then [] else [(x, t')]
  | (PAIR (t1, t2), VAL y) -> if occurs y t then raise IMPOSSIBLE else [(y, t)]
  | (VAL x, PAIR (t1, t2)) -> if occurs x t' then raise IMPOSSIBLE else [(x, t')]
  | (PAIR (t1, t2), PAIR (t1', t2')) -> 
    let s = unify t1 t1' in
    unify (apply s t2) (apply s t2')
  | (_, _) -> raise IMPOSSIBLE

let value = ref 0
let treasurelist = ref []
let typeenv = ref []

let maptl: substitution -> (string * ty) list -> (string * ty) list = fun sl env ->
  let strl = fst (List.split env) in
  let tyl = snd (List.split env) in
  let ftyl = List.map (apply sl) tyl in
  List.combine strl ftyl

let rec sol: (string * ty) list * map * ty -> substitution = fun (env, m, t) ->
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
    let s' = sol (maptl s env, m2, apply s newty) in
    s'@s
  | Guide (str, m') ->
    let newty1 = VAL (string_of_int !value) in
    let newty2 = VAL (string_of_int (!value + 1)) in
    value := !value + 2;
    let s = unify (PAIR(newty1, newty2)) t in
    typeenv := maptl s env @ [(str, apply s newty1)];
    let s' = sol (maptl s env @ [(str, apply s newty1)], m', apply s newty2) in
    s'@s

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

let init ((): unit): unit =
  value := 0;
  treasurelist := [];
  typeenv := [];
  ()

let getReady: map -> key list = fun m ->
  init ();
  let initty = VAL (string_of_int !value) in
  value := !value + 1;
  let _ = sol ([], m, initty) in
  remove_duplicate (extract !typeenv !treasurelist)
