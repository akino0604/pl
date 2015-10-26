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
  | PAIR (t1, t2) -> PAIR(apply s t1, apply s t2)

let rec replace: string -> string -> substitution -> substitution = fun x y s ->
  match s with
  | [] -> []
  | (str, ty)::tl -> if str = x then (y, ty)::(replace x y tl) else replace x y tl

let rec compose: substitution -> substitution -> substitution = fun s1 s2 ->
  match s1 with
  | [] -> []
  | (str, ty)::tl ->
   (match ty with
    | VAL x ->
      if List.mem_assoc x s2 then (str, List.assoc x s2)::(compose tl s2)
      else (str, ty)::(compose tl s2)
    | _ -> (str, ty)::(compose tl s2))

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
    let s' = unify (apply s t2) (apply s t2') in
    (compose (unifysamekey s' s) s)@(rmsamekey s' s)
  | (_, _) -> raise IMPOSSIBLE
and rmsamekey: substitution -> substitution -> substitution = fun s1 s2 ->
  match s1 with
  | [] -> s2
  | (str, t)::tl ->
    if List.mem_assoc str s2 then rmsamekey tl (List.remove_assoc str s2)
    else rmsamekey tl s2
and unifysamekey: substitution -> substitution -> substitution = fun s1 s2 ->
  match s2 with
  | [] -> s1
  | (str, t)::tl ->
    if List.mem_assoc str s1
      then unify t (List.assoc str s1)
    else
      unifysamekey s1 tl

let value = ref 0
let treasurelist = ref []
let typeenv = ref []

let maptl: substitution -> (string * ty) list -> (string * ty) list = fun sl env ->
  let strl = fst (List.split env) in
  let tyl = snd (List.split env) in
  let ftyl = List.map (apply sl) tyl in
  List.combine strl ftyl

let rec sol: map * ty -> substitution = fun (m, t) ->
  match m with
  | End treasure ->
    treasurelist := treasure::!treasurelist;
   (match treasure with
    | StarBox -> unify BAR t
    | NameBox str -> 
      if (List.mem_assoc str !typeenv) then unify t (List.assoc str !typeenv)
      else
        (typeenv := (unify (VAL str) t) @ !typeenv;
        unify (VAL str) t))
  | Branch (m1, m2) ->
    let newty = VAL (string_of_int !value) in
    value := !value + 1;
    let s = sol (m1, PAIR (newty, t)) in
    typeenv := maptl s !typeenv;
    let s' = sol (m2, apply s newty) in
    (compose (unifysamekey s' s) s)@(rmsamekey s' s)
  | Guide (str, m') ->
    let newty1 = VAL (string_of_int !value) in
    let newty2 = VAL (string_of_int (!value + 1)) in
    value := !value + 2;
    let s = unify (PAIR(newty1, newty2)) t in
    let t = maptl s !typeenv in
    let news = [(str, apply s newty1)] in
    typeenv := (compose (unifysamekey t news) news)@(rmsamekey t news);
    let s' = sol (m', apply s newty2) in
    (compose (unifysamekey s' s) s)@(rmsamekey s' s)

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

let rec tilend: substitution -> unit = fun s ->
  let t1 = !typeenv in
  let t2 = maptl s !typeenv in
  if not (t1 = t2)
    then
      (typeenv := maptl s !typeenv;
      tilend s)

let getReady: map -> key list = fun m ->
  init ();
  let initty = VAL (string_of_int !value) in
  value := !value + 1;
  let s = sol (m, initty) in
  tilend s;
  remove_duplicate (extract !typeenv !treasurelist)
