(*
 * SNU 4190.310 Programming Languages 
 * Continuation Passing Style Conversion Skeleton
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

open M0

let count = ref 0

let new_name () = 
  let _ = count := !count + 1 in
  "x_" ^ (string_of_int !count)

let rec alpha_conv exp subs = 
  match exp with
  | Num n -> Num n
  | Var x -> (try Var (List.assoc x subs) with Not_found -> Var x)
  | Fn (x, e) ->
    let x' = new_name () in
    let subs' = (x, x') :: subs in
    Fn (x', alpha_conv e subs')
  | App (e1, e2) -> App (alpha_conv e1 subs, alpha_conv e2 subs)
  | Rec (f, x, e) -> 
    let x' = new_name () in
    let f' = new_name () in
    let subs' = (f, f') :: (x, x') :: subs in
    Rec (f', x', alpha_conv e subs')
  | Ifz (e1, e2, e3) -> 
    Ifz (alpha_conv e1 subs, alpha_conv e2 subs, alpha_conv e3 subs)
  | Add (e1, e2) -> Add (alpha_conv e1 subs, alpha_conv e2 subs)
  | Pair (e1, e2) -> Pair (alpha_conv e1 subs, alpha_conv e2 subs)
  | Fst e -> Fst (alpha_conv e subs)
  | Snd e -> Snd (alpha_conv e subs)

(* TODO : Complete this function *)
let rec cps' exp = 
  let k = new_name () in
  match exp with
  (* Constant expressions *)
  | Num n -> Fn (k, Num n)
  | Var x -> Fn (k, Var x)
  | Fn (x, e) -> Fn (k, APP(Var k, Fn(x, cps' e)))
  | Rec (f, x, e) -> Fn (k, APP(Var k, Rec(f, x, cps' e)))
  (* Non constant expressions *)
  | App (e1, e2) ->
    let f = new_name () in
    let v = new_name () in
    Fn (k, APP (cps' e1, Fn (f, APP (cps' e2, Fn (v, APP (Var k, APP (Var f, Var v)))))))
  | Ifz (e1, e2, e3) -> Fn (k, )
  | Add (e1, e2) ->
    let v1 = new_name () in
    let v2 = new_name () in
    Fn (k, App (cps' e1, Fn (v1, App (cps' e2, Fn (v2, App (Var k, Add (Var v1, Var v2)))))))
  | Pair (e1, e2) ->
    let v = new_name () in
    let w = new_name () in
    Fn (k, APP (cps' e1, Fn (v, APP (cps' e2, Fn (w, APP (Var k, Pair (Var v, Var w)))))))
  | Fst e ->
    let v = new_name () in
    Fn (k, APP (cps' e, APP (Fn v, APP (Var k, Fst v))))
  | Snd e ->
    let v = new_name () in
    Fn (k, APP (cps' e, APP (Fn v, APP (Var k, Snd v))))

let cps exp = cps' (alpha_conv exp [])

