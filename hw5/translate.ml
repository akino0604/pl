exception Error of string
(*
 * SNU 4190.310 Programming Languages 
 * K-- to SM5 translator skeleton code
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

open K
open Sm5
module Translator = struct

  (* TODO : complete this function  *)
  let rec trans : K.program -> Sm5.command = function
    | K.NUM i -> [Sm5.PUSH (Sm5.Val (Sm5.Z i))]
    | K.TRUE -> [Sm5.PUSH (Sm5.Val (Sm5.B true))]
    | K.FALSE -> [Sm5.PUSH (Sm5.Val (Sm5.B false))]
    | K.UNIT -> [Sm5.PUSH (Sm5.Val (Sm5.Unit))]
    | K.VAR x -> [Sm5.PUSH (Sm5.Id x); Sm5.LOAD]
    | K.ADD (e1, e2) -> trans e1 @ trans e2 @ [Sm5.ADD]
    | K.SUB (e1, e2) -> trans e1 @ trans e2 @ [Sm5.SUB]
    | K.MUL (e1, e2) -> trans e1 @ trans e2 @ [Sm5.MUL]
    | K.DIV (e1, e2) -> trans e1 @ trans e2 @ [Sm5.DIV]
    | K.EQUAL (e1, e2) -> trans e1 @ trans e2 @ [Sm5.EQ]
    | K.LESS (e1, e2) -> trans e1 @ trans e2 @ [Sm5.LESS]
    | K.NOT e -> trans e @ [Sm5.NOT]
    | K.ASSIGN (x, e) -> trans e @ [Sm5.PUSH (Sm5.Id x); Sm5.STORE; Sm5.PUSH (Sm5.Id x); Sm5.LOAD]
    | K.SEQ (e1, e2) -> trans e1 @ [Sm5.POP] @ trans e2
    | K.IF (e1, e2, e3) -> trans e1 @ [Sm5.JTR (trans e2, trans e3)]
    | K.WHILE (e1, e2) ->
      let w = K.LETF ("func!", "@", K.IF (K.VAR "@", K.SEQ (e2, K.CALLV ("func!", e1)), K.UNIT), K.CALLV ("func!", e1)) in
      trans w
    | K.FOR (x, e1, e2, e3) ->
      let f = K.LETF ("func!", "@",
                      K.IF (K.LESS (K.VAR x, K.VAR "@"),
                            K.SEQ (K.SEQ (e3, K.ASSIGN (x, K.ADD (K.VAR x, K.NUM 1))),
                                   K.CALLV ("func!", K.VAR "@")),
                            K.SEQ (e3, K.UNIT)),
                      K.SEQ (K.ASSIGN (x, e1), K.CALLV ("func!", e2))) in
      trans f
    | K.LETV (x, e1, e2) ->
      trans e1 @ [Sm5.MALLOC; Sm5.BIND x; Sm5.PUSH (Sm5.Id x); Sm5.STORE] @
      trans e2 @ [Sm5.UNBIND; Sm5.POP]
    | K.LETF (f, x, e1, e2) ->
      let body = [Sm5.BIND f] @ trans e1 @ [Sm5.UNBIND; Sm5.POP] in
      [Sm5.PUSH (Sm5.Fn (x, body)); Sm5.BIND f] @ trans e2 @ [Sm5.UNBIND; Sm5.POP]
    | K.CALLV (f, e) ->
      [Sm5.PUSH (Sm5.Id f); Sm5.PUSH (Sm5.Id f)] @ trans e @ [Sm5.MALLOC; Sm5.CALL]
    | K.CALLR (f, x) ->
      [Sm5.PUSH (Sm5.Id f); Sm5.PUSH (Sm5.Id f); Sm5.PUSH (Sm5.Id x); Sm5.LOAD; Sm5.PUSH (Sm5.Id x); Sm5.CALL]
    | K.READ x -> [Sm5.GET; Sm5.PUSH (Sm5.Id x); Sm5.STORE; Sm5.PUSH (Sm5.Id x); Sm5.LOAD]
    | K.WRITE e -> trans e @ [Sm5.MALLOC; Sm5.BIND "#"; Sm5.PUSH (Sm5.Id "#"); Sm5.STORE; Sm5.PUSH (Sm5.Id "#"); Sm5.LOAD; Sm5.PUT; Sm5.PUSH (Sm5.Id "#"); Sm5.LOAD; Sm5.UNBIND; Sm5.POP]
end
