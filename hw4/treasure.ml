exception IMPOSSIBLE

type treasure = StarBox
              | NameBox of string

type key = Bar
         | Node of key * key

type map = End of treasure
         | Branch of map * map
         | Guide of string * map

getReady: map -> key list = fun m ->
  match m with
  | End t -> [Bar]
  | Branch (m1, m2) -> []
  | Guide (str, m') -> []
