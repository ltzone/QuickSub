open Linear_eval
open Defs

let t1 : typ = Nat

let t2 : typ = Nat

let main = print_string (string_of_bool (CompleteSub.sub t1 t2))