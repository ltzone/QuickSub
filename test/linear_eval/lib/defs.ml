type typ = Nat | Real | Prod of typ * typ | Sum of typ * typ 
         | Fun of typ * typ | Rec of int * typ | Var of int


let rec numVars (t: typ) = match t with 
  | Prod (t1, t2) | Sum (t1, t2) | Fun (t1, t2) -> numVars t1 + numVars t2 
  | Rec (_, t) -> numVars t + 1
  | _ -> 0


let range a b =
    List.init (b - a) ((+) a)


let rev_concat_map f xs = List.fold_right List.rev_append (List.rev_map f xs) []
(* The tail-recursive version of concat map *)

let rec typgenh (depth: int) (max_var: int) : typ list =
  if depth = 0 then 
      ([Nat; Real] @ (List.map (fun i -> Var i) (range 0 max_var)))
  else
    (let st1 = typgenh (depth - 1) max_var in
      let st2 = typgenh (depth - 1) (max_var + 1) in
        let st1_comb = rev_concat_map 
            (fun t1 -> rev_concat_map (fun t2 -> [Prod (t1, t2); Sum (t1, t2); Fun (t1, t2)]) st1) st1 in
        let st2_comb = rev_concat_map (fun t -> [Rec (max_var, t)]) st2 in
        List.rev_append st1_comb st2_comb
    )
    
let typgen (depth: int) = 
    typgenh depth 0

let ascii n = String.make 1 (Char.chr (Char.code 'a' + n))

let rec string_of_typ t = match t with
  | Nat -> "nat"
  | Real -> "real"
  | Prod (t1, t2) -> "(" ^ string_of_typ t1 ^ " * " ^ string_of_typ t2 ^ ")"
  | Sum (t1, t2) -> "(" ^ string_of_typ t1 ^ " + " ^ string_of_typ t2 ^ ")"
  | Fun (t1, t2) -> "(" ^ string_of_typ t1 ^ " -> " ^ string_of_typ t2 ^ ")"
  | Rec (i, t) -> "(μ " ^ ascii i ^ ". " ^ string_of_typ t ^ ")"
  | Var i -> ascii i

let print_typ t = print_string (string_of_typ t)



let t1 = Rec (0, (Fun (Var 0, Nat))) (* μ a. a -> nat *)
let t2 = Rec (0, (Fun (Var 0, Real))) (* μ a. a -> real *)

let t3 = Rec (0, (Fun (Real, Var 0))) (* μ a. real -> a *)
let t4 = Rec (0, (Fun (Nat, Var 0))) (* μ a. nat -> a *)

let t1_unfold = Rec (0, (Fun (Rec (1, (Fun (Var 1, Nat))), Nat))) (* μ a. (μ b. b -> nat) -> nat *)