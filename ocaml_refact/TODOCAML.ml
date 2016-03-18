let flip f = fun x y -> f y x

let rec filter_map f l =
  match l with
  | [] -> []
  | x::l ->
     match f x with
     | Some y -> y::(filter_map f l)
     | None -> filter_map f l

let findi p l =
  let rec r l idx = 
  match l with
  | [] -> failwith "List.findi"
  | x::l ->
     if p idx x
     then (idx, x)
     else r l (idx + 1)
  in
  r l 0

let get o =
  match o with
  | None -> failwith "Option.get None"
  | Some x -> x

let list_to_string (l:char list) : string =
  String.init (List.length l) (List.nth l)
