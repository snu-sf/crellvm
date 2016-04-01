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

let int_list_max l default =
  List.fold_left (fun s i -> if(s < i) then i else s) default l

let list_zip ls default =
  let rec fill_list_until i l =
    if(List.length l < i)
    then fill_list_until i (l @ [default])
    else let _ = assert(List.length l == i) in l in
  let len = int_list_max (List.map (fun l -> List.length l) ls) 0 in
  let ls = List.map (fill_list_until len) ls in
  let _ = List.iter (fun l -> assert(List.length l = len)) in
  let rec pile ls i =
    if(i == 0)
    then [] (* should not be [[]] *)
    else (List.map List.hd ls) :: pile (List.map List.tl ls) (i-1) in
  pile ls len
