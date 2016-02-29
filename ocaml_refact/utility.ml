open MetatheoryAtom
open Syntax
open Syntax_ext


let mapi f l =
  let rec r n l =
    match l with
    | [] -> []
    | hd::tl -> (f n hd)::(r (n + 1) tl)
  in
  r 0 l

let foldi f acc l =
  let rec r n acc l =
    match l with
    | [] -> acc
    | hd::tl -> r (n+1) (f n acc hd) tl
  in
  r 0 acc l

let fold2i f acc l1 l2 =
  let rec r n acc l1 l2 =
    match l1, l2 with
    | [], [] -> acc
    | hd1::tl1, hd2::tl2 -> r (n+1) (f n acc hd1 hd2) tl1 tl2
    | _, _ -> failwith "fold2i"
  in
  r 0 acc l1 l2

let lookupAL_opt lst key =
  match key with
  | None ->
     (match lst with
      | (_, result)::_ -> Some result
      | nil -> None)
  | Some key ->
     Alist.lookupAL lst key

     let combine_filter ls rs filter =
       let lrs = List.map (fun l -> List.map (fun r -> (l, r)) rs) ls in
       let lrs = List.flatten lrs in
       let lrs = List.filter (fun (l, r) -> filter l r) lrs in
       lrs

let atom_set_of_list atoms =
  List.fold_left
    (fun atoms atom -> AtomSetImpl.add atom atoms)
    AtomSetImpl.empty
    atoms

let rec get_orig_idx (n : noop_t) (idx : int) : int = 
  if noop_idx_zero_exists n
  then 1 + (get_orig_idx (noop_idx_zero_remove n) idx)
  else if idx = 0
  then 0
  else 1 + (get_orig_idx n (idx - 1))
