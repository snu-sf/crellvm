open MetatheoryAtom
open Dom_list
open Dom_tree

let rec string_of_dtree dtree =
  match dtree with
  | DT_node (a, dtrees) -> a ^ "->(" ^ (string_of_dtrees dtrees) ^  ")"
and string_of_dtrees dtrees =
  match dtrees with
  | DT_nil -> ""
  | DT_cons (dtree, dtrees) -> (string_of_dtree dtree) ^ ", " ^ (string_of_dtrees dtrees)

let rec find_in_dtree a dtree =
  match dtree with
  | DT_node (a', dtrees) ->
     if a = a'
     then Some dtree
     else find_in_dtrees a dtrees
and find_in_dtrees a dtrees =
  match dtrees with
  | DT_nil -> None
  | DT_cons (dtree, dtrees) ->
     (match find_in_dtree a dtree with
      | Some result -> Some result
      | None -> find_in_dtrees a dtrees)

let rec collapse_dtree ?(acc=AtomSetImpl.empty) dtree =
  match dtree with
  | DT_node (a, dtrees) -> collapse_dtrees ~acc:(AtomSetImpl.add a acc) dtrees
and collapse_dtrees ?(acc=AtomSetImpl.empty) dtrees =
  match dtrees with
  | DT_nil -> acc
  | DT_cons (dtree, dtrees) ->
     let acc' = collapse_dtree ~acc:acc dtree in
     let acc'' = collapse_dtrees ~acc:acc' dtrees in
     acc''

let rec bfs_traversal_of_tree (dtree: 'a coq_DTree) : 'a list = 
  match dtree with
  | DT_node (a, dtrees) -> a :: (bfs_traversal_of_trees dtrees)
and bfs_traversal_of_trees (dtrees: 'a coq_DTrees) : 'a list = 
  match dtrees with
  | DT_nil -> []
  | DT_cons (dtree, dtrees) ->
    let l1 = bfs_traversal_of_tree dtree in
    let l2 = bfs_traversal_of_trees dtrees in
    List.append l1 l2

let dom_by a dtree =
  let dtree =
    match find_in_dtree a dtree with
    | None -> failwith "translateHints sdom_by"
    | Some dtree -> dtree
  in
  let result = collapse_dtree dtree in
  result
