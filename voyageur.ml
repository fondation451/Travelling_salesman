open Printf;;

(*
  ****************************************************************
  ****************************************************************
  ****************************************************************
  ****************************************************************
*)

(* ALGORITHME SIMPLEXE *)

exception Not_Bound;;

(*
  Representation of a linear program :
    Canonical
      min        : cT * x
      subject to : a * x <= b

    Standard
      min        : cT * x
      subject to : a * x = b
                   x >= 0
*)

module MBase =
  Map.Make(struct
    type t = int
    let compare = compare
  end)
;;

type linear_program_format =
  |Canonical
  |Standard
;;

let print_tab data_format tab m n =
  for i = 0 to m-1 do
    for j = 0 to n-1 do
      printf data_format (tab.(i*n + j));
      if j <> n-1 then
        printf ", "
      else
        printf "\n"
    done
  done
;;

let choose_not_in_base tab m n =
  let rec aux out =
    if out >= n then
      None
    else if tab.((m-1) * n + out) > 0.0 then
      Some(out)
    else
      aux (out+1)
  in
  aux 0
;;

let min_ind delta =
  let n = Array.length delta in
  let out = ref 0 in
  for i = 0 to n-1 do
    match delta.(!out), delta.(i) with
    |Some(val_out), Some(val_i) -> if val_i < val_out then out := i
    |None, Some(val_h) -> out := i
    |_ -> ()
  done;
  !out
;;

let fill_simplexe_tab tab a b c =
  let m = Array.length b in
  let n = Array.length c in
  for i = 0 to m-1 do
    for j = 0 to n-1 do
      tab.(i*(n+1) + j) <- a.(i*n + j);
    done;
    tab.(i*(n+1) + n) <- b.(i);
  done;
  for j = 0 to n-1 do
    tab.(m*(n+1) + j) <- c.(j);
  done;
  tab.(m*(n+1) + n) <- 0.0
;;

let pivot tab m n e l =
  let r = tab.(l*n + e) in
  for i = 0 to n-1 do
    tab.(l*n + i) <- tab.(l*n + i) /. r;
  done;
  for i = 0 to m-1 do
    if i <> l then begin
      let k = tab.(i*n + e) in
      for j = 0 to n-1 do
        tab.(i*n + j) <- tab.(i*n + j) -. k *. tab.(l*n + j);
      done
    end
  done
;;

(* Linear Program in Standard Form *)
let simplexe_standard a b c =
  let m = Array.length b + 1 in
  let n = Array.length c + 1 in
  let tab = Array.make ((m+1) * (n+1)) 0.0 in
  fill_simplexe_tab tab a b c;
  let delta = Array.make (m-1) None in
  let x = Array.make (n-1) 0.0 in
  let rec aux compt base =
(*     print_tab "%f" tab m n; *)
    match choose_not_in_base tab m n with
    |Some(e) -> begin
      for i = 0 to m-2 do
        if tab.(i*n + e) > 0.0 then
          delta.(i) <- Some(tab.(i*n + n - 1) /. tab.(i*n + e))
        else
          delta.(i) <- None
      done;
      let l = min_ind delta in
      match delta.(l) with
      |None -> raise Not_Bound
      |_ -> pivot tab m n e l; aux (compt+1) (MBase.add l e base)
    end
    |None ->
      MBase.iter (fun l e -> x.(e) <- tab.(l*n + n - 1)) base;
      Array.to_list x
  in
  aux 0 MBase.empty
;;

let canonical_to_standard a b c =
  let m = Array.length b in
  let n = Array.length c in
  let a' = Array.make (m * (n + m)) 0.0 in
  let b' = Array.copy b in
  let c' = Array.make (n + m) 0.0 in
  for i = 0 to n-1 do
    c'.(i) <- c.(i)
  done;
  for i = 0 to m-1 do
    for j = 0 to n-1 do
      a'.(i*(n+m) + j) <- a.(i*n + j)
    done;
    a'.(i*(n+m) + n + i) <- 1.0
  done;
  (a', b', c')
;;

let simplexe a b c lin_type =
  match lin_type with
  |Canonical ->
    let (a', b', c') = canonical_to_standard a b c in
    simplexe_standard a' b' c'
  |Standard -> simplexe_standard a b c
;;

(* TEST *)

let () =
  let a = [|1.0 ; 3.0 ; 1.0 ;
            -1.0 ; 0.0 ; 3.0 ;
            2.0 ; 4.0 ; -1.0 ;
            1.0 ; 3.0 ; -1.0|] in
  let b = [|3.0 ; 2.0 ; 4.0 ; 2.0|] in
  let c = [|1.0 ; 5.0 ; 1.0|] in
  let x = simplexe a b c Canonical in
  List.iter (fun xi -> printf "%f, " xi) x; printf "\n"
;;



(*
  ****************************************************************
  ****************************************************************
  ****************************************************************
  ****************************************************************
*)

(* ALGORITHME DU VOYAGEUR DE COMMERCE NAIF *)
(* RECHERCHE EXHAUSTIVE *)

let listn_withi n i =
  let rec aux j out =
    if j < 0 then
      out
    else if i <> j then
      aux (j-1) (j::out)
    else
      aux (j-1) out
  in
  aux n []
;;

let tsp_naive_src tab src =
  let rec aux loc dest_l acc_l sol sol_val out out_val =
    match dest_l with
    |[] ->
      if acc_l = [] then
        (List.rev (src::sol), tab.(loc).(src) + sol_val)
      else
        (out, out_val)
    |dest::t ->
      let new_sol = (dest::sol) in
      let new_sol_val = tab.(loc).(dest) + sol_val in
      let new_dest_l = List.rev_append t acc_l in
      let (path, path_val) = aux dest new_dest_l [] new_sol new_sol_val out out_val in
      let new_out, new_out_val =
        if path_val < out_val then
          (path, path_val)
        else
          (out, out_val)
      in
      aux loc t (dest::acc_l) sol sol_val new_out new_out_val
  in
  let max_edge = Array.fold_left (fun acc t -> Array.fold_left (fun acc x -> max acc x) acc t) 0 tab in
  let nb_vertex = Array.length tab in
  let path_val_bound = (nb_vertex + 1) * max_edge in
  let vertex_l = listn_withi (nb_vertex - 1) src in
  aux src vertex_l [] [src] 0 [] path_val_bound
;;

(* TEST *)

let () =
  let tab = [|[|0 ; 5 ; 8 ; 7|] ;
              [|5 ; 0 ; 6 ; 7|] ;
              [|8 ; 6 ; 0 ; 5|] ;
              [|7 ; 7 ; 5 ; 0|] ;|] in
  let (path, path_val) = tsp_naive_src tab 0 in
  List.iter (fun pi -> printf "%d --> " pi) path; printf "\nVal = %d\n" path_val
;;


(*
  ****************************************************************
  ****************************************************************
  ****************************************************************
  ****************************************************************
*)

(* HEURISTIQUE DU VOYAGEUR DE COMMERCE NAIF *)
(* RECHERCHE EXHAUSTIVE *)





















