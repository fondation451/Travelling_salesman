open Printf;;

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

let pivot nbase base a b c nu l e =
	printf "Pivot\n"; flush stdout;
	let m = Array.length b in
	let n = Array.length c in
	let a' = Array.make (m*n) 0 in
	let b' = Array.make m 0 in
	let c' = Array.make n 0 in
	b'.(e) <- b.(l)/a.(l*n + e);
	List.iter (fun i -> if i <> e then a'.(e*n + i) <- a.(l*n + i)/a.(l*n + e)) nbase;
	a'.(e*n + l) <- 1/a.(l*n + e);
	List.iter
	  (fun i ->
	  	if i <> l then begin
	  	  b'.(i) <- b.(i) - a.(i*n + e) * b'.(e);
	      List.iter
	        (fun j ->
	        	if j <> e then
	        	  a'.(i*n + j) <- a.(i*n + j) - a.(i*n + e)*a'.(e*n + j))
	        nbase;
	      a'.(i*n + l) <- -1 * a.(i*n + e) * a'.(e*n + l)
	    end)
	  base;
	let nu' = nu + c.(e)*b'.(e) in
	List.iter (fun i -> if i <> e then c'.(i) <- c.(i) - c.(e)*a'.(e*n + i)) nbase;
	c'.(l) <- -1 * c.(e) * a'.(e*n + l);
	let nbase' = l::(List.filter (fun x -> x <> e) nbase) in
	let base' = e::(List.filter (fun x -> x <> l) base) in
	(nbase', base', a', b', c', nu')
;;

let rec choose_nbase nbase c =
	printf "Choose_nbase\n"; flush stdout;
	match nbase with
	|[] -> None
	|h::t ->
	  if c.(h) > 0 then
	    Some(h)
	  else
	    choose_nbase t c
;;

let min_ind base delta =
	printf "Min_ind\n"; flush stdout;
	let rec aux base out =
    match base with
    |[] -> out
    |h::t -> begin
    	match delta.(out), delta.(h) with
    	|Some(val_out), Some(val_h) ->
    		if val_h < val_out then
    		  aux t h
    		else
    		  aux t out
    	|None, Some(val_h) ->
    		aux t h
    	|_ ->
    		aux t out
    end
	in
	aux (List.tl base) (List.hd base)
;;

let simplexe nbase base a b c nu =
(*   let (nbase, base, a, b, c, nu) = init_simplexe a b c in *)
	let n = Array.length c in
  let delta = Array.make n None in
  let rec aux nbase base a b c nu =
    match choose_nbase nbase c with
    |Some(e) -> begin
    	printf "e = %d\n" e;
      List.iter
        (fun i -> if a.(i*n + e) > 0 then
                    delta.(i) <- Some(b.(i)/a.(i*n + e))
                  else
                    delta.(i) <- None)
        base;
      let l = min_ind base delta in
      match delta.(l) with
      |None -> raise Not_Bound
      |_ ->
        let (nbase', base', a', b', c', nu') = pivot nbase base a b c nu l e in
        aux nbase' base' a' b' c' nu'
    end
    |None -> begin
    	let out = Array.make n 0 in
    	for i = 0 to (n-1) do
    	  if List.mem i base then
    	    out.(i) <- b.(i)
      done;
      out
    end
  in
  aux nbase base a b c nu
;;

let () =
  let nbase = [0 ; 1 ; 2] in
  let base = [3 ; 4 ; 5] in
  let a = [|1 ; 1 ; 3 ; 1 ; 0 ; 0 ;
            2 ; 2 ; 5 ; 0 ; 1 ; 0 ;
            4 ; 1 ; 2 ; 0 ; 0 ; 1|] in
  let b = [|30 ; 24 ; 36|] in
  let c = [|3 ; 1 ; 2 ; 0 ; 0 ; 0|] in
  let nu = 0 in
  let x_opt = simplexe nbase base a b c nu in
  Array.iter (printf "%d ; ") x_opt;
  printf "\n"
;;



























