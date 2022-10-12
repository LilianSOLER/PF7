(* 3 Manipulation de listes *)

(* 3.1 Tri par sélection *)

(* Exercice 26 *)

let rec min_list = fun l ->
  match l with 
    | [] -> max_int
    | x::l -> min x (min_list l);;

let rec pop = fun l i ->
  match l with 
    | [] -> []
    | x::l -> if x = i then pop l i else x::(pop l i);;

let trouve_min_i = fun list -> let min = min_list list in (min, pop list min);;


let list1 = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10];;
let list2 = [10; 9; 8; 7; 6; 5; 4; 3; 2; 1];;

let test_min1 = assert(min_list list1 = 1);;
let test_min2 = assert(min_list list2 = 1);;

let test_pop1 = assert(pop list1 4 = [1; 2; 3; 5; 6; 7; 8; 9; 10]);;
let test_pop1 = assert(pop list1 1 = [2; 3; 4; 5; 6; 7; 8; 9; 10]);;
let test_pop1 = assert(pop list1 10 = [1; 2; 3; 4; 5; 6; 7; 8; 9]);;
let test_pop1 = assert(pop list1 9 = [1; 2; 3; 4; 5; 6; 7; 8; 10]);;

let test_trouve_min_i_1 = assert (trouve_min_i list1 = (1, [2; 3; 4; 5; 6; 7; 8; 9; 10]));;
let test_trouve_min_i_2 = assert (trouve_min_i list2 = (1, [10; 9; 8; 7; 6; 5; 4; 3; 2]));;

let trouve_min = fun min_func list -> let min = min_func list in (min, pop list min);;

let test_trouve_min1 = assert (trouve_min min_list list1 = (1, [2; 3; 4; 5; 6; 7; 8; 9; 10]));;
let test_trouve_min2 = assert (trouve_min min_list list2 = (1, [10; 9; 8; 7; 6; 5; 4; 3; 2]));;

(* Exercice 27 *)

let min_list_with_comp = fun comp_func list ->
  let rec aux = fun list comp_func min ->
    match list with 
      | [] -> min
      | x::l -> if comp_func x min = x then aux l comp_func x else aux l comp_func min
  in match list with 
       | [] -> 0
       | x::l -> aux list comp_func x;;

let tri_selection_aux = fun list min_func comp_func -> let min = min_func comp_func list in (min, pop list min);;



let rec tri_selection = fun list comp_func -> match list with
                                 | [] -> []
                                 | _ -> let (min, l) = tri_selection_aux list min_list_with_comp comp_func in
                                        min::(tri_selection l comp_func);;

let test_tri_selection1 = assert(tri_selection list1 max = [10; 9; 8; 7; 6; 5; 4; 3; 2; 1]);;
let test_tri_selection2 = assert(tri_selection list2 max = [10; 9; 8; 7; 6; 5; 4; 3; 2; 1]);;
let test_tri_selection3 = assert(tri_selection list1 min = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]);;
let test_tri_selection4 = assert(tri_selection list2 min = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]);;

let tri_selection_i = fun list -> tri_selection list min;;

let test_tri_selection_i1 = assert(tri_selection_i list1 = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]);;
let test_tri_selection_i2 = assert(tri_selection_i list2 = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]);;

(* 3.2 Mesure de performances *)

(* Exercice 28 (Génération de tests) *)

Random.init 28

let rec list_alea = fun n ->
  match n with 
    | 0 -> []
    | n' -> (Random.int 10)::(list_alea (n'-1));;

let list_alea1 = list_alea 15;;

let deb = Sys.time() in
let _ = tri_selection_i (list_alea 100)
in Sys.time() -. deb;;

let list_ordered = tri_selection_i (list_alea 100);;

let deb2 = Sys.time() in
let _ = tri_selection_i list_ordered
in Sys.time() -. deb2;;
                                                                                 
let renv liste=let rec renv_aux a b=match a with |[]->b |hd::tl->renv_aux tl (hd::b) in renv_aux liste []

let exemple_renv1=assert(renv list1=[10;9;8;7;6;5;4;3;2;1])

let rec renv_app =fun l1 l2 ->match l1 with |[]->l2 |x::s->renv_app s (x::l2)

let exemple_renv_app1=assert(renv_app list1 list2 =[10;9;8;7;6;5;4;3;2;1;10;9;8;7;6;5;4;3;2;1])
(*
let rec max_list = fun l ->
  match l with 
    | [] -> max_int
    | x::l -> max x (max_list l);;

let dromadaire=fun list comp_func->let tri=tri_selection comp_func list in let max=max_list tri in max

let test_dromadaire=assert(dromadaire list1 max = 10)
 *)
