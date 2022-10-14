(*Bracquier Benjamin - Soler Lilian - INFO4 *)

(*4.1 Structure de file *)
type 'a file  = 'a list;;

exception Foo of string;;

let file_vide : 'a file = [];;

let est_vide : 'a file -> bool = fun f -> f = file_vide;;

let enfile : 'a -> 'a file -> 'a file = fun x f -> x::f;;

let rec defile : 'a file -> 'a * 'a file = fun f -> 
  match f with 
    | [] -> raise(Foo "Vous ne pouvez pas défilez une liste vide")
    | [x] -> (x, []) 
    | x::l -> let (xrec, frec) = defile l in (xrec, x::frec);; 

let file1 : int list = enfile 5  (enfile 4  (enfile 3  (enfile 2 (enfile 1 file_vide))));;

let file2 : int list = enfile 5  (enfile 4  (enfile 3  (enfile 2 file_vide)));;

let test_defile = assert(defile file1 = (1, file2));;

let rec list_to_file : 'a list -> 'a file = fun l -> 
    match l with 
      | [] -> file_vide
      | x::l -> enfile x (list_to_file l);;

let file3 : int list = list_to_file [1;2;3;4;5];; 

let rec file_to_list : 'a file -> 'a list = fun file ->
    match file with 
      | [] -> []
      | x::f -> let (xrec, frec) = defile file in xrec::(file_to_list frec);;

let list3 : int list = file_to_list file3;;

let rec renv_app = fun l1 l2 ->
  match l1 with 
  | []->l2 
  | x::s->renv_app s (x::l2);;

let renv : 'a list -> 'a list = fun l -> renv_app l [];;

let test_file : 'a list -> bool = fun l -> 
  let f = list_to_file l in 
  let l' = file_to_list f in 
  l = renv l';;

Random.init 28

let rec list_alea = fun n ->
  match n with 
    | 0 -> []
    | n' -> (Random.int 100000)::(list_alea (n'-1));;

let test_file_alea = fun n -> assert(test_file (list_alea n));;

test_file [1;2;3;4;5];;
test_file [5;4;3;2;1];;

test_file_alea 1000;;
test_file_alea 10000;;

type 'a file = 'a list * 'a list;;

let file_vide : 'a file = ([], []);;

let est_vide : 'a file -> bool = fun (l1, l2) -> l1 = [] && l2 = [];;

let enfile : 'a -> 'a file -> 'a file = fun x (l1, l2) -> (x::l1, l2);;

let rec defile : 'a file -> 'a * 'a file = fun (l1, l2) -> 

  match l2 with 
    | [] -> 
      begin
      match l1 with 
      | [] -> raise(Foo "Vous ne pouvez pas défilez une liste vide")
      | y::l1' ->defile ([], renv l1)
      end
    | x::l2' -> (x, (l1, l2'));;

let file1 : int file = enfile 5  (enfile 4  (enfile 3  (enfile 2 (enfile 1 file_vide))));;
let file2 : int file = enfile 5  (enfile 4  (enfile 3  (enfile 2 file_vide)));;

let file3 : int file = snd(defile file1);;
let element2 : int = fst(defile file3);;

(* 4.4 File à priorité  *)

type 'a fap = ('a * int) list;;

let fap_vide : 'a fap = [];;

let est_vide : 'a fap -> bool = fun f -> f = fap_vide;;

let rec insert : 'a -> int -> 'a fap -> 'a fap = fun x p f ->
  match f with 
    | [] -> [(x, p)]
    | (y, q)::f' -> if p > q then (x, p)::(y, q)::f' else (y, q)::(insert x p f');;

let rec extract : 'a fap -> 'a * 'a fap = fun f -> 
  match f with 
    | [] -> raise(Foo "Vous ne pouvez pas extraire un élément d'une fap vide")
    | (x, p)::f' -> (x, f');;

let fap1 : int fap = insert 5 1 (insert 4 2 (insert 3 3 (insert 2 4 (insert 1 5 fap_vide))));;
let fap2 : int fap = insert 5 1 (insert 4 2 (insert 3 3 (insert 2 4 fap_vide)));;

let fap3 : int fap = snd(extract fap1);;

let element2 : int = fst(extract fap3);;

let list_to_fap : 'a list -> 'a fap = fun l -> 
  let rec aux = fun l p f -> 
    match l with 
      | [] -> f
      | x::l' -> aux l' (p+1) (insert x p f) in 
  aux l 0 fap_vide;;

let fap4 : int fap = list_to_fap [1;2;3;4;5];;

let fap_to_list : 'a fap -> 'a list = fun f -> 
  let rec aux = fun f l -> 
    match f with 
      | [] -> l
      | (x, p)::f' -> aux f' (x::l) in 
  aux f [];;

let list4 : int list = fap_to_list fap4;;

let test_fap : 'a list -> bool = fun l -> 
  let f = list_to_fap l in 
  let l' = fap_to_list f in 
  l = l';;

test_fap [1;2;3;4;5];;
test_fap [5;4;3;2;1];;

let fap_test = assert(test_fap [1;2;3;4;5]);;







