(* TP 2 *)
(* 2.1 - Fonctions simples sur un arbre *)

type abin = Nil | Cons of abin * int * abin;; (* Create a new type called abin, which is either Nil or Cons of an abin, an int, and an abin. *)


let abin1 = Cons(Nil, 10, Nil);;
let abin2 = Cons(abin1, 12, abin1);;
let abin3 = Cons(abin2, 14, abin1);;
let abin4 = Cons(abin2, 16, abin3);;

let rec nombre_noeuds = fun abin -> match abin with 
  | Nil -> 0 
  | Cons(a1, x, a2) -> 1 + nombre_noeuds a1 + nombre_noeuds a2;; (*1 + les autres noeuds *)
  
let test_nombre_noeuds_1 = assert (nombre_noeuds abin1 = 1);;
let test_nombre_noeuds_2 = assert (nombre_noeuds abin2 = 3);;

let rec hauteur_arbre = fun abin -> match abin with 
  | Nil -> 0
  | Cons(a1, x, a2) -> 1 + max (hauteur_arbre a1) (hauteur_arbre a2);;


let test_hauteur_arbre1 = assert (hauteur_arbre abin1 = 1);;
let test_hauteur_arbre2 = assert (hauteur_arbre abin2 = 2);;
let test_hauteur_arbre3 = assert (hauteur_arbre abin3 = 3);;
let test_hauteur_arbre4 = assert (hauteur_arbre abin4 = 4);;

let rec somme_arbre = fun abin -> match abin with 
  | Nil -> 0
  | Cons(a1, x, a2) -> somme_arbre a1 + x + somme_arbre a2;;

let sum_1 = somme_arbre abin1;;
let sum_2 = somme_arbre abin2;;
let sum_3 = somme_arbre abin3;;
let sum_4 = somme_arbre abin4;;

let p1 = 10;;
let p2 = 12 + p1 + p1;;
let p3 = 14 + p2 + p1;;
let p4 = 16 + p3 + p2;;

let test_somme_arbre1 = assert (sum_1 = p1);;
let test_somme_arbre2 = assert (sum_2 = p2);;
let test_somme_arbre3 = assert (sum_3 = p3);;
let test_somme_arbre4 = assert (sum_4 = p4);;

let rec produit_arbre = fun abin -> match abin with 
  | Nil -> 1
  | Cons(a1, x, a2) -> produit_arbre a1 * x * produit_arbre a2;;

let prod_1 = produit_arbre abin1;;
let prod_2 = produit_arbre abin2;;
let prod_3 = produit_arbre abin3;;
let prod_4 = produit_arbre abin4;;

let p1 = 10;;
let p2 = 12 * p1 * p1;;
let p3 = 14 * p2 * p1;;
let p4 = 16 * p3 * p2;;

let test_produit_arbre1 = assert (prod_1 = p1);;
let test_produit_arbre2 = assert (prod_2 = p2);;
let test_produit_arbre3 = assert (prod_3 = p3);;
let test_produit_arbre4 = assert (prod_4 = p4);;

let rec is_in_arbre = fun abin e -> match abin with 
  | Nil -> false
  | Cons(a1, x, a2) -> (e = x) || is_in_arbre a1 e || is_in_arbre a2 e;;

let test_is_in_arbre1 = assert (is_in_arbre abin4 10 = true);;
let test_is_in_arbre2 = assert(is_in_arbre abin4 13 = false);;

let rec max_arbre = fun abin -> match abin with
  | Nil -> min_int
  | Cons(a1, x, a2) -> max (max x (max_arbre a1)) (max_arbre a2);;

let test_max_arbre1 = assert (max_arbre abin1 = 10);;
let test_max_arbre2 = assert (max_arbre abin2 = 12);;
let test_max_arbre3 = assert (max_arbre abin3 = 14);;
let test_max_arbre4 = assert (max_arbre abin4 = 16);;

let rec nombre_noeuds_really_binary = fun abin -> match abin with
  | Nil -> 0
  | Cons(Nil, x, Nil) -> 0
  | Cons(Nil, x, a2) -> nombre_noeuds_really_binary a2
  | Cons(a1, x, Nil) -> nombre_noeuds_really_binary a1 
  | Cons(a1, x, a2) -> 1 +  nombre_noeuds_really_binary a1 + nombre_noeuds_really_binary a2;;

let test_nombre_noeuds_really_binary1 = assert (nombre_noeuds_really_binary abin1 = 0);;
let test_nombre_noeuds_really_binary2 = assert (nombre_noeuds_really_binary abin2 = 1);;
let test_nombre_noeuds_really_binary3 = assert (nombre_noeuds_really_binary abin3 = 2);;
let test_nombre_noeuds_really_binary4 = assert (nombre_noeuds_really_binary abin4 = 4);;

(* 2.2 - Arbre Binaire de Recherche *)
let feuille = fun x -> Cons(Nil, x, Nil);;

type abin_name = Cons_abin_name of abin * string;;

type list_tree = Nil_tree | Cons_tree of abin_name * list_tree;;

let abr0 = feuille 1;;
let abr1 = Cons(abr0, 3, feuille 2);;
let abr2 = Cons(abr1, 4, feuille 5);;
let abr3 = Cons(feuille 7, 8, feuille 9);;
let abr4 = Cons(abr3, 10, feuille 11)
let abr5 = Cons(abr2, 6, abr4);;

let list_tree = Cons_tree(Cons_abin_name(abr5, "abr5"), Nil_tree);;


let rec insert_in_list_tree = fun abin name l ->  match l with
  | Nil_tree -> Cons_tree(Cons_abin_name(abin, name), Nil_tree)
  | Cons_tree(a, l) -> Cons_tree(a, insert_in_list_tree abin name l);;

let list_tree = insert_in_list_tree abr0 "abr0" list_tree;;
let list_tree = insert_in_list_tree abr1 "abr1" list_tree;;
let list_tree = insert_in_list_tree abr2 "abr2" list_tree;;
let list_tree = insert_in_list_tree abr3 "abr3" list_tree;;
let list_tree = insert_in_list_tree abr4 "abr4" list_tree;;


let rec mem = fun abr e -> match abr with 
  | Nil -> false
  | Cons(a1, x, a2) -> if x = e then true else if x < e then mem a2 e else mem a1 e;;

let test_mem1 = assert (mem abr0 1);;
let test_mem1_bis = assert (mem abr0 2 = false);;
let test_mem5 = assert (mem abr5 11);;
let test_mem5_bis = assert (mem abr5 1);;
let test_mem5_ter = assert (mem abr5 13 = false);;

let rec insert = fun abin e -> match abin with 
  | Nil -> feuille e
  | Cons(a1, x, a2) -> if x < e then Cons(a1, x, insert a2 e) else Cons(insert a1 e, x, a2);;

let abr1_insert = insert abr1 4;;
let abr2_insert = insert abr2 13;;
let abr3_insert = insert abr3 4;;
let abr4_insert = insert abr4 13;;
let abr5_insert = insert abr5 8;;
let abr5_insert_bis = insert abr5 12;;

let list_insert_tree =  Cons_tree(Cons_abin_name(abr5_insert_bis, "abr5_insert_bis"), Nil_tree);;
let list_insert_tree = insert_in_list_tree abr1_insert "abr1_insert" list_insert_tree;;
let list_insert_tree = insert_in_list_tree abr2_insert "abr2_insert" list_insert_tree;;
let list_insert_tree = insert_in_list_tree abr3_insert "abr3_insert" list_insert_tree;;
let list_insert_tree = insert_in_list_tree abr4_insert "abr4_insert" list_insert_tree;;
let list_insert_tree = insert_in_list_tree abr5_insert "abr5_insert" list_insert_tree;;


let display_tree = fun abin ->
  let rec display_tree_aux = fun abin tab -> match abin with 
    | Nil -> ()
    | Cons(a1, x, a2) -> display_tree_aux a2 (tab ^ "   "); print_string (tab ^ string_of_int x ^ "  "); print_newline(); display_tree_aux a1 (tab ^ "   ") in 
  display_tree_aux abin "";;

let rec display_tree_list = fun list -> match list with 
  | Cons_tree(Cons_abin_name(a, name), list) -> print_string (name ^ ":"); print_newline();display_tree a; print_newline();print_newline(); display_tree_list list
  | Nil_tree -> ();;

let test_display_tree_list = display_tree_list list_tree;;
let test_display_tree_list_insert = display_tree_list list_insert_tree;;








(* Exercice 21 est le dernier à faire *)








