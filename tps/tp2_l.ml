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
let abr1 = Cons(abr0, 2, feuille 3);;
let abr2 = Cons(abr1, 4, feuille 5);;
let abr3 = Cons(feuille 7, 9, feuille 10);;
let abr4 = Cons(abr3, 11, feuille 12)
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
let abr3_insert = insert abr3 8;;
let abr4_insert = insert abr4 13;;
let abr5_insert = insert abr5 8;;
let abr5_insert_bis = insert abr5 13;;

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

let rec verif_abr = fun abin -> match abin with 
  | Nil -> true
  | Cons(Nil, x, Nil) -> true
  | Cons(Nil, x, Cons(a1, y, a2)) -> if x < y then verif_abr (Cons(a1, y, a2)) else false
  | Cons(Cons(a1, y, a2), x, Nil) -> if x > y then verif_abr (Cons(a1, y, a2)) else false
  | Cons(Cons(a1, y, a2), x, Cons(a3, z, a4)) -> if x > y && x < z then verif_abr (Cons(a1, y, a2)) && verif_abr (Cons(a3, z, a4)) else false;;

let test_verif_abr1 = assert (verif_abr abr1);;
let test_verif_abr2 = assert (verif_abr abr2);;
let test_verif_abr3 = assert (verif_abr abr3);;
let test_verif_abr4 = assert (verif_abr abr4);;
let test_verif_abr5 = assert (verif_abr abr5);;
let test_verif_abr5_insert = assert (verif_abr abr5_insert);;
let test_verif_abr5_insert_bis = assert (verif_abr abr5_insert_bis);;
let test_verif_abr1_insert = assert (verif_abr abr1_insert);;

type list = Nil_int | Cons_int of int * list;;

let triAbr = fun list -> 
  let rec triAbr_aux = fun list abin -> match list with 
    | Nil_int -> abin
    | Cons_int(x, list) -> triAbr_aux list (insert abin x) in 
  triAbr_aux list Nil;;

let triAbr1 = triAbr (Cons_int(1, Cons_int(2, Cons_int(3, Cons_int(4, Cons_int(5, Nil_int))))));;
let triAbr2 = triAbr (Cons_int(5, Cons_int(4, Cons_int(3, Cons_int(2, Cons_int(1, Nil_int))))));;
let triAbr3 = triAbr (Cons_int(1, Cons_int(3, Cons_int(5, Cons_int(2, Cons_int(4, Nil_int))))));;
let triAbr4 = triAbr (Cons_int(5, Cons_int(3, Cons_int(1, Cons_int(4, Cons_int(2, Nil_int))))));;
let triAbr5 = triAbr (Cons_int(2, Cons_int(4, Cons_int(1, Cons_int(3, Cons_int(5, Nil_int))))));;

let test_triAbr = assert (verif_abr (triAbr (Cons_int(1, Cons_int(2, Cons_int(3, Cons_int(4, Cons_int(5, Cons_int(6, Cons_int(7, Cons_int(8, Cons_int(9, Cons_int(10, Nil_int)))))))))))));;
let test_triAbr_bis = assert (verif_abr (triAbr (Cons_int(10, Cons_int(9, Cons_int(8, Cons_int(7, Cons_int(6, Cons_int(5, Cons_int(4, Cons_int(3, Cons_int(2, Cons_int(1, Nil_int)))))))))))));;
let test_triAbr_ter = assert (verif_abr (triAbr (Cons_int(5, Cons_int(3, Cons_int(1, Cons_int(2, Cons_int(4, Cons_int(7, Cons_int(6, Cons_int(8, Nil_int)))))))))));;

let abr_to_list = fun abin -> 
  let rec abr_to_list_aux = fun abin list -> match abin with 
    | Nil -> list
    | Cons(a1, x, a2) -> abr_to_list_aux a1 (Cons_int(x, abr_to_list_aux a2 list)) in 
  abr_to_list_aux abin Nil_int;;

let test_abr_to_list = assert (abr_to_list (triAbr (Cons_int(1, Cons_int(2, Cons_int(3, Cons_int(4, Cons_int(5, Cons_int(6, Cons_int(7, Cons_int(8, Cons_int(9, Cons_int(10, Nil_int)))))))))))) = Cons_int(1, Cons_int(2, Cons_int(3, Cons_int(4, Cons_int(5, Cons_int(6, Cons_int(7, Cons_int(8, Cons_int(9, Cons_int(10, Nil_int)))))))))));;
let abr_to_list1 = abr_to_list (triAbr (Cons_int(1, Cons_int(2, Cons_int(3, Cons_int(4, Cons_int(5, Cons_int(6, Cons_int(7, Cons_int(8, Cons_int(9, Cons_int(10, Nil_int)))))))))))) ;;
let abr_to_list2 = abr_to_list (triAbr (Cons_int(10, Cons_int(9, Cons_int(8, Cons_int(7, Cons_int(6, Cons_int(5, Cons_int(4, Cons_int(3, Cons_int(2, Cons_int(1, Nil_int)))))))))))) ;;
let abr_to_list3 = abr_to_list (triAbr (Cons_int(5, Cons_int(3, Cons_int(1, Cons_int(2, Cons_int(4, Cons_int(7, Cons_int(6, Cons_int(8, Nil_int))))))))));; 







(* Exercice 21 est le dernier à faire *)








