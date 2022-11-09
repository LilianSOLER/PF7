(*POITEVIN Eve & REYGNER Etienne*)

(*2.1*)

type abin =
  | F
  | N of abin*int*abin;;

let arbre = N (N (F, 2, N (F, 4, F)), 1, F);;

let rec nbN : abin -> int =
  fun a -> match a with
           | F -> 0
           | N (g, n, d) -> nbN(g) + 1 + nbN(d);;

assert (nbN arbre = 3);; (* Expecting 3 *)

let rec hauteur : abin -> int =
  fun a -> match a with
           | F -> 0
           | N (g, n, d) -> let x = hauteur g in
                           let y = hauteur d in
                           (max x y) + 1;;

assert (hauteur arbre = 3) ;; (* Expecting 3 *)
           
let rec produit : abin -> int =
  fun a -> match a with
           | F -> 1
           | N (g, n, d) -> let x = produit g in
                           let y = produit d in
                           x * n * y;;

assert (produit arbre = 8);; (* Expecting 8 *)

let rec somme : abin -> int =
  fun a -> match a with
           | F -> 0
           | N (g, n, d) -> let x = somme g in
                           let y = somme d in
                           x + n + y;;

assert (somme arbre = 7);; (* Expecting 7 *)

let rec appartient : abin -> int -> bool =
  fun a x -> match a with
           | F -> false
           | N (g, n, d) -> x = n || appartient g x || appartient d x;;

assert (appartient arbre 1 = true);; (* Expecting true *)
assert (appartient arbre 2 = true);; (* Expecting true *)
assert (appartient arbre 4 = true);; (* Expecting true *)
assert (appartient arbre 3 = false);; (* Expecting false *)

let rec maxArbre : abin  -> int =
  fun a -> match a with
           | F -> min_int
           | N (g, n, d) -> let x = maxArbre g in
                            let y = maxArbre d in
                            max (max x y) n;;

assert (maxArbre arbre = 4);; (* Expecting 4 *)
                            
let arbre2 = N (N (F, 2, N (F, 4, F)), 1, N (F, 3, F));;

let estNoeud : abin -> bool =
  fun a -> match a with
           | F -> false
           | N (g, n, d) -> true;;

let rec nbNBinaires : abin -> int =
  fun a -> match a with
           | F -> 0
           | N (g, n, d) -> nbNBinaires g + (if (estNoeud g && estNoeud d) then 1 else 0) + nbNBinaires d ;;

assert(nbNBinaires arbre2 = 1);;

(* Exercice 17 *)

let arbre3 = N (N (N (F, 2, F), 3, F), 5, N (N (F, 6, N (F, 7, F)), 8, N (F, 9, F)));;

(* Exercice 18 *)

let rec appartientAbr : abin -> int -> bool =
  fun a x -> match a with
           | F -> false
           | N (g, n, d) -> x = n || if x < n then appartientAbr g x else appartientAbr d x;;

assert(appartientAbr arbre3 3 = true);;

(* Exercice 19 *)

let rec insert : abin -> int -> abin =
  fun a x -> match a with
           | F -> N (F, x, F)
           | N (g, n, d) -> if x < n then N(insert g x, n, d) else N(g, n, insert d x);;

assert (insert arbre3 1 = N (N (N (N (F, 1, F), 2, F), 3, F), 5, N (N (F, 6, N (F, 7, F)), 8, N (F, 9, F))));;

(* Exercice 20 *)

let rec valLeft : abin -> int -> bool =
  fun a x -> match a with
           | F -> true
           | N (g, n, d) -> x < n && valLeft g x && valLeft d x ;;

let rec valRight : abin -> int -> bool =
  fun a x -> match a with
             | F -> true
             | N (g, n, d) -> x < n && valRight g x && valRight d x;;

let rec verifAbr : abin -> bool =
  fun a -> match a with
           | F -> true
           | N(g, n, d) -> valLeft g n && valRight d n;;

verifAbr arbre3;;
