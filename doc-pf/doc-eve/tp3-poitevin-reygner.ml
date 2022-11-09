(*POITEVIN Eve & REYGNER Etienne*)

(* 3.1. *)

(* Exercice 50 *)

type produit =
  | MP3
  | Appareil
  | Camera
  | Telephone
  | Ordinateur;;

type marque =
  | Alpel
  | Syno
  | Massung
  | Liphisp;;

type abin =
  | F
  | N of abin*int*abin;;



type article = Article of produit * marque * int * int;;

let art = (Article(Telephone, Alpel, 1000, 3))::(Article(Telephone, Massung, 800, 3))::[];;

(* Exercice 51 *)

let rec est_en_stock = fun p1 m1 i1 l ->
  match l with
  |[] -> false
  |Article(p, m, x, s)::l' -> if ((p1=p && m1=m && i1=x) && (s>0)) then true else est_en_stock p1 m1 i1 l';;

assert(est_en_stock Telephone Alpel 1000 art = true);;

(* Exercice 52 *)

let rec ajoute_article = fun a l -> let Article(p, m, x, s) = a in
  match l with
  | [] -> a::[]
  | Article(ps, ms, xs, ss)::l' -> if p = ps && m = ms && x = xs && s = ss then Article(ps, ms, xs, ss + s)::l' else Article(ps, ms, xs, ss)::(ajoute_article a l');;

ajoute_article (Article(Ordinateur, Alpel, 300, 1)) art;;

(* Exercice 53 *)

let rec enleve_article = fun a l -> let Article(p, m, x, s) = a in
                                    match l with
                                    | [] -> []
                                    | Article(ps, ms, xs, ss)::l' -> if p = ps && m = ms && x = xs && s = ss then enleve_article a l' else Article(ps, ms, xs, ss)::(enleve_article a l');;


enleve_article (Article(Ordinateur, Alpel, 300, 1)) art;;
ajoute_article (Article(Ordinateur, Alpel, 300, 1)) art;;

(* Exercice 26 *)

exception Error;;

let rec trouve_min_bis = fun l a ->let Article(p1, q1, m1, w1) = a in match l with
                                    | [] -> a
                                    | Article(p, q, x, w)::l' -> if x < m1 then trouve_min_bis l' (Article(p, q, x, w)) else trouve_min_bis l' a;;

let trouve_min = fun l -> match l with
                          | [] -> raise Error
                          | a::l' -> let min = trouve_min_bis l a in
                                    let p = enleve_article min l in (min, p);;
art;;
(*trouve_min art;;*)

(* Exercice 27 *)

let rec tri_selection_a = fun l -> match l with
                                 | [] -> []
                                 | _ -> let (min, s) = trouve_min l in min::(tri_selection s);;


tri_selection_a art;;

(* ----------------------------------- Nouveau sujet -----------------------------------*)

(* Exercice 26 *)

exception Error;;

let rec enleve_min = fun x l -> match l with
                                    | [] -> []
                                    | u::l' -> if u = x then enleve_min x l' else u::(enleve_min x l');;

let rec trouve_min_bis = fun l x -> match l with
                                    | [] -> x
                                    | u::l' -> if u < x then trouve_min_bis l' u else trouve_min_bis l' x;;

let trouve_min_i = fun l -> match l with
                          | [] -> raise Error
                          | x::l' -> let min = trouve_min_bis l x in
                                     let p = enleve_min min l in (min, p);;

let enlMin = 7::3::2::5::[];;
trouve_min_i enlMin;;

(* Exercice 27 *)

let rec tri_selection_i = fun l -> match l with
                                 | [] -> []
                                 | _ -> let (min, s) = trouve_min_i l in min::(tri_selection_i s);;

tri_selection_i enlMin;;

(* Exercice 28 *)

let rec liste_alea = fun n -> match n with
                              | 0 -> []
                              | _ -> Random.int(50)::(liste_alea(n-1));;

liste_alea 3;;

let deb = Sys.time() in
    let _ = liste_alea 3
    in Sys.time() -. deb;;

(* Exercice 29 *)

(* --- Import de triABR --- *)

let rec insert : abin -> int -> abin =
  fun a x -> match a with
           | F -> N (F, x, F)
           | N (g, n, d) -> if x < n then N(insert g x, n, d) else N(g, n, insert d x);;

let rec createABR = fun l x -> match l with
           | [] -> x
           | u::s -> createABR s (insert x u);;

let rec listFinal = fun a -> match a with
                             | F -> []
                             | N(g, n, d) -> (listFinal g) @ [n] @ (listFinal d);;

let triABR = fun l -> let a = (createABR l F) in listFinal a;;

let list1 = 5::2::3::4::9::[];;
let listVerif = 2::3::4::5::9::[];;

assert(triABR list1 = listVerif);;

(* --- --- *)

let l1 = liste_alea 50;;

let deb = Sys.time() in
    let _ = tri_selection_i l1
    in Sys.time() -. deb;;

(* temps : 0.00027200000000005 *)

let deb = Sys.time() in
    let _ = triABR l1
    in Sys.time() -. deb;;

(* temps : 9.79999999999314753e-05 *)

(* Exercice 30 *)

let rec renv = fun l -> match l with
                        | [] -> []
                        | x::l' -> renv l' @ (x::[]);;

assert(renv (renv l1) = l1);;

(* Exercice 31 *)

let rec renv_app = fun l_1 l_2 -> match l_1 with
                                  | [] -> l_2
                                  | x::l' -> renv_app l' (x::l_2);;

let l2 = liste_alea 50;;

assert(renv_app l1 l2 = (renv l1) @ l2);;

(* Exercice 32 *)

let l3 = liste_alea 10000;;
let l4 = liste_alea 10000;;

let deb = Sys.time() in
    let _ = renv l3
    in Sys.time() -. deb;;

(* temps :  1.091532 *)

let deb = Sys.time() in
    let _ = renv_app l3 l4
    in Sys.time() -. deb;;

(* temps : 0.00076799999999987989 *)
