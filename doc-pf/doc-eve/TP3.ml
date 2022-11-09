(*
  Lucas DREZET : lucasdrezet@gmail.com
  Sami ELHADJI-TCHIAMBOU : sami3232@live.fr
  
  tout a ete fait
*)

(* TP3 : RENVERSONS *)

Random.self_init();;

let exemple1 = 1::2::3::4::5::6::7::8::9::[];;
let exemple2 = 10::11::12::13::[];;


(* EX 36 *)
let rec auxiliaire = fun l -> fun x -> match l with
                                       | [] -> [x]
                                       | x'::s -> x'::(auxiliaire s x);;

let rec renverser = fun l -> match l with
                             | [] -> []
                             | x::s -> (auxiliaire (renverser s) x);;

renverser exemple1;;


(* EX 37 *)
let rec renverser_tr = fun l1 l2 -> match l1 with
                                    | [] -> l2
                                    | x::s -> renverser_tr s (x::l2);;

renverser_tr exemple1 exemple2;;
renverser_tr exemple1 [];;
(* Pour renverser une seule liste, on met l2 = [] *)


(* EX 38 *)
let rec liste_alea = fun n -> match n with
                              | 0 -> []
                              | _ -> Random.int(100)::(liste_alea (n-1));;


(* EX 39 *)
let n = 10;;
let ex1 = liste_alea n;;

let e1R1 = let deb = Sys.time() in
          let _ = renverser ex1 in
          Sys.time() -. deb;;

let e1E2 = let deb = Sys.time() in
          let _ = renverser_tr ex1 [] in
          Sys.time() -. deb;;
(* Pour une liste de taille 10, le temps de trie est dans le même ordre de grandeur *)

let n = 100;;
let ex1 = liste_alea n;;
let e2R1 = let deb = Sys.time() in
          let _ = renverser ex1 in
          Sys.time() -. deb;;

let e2E2 = let deb = Sys.time() in
          let _ = renverser_tr ex1 [] in
          Sys.time() -. deb;;
(* Pour une liste de taille 100, on voit déjà un écart qui se creuse avec un avantage pour renverser_tr puisque renverser a un temps de 2 * 10^(-4)sec contre 6 * 10^(-6)sec pour renverser_tr *)

let n = 10000;;
let ex1 = liste_alea n;;
let e3R1 = let deb = Sys.time() in
          let _ = renverser ex1 in
          Sys.time() -. deb;;

let e3E2 = let deb = Sys.time() in
          let _ = renverser_tr ex1 [] in
          Sys.time() -. deb;;
(* On observe bien que renverser_tr est plus rapide (avec un temps de 0.0004sec) contre 1.8sec pour renverser *)


(*
  Le cout dépend surtout des parcours de liste effectués.
  la première fonction effectue plusieurs parcours de listes via la fonction auxiliaire et la fonction renverser.
  cela génere de multiples appels recursif. Cela explique la difference avec la seconde fonction renverse qui ne fait qu'un parcours de liste.)
*)
