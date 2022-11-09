(* Consigne gÃ©nÃ©rale : remplacer les
              raise (TODO "...")
   par votre code.
   PrÃ© et post-condition : ce fichier compile sans erreur *)

let prenom: string = "Eve"
let nom: string = "Poitevin"

exception TODO of string


type arbint = F | N of arbint * int * arbint
type file_d_entiers = int list

(*
                        N
                     /  |  \
                   N    4    N
                 / | \     / | \
                F  1  F   F  6  F
 *)

(* DÃ©finir en OCaml la valeur de l'arbre ci-dessus *)
let arbre1 = N (N (F, 1, F), 4, N (F, 6, F));; 

(* decomposition d'une file d'entiers en
- soit le vide
- soit la file des premiers Ã©lÃ©ments et le dernier
 *)
type decomp = Aucun | Elts of file_d_entiers * int

(* L'interface est alors plus simple (pas besoin d'exception) :
val  file_vide : file_d_entiers
val enfile : int -> file_d_entiers -> file_d_entiers
val defile : file_d_entiers -> decomp
 *)

(* Algorithmes quand on enfile en fin de liste et on dÃ©file en dÃ©but de liste *)
let file_vide : file_d_entiers = []
let enfile : int -> file_d_entiers -> file_d_entiers =
  fun x f -> f @ (x :: [])
let defile : file_d_entiers -> decomp =
  fun f ->
  match f with
  | [] -> Aucun
  | x :: u -> Elts (u, x)

(* Je ne suis pas certaine d'avoir très bien compris ce qu'il fallait faire ci-dessous : *)

let est_de_complexite_lineaire_enfile : unit -> bool = fun () -> false;;
let est_de_complexite_lineaire_defile : unit -> bool = fun () -> true;;


(* Comme pour enfile, mais on enfile une liste d'entiers au lieu d'un seul entier,
   dans une file existante *)
(* Les Ã©lÃ©ments de la liste sont enfilÃ©s en commenÃ§ant par la tÃªte de liste.
   Par exemple si la liste est [1; 4; 6], les Ã©lÃ©ments Ã  enfiler sont dans l'ordre
   1 puis 4 puis 6. *)
let rec enfiliste : int list -> file_d_entiers -> file_d_entiers =
  fun u f -> match u with
             | [] -> f
             | x :: f' -> enfiliste f' (x :: f);;

let i = enfiliste (1 :: 2 :: 3 :: []) file_vide;; 

(* Comme pour enfile, mais on enfile un arbre d'entiers au lieu d'un seul entier,
   dans une file existante *)
(* Les Ã©lÃ©ments de l'arbre sont enfilÃ©s en commenÃ§ant par la gauche
   Par exemple si l'arbre est arbre1 (ci-dessus), les Ã©lÃ©ments Ã  enfiler sont dans l'ordre
   1 puis 4 puis 6. *)
let rec enfilarb_gauche : arbint -> file_d_entiers -> file_d_entiers =
  fun a f -> match a with
             | F -> f
             | N (g, n, d) -> let a = enfilarb_gauche g f in
                              let b = enfile n a in
                              enfilarb_gauche d b;;

(* Pour tester *)
let test () = enfilarb_gauche arbre1 file_vide

(* La fonction defilarb defile la file en entrÃ©e en un arbre binaire
   de sorte que le premier Ã©lÃ©ment sera Ã  la racine, tandis que le dernier
   sera "en bas Ã  gauche", exemple :
   si les Ã©lÃ©ments dÃ©filÃ©s sont successivement 1, 4 et 6, l'arbre sera

                            N
                          / | \
                        N   1  F
                      / | \
                    N   4  F
                  / | \
                 F  6  F

 *)

let rec defilarb : file_d_entiers -> arbint =
  fun f -> match f with
           | [] -> F
           | x :: f' -> N (defilarb f', x, F);;

let arb146 () = defilarb (enfiliste (1 :: 4 :: 6 :: []) file_vide);;


(* Donner le type d'un arbre polymorphe qui gÃ©nÃ©ralise arbint *)

type 'a arb = | F
              | N of ('a arb) * 'a * ('a arb);;
