(* Fichier pouvant être fourni aux étudiants après leurs tentatives *)

(* ---------------------------------------------------------------- *)
(* Pour les tests *)

let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0

(* ------------------------------------------------------------ *)
(* Types et primitives de base *)

(* Le type des fonctions qui épluchent une liste de caractères. *)
type analist = char list -> char list

(* Le type des fonctions qui épluchent une liste de caractères et rendent un résultat. *)
type 'res ranalist = char list -> 'res * char list

(* Idem en plus général. *)
type ('token, 'res) ranalist_gen = 'token list -> 'res * 'token list

(* L'exception levée en cas de tentative d'analyse ratée. *)
exception Echec

(* Ne rien consommer *)
let epsilon : analist = fun l -> l
(* Un epsilon informatif *)
let epsilon_res (info : 'res) : 'res ranalist =
  fun l -> (info, l)

(* Terminaux *)
let terminal c : analist = fun l -> match l with
  | x :: l when x = c -> l
  | _ -> raise Echec

let terminal_cond (p : char -> bool) : analist = fun l -> match l with
  | x :: l when p x -> l
  | _ -> raise Echec

(* Le même avec résultat *)
let terminal_res (f : 'term -> 'res option) : 'res ranalist =
  fun l -> match l with
  | x :: l -> (match f x with Some y -> y, l | None -> raise Echec)
  | _ -> raise Echec


(* ------------------------------------------------------------ *)
(* Exercice sur les suites de chiffres *)


           
(* Grammaire (U pour un-chiffre, A pour au-moins-un, C pour chiffres) :

  U ::= '0' | ... | '9'

  C ::= U C | epsilon

Que l'on décompose en :

  C ::= A | epsilon

  A ::= U C

 *)

let est_chiffre c = '0' <= c && c <= '9'

(* Consommation de tous les chiffres en préfixe *)
let rec chiffres : analist =
  let un_chiffre : analist = terminal_cond est_chiffre in
  let au_moins_un : analist = fun l ->
    let l = un_chiffre l in
    let l = chiffres l in
    l
  and aucun : analist = epsilon
  in fun l ->
     try au_moins_un l with Echec -> aucun l

let val_chiffre : char -> int option = fun c ->
  match c with
  | '0' .. '9' -> Some (Char.code c - Char.code '0')
  |_ -> None
let un_chiffre : int ranalist =
    terminal_res val_chiffre

let rec sommechiffres : int ranalist =
  let rec au_moins_un : int ranalist = fun l ->
    let x, l = un_chiffre l in
    let n, l = sommechiffres l in
    x + n, l
  and aucun : int ranalist = epsilon_res 0
  in fun l ->
     try au_moins_un l with Echec -> aucun l
