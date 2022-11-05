

(*Benjamin Bracquier et Lilian Soler*)

 
type analist = char list -> char list

type 'res ranalist = char list -> 'res * char list

type ('token, 'res) ranalist_gen = 'token list -> 'res * 'token list

exception Echec

let epsilon : analist = fun l -> l
let epsilon_res (info : 'res) : 'res ranalist =
  fun l -> (info, l)


let terminal c : analist = fun l -> match l with
  | x :: l when x = c -> l
  | _ -> raise Echec

let terminal_cond (p : char -> bool) : analist = fun l -> match l with
  | x :: l when p x -> l
  | _ -> raise Echec

let terminal_res (f : 'term -> 'res option) : 'res ranalist =
  fun l -> match l with
  | x :: l -> (match f x with Some y -> y, l | None -> raise Echec)
  | _ -> raise Echec

(*Exercice 8.1 du poly de TD *)
(*1:grammaire*)

(*
U ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
A ::= U . C
C ::= A | epsilon

 *)

(*2*)



let est_chiffre c = '0' <= c && c <= '9'

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

let readfile : string -> string = fun nomfic ->
let ic = open_in nomfic in
really_input_string ic (in_channel_length ic);;


let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0
let truc=readfile "chiffres.txt";;

let truc2 =list_of_string truc;;

let truc3=chiffres truc2;;

(*3*)
let rec sommechiffres : int ranalist =
  let rec au_moins_un : int ranalist = fun l ->
    let x, l = un_chiffre l in
    let n, l = sommechiffres l in
    x + n, l
  and aucun : int ranalist = epsilon_res 0
  in fun l ->
     try au_moins_un l with Echec -> aucun l



let truc4=sommechiffres truc2;;

(*4*)



(*Exercice 8.3 du poly de TD *)
(*1*)
(*pas sur de ces types*)
type joueur = Noir | Blanc;;
type longueur = Longueur of int;;
type largeur = Largeur of int ;;
type partie = {longueur:longueur;largeur:largeur};;
type coup ={joueur: joueur;couplongueur:longueur;couplargeur:largeur};;

(*2*)
