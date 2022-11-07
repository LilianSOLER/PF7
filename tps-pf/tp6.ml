

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

let rec (horner : int -> int ranalist) =
  fun a l  ->
  try au_moins_un a l with Echec -> aucun a l 
and au_moins_un : int -> int ranalist = fun a l ->
  let x, l = un_chiffre l in
  let n, l = horner  (a*10 +x) l  in
  n, l
and aucun : int ->int ranalist = fun a l ->epsilon_res a l


(*Exercice 8.3 du poly de TD *)

(*
P ::= noir | blanc
C ::= ( P int int )
Cl ::= ε | C Cl
S ::= ( int int ) Cl
           *)

(*1*)
(*type*)
(*2 joueur*)
type joueur = Noir | Blanc;;
(*correspond à C=joueur et ou est le coup *)
type coup = joueur * int * int;;
(*correspond à la dimension du plateau et la liste de tous les coups*)
type partie = int * int * coup list;;

(*2*)
(*dans ce type,on doit avoir tous les symbole qui peuvent apparaitre*)
type token =
  | ParG (* parenthèse gauche *)
  | ParD (* parenthèse droite *)
  | Blanc(*quand il y a blanc et noir*)
  | Noir
  | Int of int (*chiffres*)


(*reconnaitre le token noir*)
let p_noir = fun l ->
    match l with
    | 'n' :: 'o' :: 'i' :: 'r' :: apres -> (Noir, apres)
    | _ -> raise Echec;;
(*reconnaitre le token blanc*)
let p_blanc = fun l ->
    match l with
    | 'b' :: 'l' :: 'a' :: 'n' :: 'c' :: apres -> (Blanc, apres)
    | _ -> raise Echec;;
(*reconnaitre le token parenthese droite*)
let p_parouv = fun l -> match l with
  | '(' :: apres -> (ParG,apres)
  | _ -> raise Echec;;
(*reconnaitre le token parenthese gauche*)
let p_parfer = fun l -> match l with
  | ')' :: apres -> (ParD,apres)
  | _ -> raise Echec;;

(*reconnaitre chaque chiffre*)
let parse_int = function
  | [] -> raise Echec
  | '0' :: xs -> (0, xs)
  | '1' :: xs -> (1, xs)
  | '2' :: xs -> (2, xs)
  | '3' :: xs -> (3, xs)
  | '4' :: xs -> (4, xs)
  | '5' :: xs -> (5, xs)
  | '6' :: xs -> (6, xs)
  | '7' :: xs -> (7, xs)
  | '8' :: xs -> (8, xs)
  | _ :: xs -> (9, xs);;

(*reconnaitre le token chiffres avec parse_int *)
let p_int  = fun l ->
  let (i, suite) = parse_int l in
    Int i;;

(*rend le token en tete donc on passe par toutes les symboles possibles *)
let token_here = fun l ->
    try
        p_parouv l
    with Echec -> try
        p_parfer l
    with Echec -> try
        p_blanc l
    with Echec -> try
        p_noir l
    with Echec ->
        let (i, suite) = parse_int l in
        (Int i, suite);;

(*enleve les espaces*)
let rec espace = fun l ->
    match l with
    | ' ' :: apres -> espace apres
    | _ -> l;;

(*rend le 1er token en passant les espaces*)
let next_token = fun l ->
  token_here (espace l);;

(*retourne tout les tokens*)
let rec tokens = fun l ->
    if l = [] then
        []
    else
        let (token, suite) = next_token l in
        token :: (tokens suite);;


(*3*)
