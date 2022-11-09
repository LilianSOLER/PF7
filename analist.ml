(* Analyse descendante récursive sur une liste de caractères *)
(*
 S  ::=  (S)  |  x
*)

(* Le type des fonctions qui épluchent une liste *)
type analist = char list -> char list
(* Le type des fonctions qui épluchent une liste et rendent un résultat *)
type 'r ranalist = char list -> 'r * char list

exception Echec


(* Consommation d'un caractère précis en début de mot *)
let p_parouv : analist = fun l -> match l with
  | '(' :: l -> l
  | _ -> raise Echec

let p_parfer : analist = fun l -> match l with
  | ')' :: l -> l
  | _ -> raise Echec

let p_x : analist = fun l -> match l with
  | 'x' :: l -> l
  | _ -> raise Echec

(* Généralisation *)
let terminal c : analist = fun l -> match l with
  | x :: l when x = c -> l
  | _ -> raise Echec

let terminal_cond (p : char -> bool) : analist = fun l -> match l with
  | x :: l when p x -> l
  | _ -> raise Echec

(* Non terminal vide *)
let epsilon : analist = fun l -> l

let return (res : 'r) : 'r ranalist = fun l -> res, l


(* On vise la grammaire suivante :
    S ::=  '(' S ')'
         | 'x'

  On considère d'abord une grammaire non récursive, en séparant les règles
    S0  ::=  'x'
    S1  ::=  '(' S0 ')'
    S2  ::=  'x'
    S   ::=  S1  |  S2
*)

let p_S0 : analist = terminal 'x'

let p_S1 : analist = fun l ->
  let l1 = terminal '(' l in
  let l2 = p_S0 l1 in
  let l3 = terminal ')' l2 in
  l3

(* Écriture moins gourmande en identificateurs *)
let p_S1 : analist = fun l ->
  let l = terminal '(' l in
  let l = p_S0 l in
  let l = terminal ')' l in
  l

let p_S2 : analist = terminal 'x'

let p_S : analist = fun l ->
  try p_S1 l with Echec -> p_S2 l

(* Tests *)

let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0

let test s = p_S (list_of_string s)
let _ = test "(x)()abc"
let _ = test "xa()bc"
let _ = test "()abc"

(* Grammaire récursive
    S1  ::=  '(' S ')'
    S2  ::=  'x'
    S   ::=  S1  |  S2
*)

let rec p_S : analist =
  let p_S1 : analist = fun l ->
    let l = terminal '(' l in
    let l = p_S l in
    let l = terminal ')' l in
    l
  and p_S2 : analist = fun l ->
    let l = terminal 'x' l in
    l in
  fun l ->
  try p_S1 l with Echec -> p_S2 l

let test s = p_S (list_of_string s)
let _ = test "(((x)))abc"
let _ = test "xa()bc"
let _ = test "()abc"

(* Grammaire récursive avec calcul d'AST *)
type ast = Fin | Pa of ast

let rec p_S : ast ranalist =
  let p_S1 : ast ranalist = fun l ->
    let l = terminal '(' l in
    let a, l = p_S l in
    let l = terminal ')' l in
    Pa (a), l
  and p_S2 : ast ranalist = fun l ->
    let l = terminal 'x' l in
    Fin, l
  in fun l ->
     try p_S1 l with
       Echec -> p_S2 l

let test s = p_S (list_of_string s)
let _ = test "(((x)))abc"
let _ = test "xa()bc"
let _ = test "()abc"


(* ------------------------------------------------------------ *)

(* Les grammaires comportent souvent de la récursion mutuelle
   voici un exemple pour illustrer la syntaxe à employer en OCaml.

  B  ::=  (B)  |   C
  C  ::=  x    |   yC   |  zBC

(Sans détailler la décomposition de S en S1 et S2,
et celle de L en L1, L2 et L3)

 *)

type boite = Emb of boite | Cont of contenu
and contenu = X | Y of contenu | Z of boite * contenu

let rec p_B : boite ranalist =
  let p_B1 : boite ranalist = fun l ->
    let l = terminal '(' l in
    let b, l = p_B l in
    let l = terminal ')' l in
    Emb (b), l
  and p_B2 : boite ranalist = fun l ->
    let c, l = p_C l in
    Cont (c), l
  in fun l ->
     try p_B1 l with
       Echec -> p_B2 l

and p_C : contenu ranalist =
  let p_C1 : contenu ranalist = fun l ->
    let l = terminal 'x' l in
    X, l
  and p_C2 : contenu ranalist = fun l ->
    let l = terminal 'y' l in
    let c, l = p_C l in
    Y (c), l
  and p_C3 : contenu ranalist = fun l ->
    let l = terminal 'z' l in
    let b, l = p_B l in
    let c, l = p_C l in
    Z (b, c), l
  in fun l ->
     try p_C1 l with
       Echec ->
       try p_C2 l with
         Echec ->
          p_C3 l

let _ = p_B (list_of_string "((yz(yyx)yx))a")
