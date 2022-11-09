(* Analyse descendante récursive sur une liste de caractères *)
(*
 S  ::=  (S)  |  x
*)

(* Pour les tests *)

let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0

(* Le type des aspirateurs (fonctions qui aspirent le préfixe d'une liste) *)
type analist = char list -> char list
(* Le type des aspirateurs qui, en plus, rendent un résultat *)
type 'r ranalist = char list -> 'r * char list

(* Idem en plus général (utile lorsqu'on enchaîne analyse lexicale puis syntaxique). *)
type ('token, 'res) ranalist_gen = 'token list -> 'res * 'token list

exception Echec

(* Aspirateur d'un caractère précis en début de liste *)
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

(* Non-terminal vide *)
let epsilon : analist = fun l -> l

let epsilon_res (res : 'r) : 'r ranalist = fun l -> res, l


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

let test s = p_S (list_of_string s)
let _ = test "(x)()abc"
let _ = test "xa()bc"
let _ = try test "()abc" with Echec -> list_of_string "ECHEC"

(* Grammaire récursive
    S1  ::=  '(' S ')'
    S2  ::=  'x'
    S   ::=  S1  |  S2
*)

let rec p_S1 : analist = fun l ->
  let l = terminal '(' l in
  let l = p_S l in
  let l = terminal ')' l in
  l
and p_S2 : analist = fun l ->
  let l = terminal 'x' l in
  l
and p_S : analist = fun l ->
  try p_S1 l with Echec -> p_S2 l

let test s = p_S (list_of_string s)
let _ = test "(((x)))abc"
let _ = test "xa()bc"
let _ = try test "()abc" with Echec -> list_of_string "ECHEC"

(* Grammaire récursive avec calcul d'AST *)
type ast = Fin | Pa of ast

let rec p_S1 : ast ranalist = fun l ->
  let l = terminal '(' l in
  let a, l = p_S l in
  let l = terminal ')' l in
  Pa (a), l
and p_S2 : ast ranalist = fun l ->
  let l = terminal 'x' l in
  Fin, l
and p_S : ast ranalist = fun l ->
  try p_S1 l with Echec -> p_S2 l

let test s = p_S (list_of_string s)
let _ = test "(((x)))abc"
let _ = test "xa()bc"
let _ = try test "()abc" with Echec -> (Fin, list_of_string "ECHEC")


(* ------------------------------------------------------------ *)

(* Les grammaires comportent souvent de la récursion mutuelle
   voici un exemple pour illustrer la syntaxe à employer en OCaml.

  B  ::=  (B)  |   C
  C  ::=  x    |   yC   |  zBC

 On décompose B ainsi :
  B1 ::= (B)
  B2 ::= C
  B  ::= B1 | B2

 Et C de manière semblable :
  C1 ::= x
  C2 ::= yC
  C3 ::= zBC
  C  :: C1 | C2 | C3

 *)

type boite = Emb of boite | Cont of contenu
and contenu = X | Y of contenu | Z of boite * contenu

let rec p_B1 : boite ranalist = fun l ->
  let l = terminal '(' l in
  let b, l = p_B l in
  let l = terminal ')' l in
  Emb (b), l
and p_B2 : boite ranalist = fun l ->
  let c, l = p_C l in
  Cont (c), l
and p_B : boite ranalist = fun l ->
  try p_B1 l with
  Echec -> p_B2 l

and p_C1 : contenu ranalist = fun l ->
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
and p_C : contenu ranalist = fun l ->
  try p_C1 l with
    Echec ->
  try p_C2 l with
    Echec ->
  p_C3 l

let _ = p_B (list_of_string "((yz(yyx)yx))a")

(* On peut également cacher B1, B2, C1, 2 et C3 de la manière suivante. *)

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

