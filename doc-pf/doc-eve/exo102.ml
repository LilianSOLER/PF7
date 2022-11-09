(*POITEVIN Eve & REYGNER Etienne *)

let string_to_list s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0
;;

type analist = char list -> char list

exception Echec

(* terminal constant *)
let terminal c : analist = fun l -> match l with
  | x :: l when x = c -> l
  | _ -> raise Echec

(* terminal conditionnel *)
let terminal_cond (p : 'term -> bool) : analist = function
  | x :: l when p x -> l
  | _ -> raise Echec

(* non-terminal vide *)
let epsilon : analist = fun l -> l

(* Composition séquentielle : a suivi de b *)
let (-->) (a : analist) (b : analist) : analist =
  fun l -> let l = a l in b l

(* Choix entre a ou b *)
let (-|) (a : analist) (b : analist) : analist =
  fun l -> try a l with Echec -> b l

type 'res ranalist = char list -> 'res * char list

let epsilon_res (info : 'res) : 'res ranalist =
  fun l -> (info, l)

let terminal_res (f : char -> 'res option) : 'res ranalist =
  fun l -> match l with
    | x :: l -> (match f x with Some y -> y, l | None -> raise Echec)
    | _ -> raise Echec

(* Choix entre a ou b informatifs *)
let (+|) (a : 'res ranalist) (b : 'res ranalist) : 'res ranalist =
  fun l -> try a l with Echec -> b l

(* a sans résultat suivi de b donnant un résultat *)
let ( -+>) (a : analist) (b : 'res ranalist) : 'res ranalist =
  fun l -> let l = a l in b l

(* a rendant un résultat suivi de b sans résultat *)
let (+->) (a : 'res ranalist) (b : analist) : analist =
  fun l -> let (x, l) = a l in b l

(* a rendant un résultat suivi de b rendant un résultat *)
let (++>) (a : 'resa ranalist) (b : 'resa -> 'resb ranalist) : 'resb ranalist =
  fun l -> let (x, l) = a l in b x l
;;

(* Question 1 *)

type joueur = Blanc | Noir;;

type coup = joueur * int * int;;

type partie = int * int * coup list;;

(* Question 2 *)

type case = int * int * joueur;;

type plateau = case list;;

(* Question 3 *)

type token = ParOuv
           | ParFer
           | Couleur of joueur
           | Nombre of int
;;

(* c ::= u c | epsilon *)

let val_chiffre : char -> int option = fun c ->
  match c with
  | '0' .. '9' -> Some (Char.code c - Char.code '0')
  |_ -> None

let un_chiffre : int ranalist =
  terminal_res val_chiffre

let rec chiffres : int -> int ranalist =
  fun a l -> l |>
               (un_chiffre ++> fun x -> chiffres (a*10+x)) +| epsilon_res a
;;

let test s = chiffres 0 (string_to_list s);;
let _ = test "153abc"
let _ = test "1abc"

let token_here : token ranalist = fun l -> l |>
                                             (terminal '(' -+> epsilon_res ParOuv)
                                             +| (terminal ')' -+> epsilon_res ParFer)
                                             +| (terminal 'b' --> terminal 'l' --> terminal 'a' --> terminal 'n' --> terminal 'c' -+> epsilon_res (Couleur Blanc))
                                             +| (terminal 'n' --> terminal 'o' --> terminal 'i' --> terminal 'r' -+> epsilon_res (Couleur Noir))
                                             +| (un_chiffre ++> fun c -> chiffres c ++> fun i -> epsilon_res (Nombre i))

;;

let test s = token_here (string_to_list s);;
let _ = test "123abc";;
let _ = test "(abc";;
let _ = test ")abc";;
let _ = test "blancabc";;
let _ = test "noirabc";;

let rec espaces : analist = fun l -> l |>
                                       (terminal ' ' --> espaces)
                                       -| (epsilon);;

let test s = espaces (string_to_list s);;
let _ = test "   ab c";;

let next_token : token ranalist = fun l -> l |>
                                             espaces -+> token_here;;

let test s = next_token (string_to_list s);;
let _ = test "   noirab c";;

let rec tokens : token list ranalist = fun l -> l |>
                                                  (next_token ++> fun t -> tokens ++> fun t2 -> epsilon_res (t :: t2))
                                                  +| (epsilon_res []);;
let test s = tokens (string_to_list s);;
let _ = test "    ( noir  12 34 )"

