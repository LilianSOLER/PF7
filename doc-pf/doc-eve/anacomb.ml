(* Analyse descendante récursive sur une liste avec des combinateurs *)

(* Utilitaire pour les tests *)

let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0

(* Le type des fonctions qui épluchent une liste de terminaux *)
type 'term analist = 'term list -> 'term list

exception Echec

(* terminal constant *)
let terminal (c : 't) : 't analist = function
  | x :: l when x = c -> l
  | _ -> raise Echec

(* terminal conditionnel *)
let terminal_cond (p : 'term -> bool) : 'term analist = function
  | x :: l when p x -> l
  | _ -> raise Echec

(* non-terminal vide *)
let epsilon : 'term analist = fun l -> l

(* ------------------------------------------------------------ *)
(* Combinateurs d'analyseurs purs *)
(* ------------------------------------------------------------ *)

(* a suivi de b *)
let (-->) (a : 'term analist) (b : 'term analist) : 'term analist =
  fun l -> let l = a l in b l

(* Choix entre a ou b *)
let (-|) (a : 'term analist) (b : 'term analist) : 'term analist =
  fun l -> try a l with Echec -> b l

(* ---------------------------------- *)
(* Grammaire non récursive *)

(*
    S0  ::=  'x'
    S   ::=  '(' S0 ')'  |  'x'
*)

let p_S0 : char analist = terminal 'x'

let p_S : char analist =
    (terminal '('  -->  p_S0  -->  terminal ')')
 -| (terminal 'x')

(* Tests *)

let echec test s = try (let _ = test s in false) with Echec -> true

let test s = p_S (list_of_string s)
let _ = test "(x)abc"
let _ = test "xabc"

(* ---------------------------------- *)
(* Grammaire récursive *)

(*
    S   ::=  '(' S ')'  |  'x'
*)


(*
   En OCaml, x |> f est une autre notation de f x.
   Le let rec impose l'explicitation d'au moins un argument,
   d'où le démarrage par fun l -> l |>
*)

let rec p_S : char analist = fun l ->  l |>
     (terminal '('  -->  p_S  -->  terminal ')')
  -| (terminal 'x')

(* Variante avec ε
    S   ::=  '(' S ')'  |  ε
*)


let rec p_S : char analist = fun l ->  l |>
     (terminal '('  -->  p_S  -->  terminal ')')
  -| epsilon

(* ------------------------------------------------------------ *)
(* Combinateurs d'analyseurs
   avec calcul supplémentaire, ex. d'un AST *)
(* ------------------------------------------------------------ *)

(* Le type des fonctions qui épluchent une liste et rendent un résultat *)
type ('res, 'term) ranalist = 'term list -> 'res * 'term list

(* Un epsilon informatif *)
let epsilon_res (info : 'res) : ('res, 'term) ranalist =
  fun l -> (info, l)

(* Terminal conditionnel avec résultat *)
(* [f] ne retourne pas un booléen mais un résultat optionnel *)
let terminal_res (f : 'term -> 'res option) : ('res, 'term) ranalist =
  fun l -> match l with
  | x :: l -> (match f x with Some y -> y, l | None -> raise Echec)
  | _ -> raise Echec

(* a sans résultat suivi de b donnant un résultat *)
let ( -+>) (a : 'term analist) (b : ('res, 'term) ranalist) :
      ('res, 'term) ranalist =
  fun l -> let l = a l in b l

(* a rendant un résultat suivi de b rendant un résultat *)
let (++>) (a : ('resa, 'term) ranalist) (b : 'resa -> ('resb, 'term) ranalist) :
      ('resb, 'term) ranalist =
  fun l -> let (x, l) = a l in b x l

(* Choix entre a ou b informatifs *)
let (+|) (a : ('res, 'term) ranalist) (b : ('res, 'term) ranalist) :
      ('res, 'term) ranalist =
  fun l -> try a l with Echec -> b l

(* ---------------------------------- *)
(*
    S   ::=  '(' S ')'  |  'x'
*)

type ast = Fin | Pa of ast

let rec p_S : (ast, char) ranalist = fun l ->  l |>
     (terminal '('  -+>  p_S  ++>  (fun a -> terminal ')'  -+>  epsilon_res (Pa (a))))
  +| (terminal 'x'  -+>  epsilon_res Fin)

(* ---------------------------------- *)
(* Exemple avec récursion mutuelle

  B  ::=  (B)  |  C
  C  ::=  x    |  yC   |  zBC  |  ε

 *)

type boite = Emb of boite | Cont of contenu
and contenu = X | Y of contenu | Z of boite * contenu | Quedalle

let rec p_B : (boite, char) ranalist = fun l ->  l |>
    (terminal '('  -+>  p_B  ++>  fun b -> terminal ')'  -+>  epsilon_res (Emb (b)))
 +| (p_C  ++>  fun c -> epsilon_res (Cont (c)))

and p_C : (contenu, char) ranalist = fun l ->  l |>
    (terminal 'x'  -+>  epsilon_res X)
 +| (terminal 'y'  -+>  p_C  ++>  fun c -> epsilon_res (Y (c)))
 +| (terminal 'z'  -+>  p_B  ++>  fun b -> p_C  ++>  fun c -> epsilon_res (Z (b, c)))
 +| epsilon_res Quedalle

let _ = p_B (list_of_string "((yz(yyx)yx))a")
