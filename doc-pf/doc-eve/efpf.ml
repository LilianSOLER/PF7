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


(* Consigne générale : remplacer les
              raise (TODO "...")
   par votre code. Ne changer pas le nom des fonctions.

  Pré et post-condition : ce fichier compile sans erreur

   Il y a 3 types de questions (dans l'ordre d'apparition) :
   - des questions [**] que vous devriez réussir si vous avez fait et compris le projet sans les extensions
   - des questions [***] qui concernent les extensions facultatives
   - des questions [*] que vous n'avez pas besoin de traiter si vous avec réussi au moins 2
     des questions mieux étoilées

   Il n'est pas nécessaire de traiter plus de 2 questions à [**] ou [***] pour obtenir une note satisfaisante
   ni de traiter toutes les questions pour obtenir la note maximale.    
   *)

let prenom: string = "Eve"
let nom: string = "Poitevin"
    
(*  Vous  pouvez  utilisez  l'exception PRESQUE  si  vous  avez  un
   programme qui  marche presque.  Si  une telle exception  est levée,
   nous irons lire votre code pour voir s'il mérite quelques points.

    ex  :
    let incr x =
       (* x+2  *)
      raise (PRESQUE "mon incrémenteur incrémente, mais de 2 au lieu de 1, et je ne trouve pas mon erreur")

    *) 
exception PRESQUE of string
exception TODO of string

(* Questions projets

   Voici 2 programmes écrit dans le langage loop, pour lequel on peut
   - manipuler 2 variables ("a" et "b")
   - exécuter des instructions en séquence (";")
   - incrémenter une des 2 variables ("I a")
   - remettre la valeur d'une variable à 0 ("R a")
   - boucler entre 0 et 9 fois "L 3 ( ... )" 

   Voici 2 exemples de  programmes écrits dans ce langage
   *)
      
let prog1 = "Ra;
R b;
I a; I a;
L 4 (
  I a;
  R a;
  I b;
  L 5 ( I a )
)
";;
let prog2 = "Ra;
R b;
I a; I a;
L 9 (
  I a;
  R a;
  I b;
  L 5 ( I a )
)
";;

(*  [**]  Écrivez  une   grammaire  reconnaissant  les  2  programmes
   ci-dessus. Faites le dans  la chaîne (string) grammaire ci-dessous
   *)

let grammaire:string =
"V ::= a | b
B ::= 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
S ::= I L | epsilon
L ::= ; S | epsilon
   I ::= 
   | I V 
   | R V 
   | L B ( S )  
   | epsilon
"

(*  Voici un  analyseur  lexical  pour notre  langage.  Notez que  ce
   programme enlève les blancs et les retours à la ligne *)
let lexer : string -> char list = fun s ->
  let blank = function
    | ' ' | '\n' | '\t' -> true
    | _ -> false
  in
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else if blank s.[i] then boucle (i+1) else s.[i] :: boucle (i+1)
  in boucle 0;;
    
(* En utilisant le fichier anacomb.ml qui vous est fourni... *)

#use "anacomb.ml";;

(*  ...    écrivez  un  analyseur  syntaxique   (p_P)  permettant  de
   reconnaître  les programmes  définis  par votre  grammaire, et  de
   construire  un arbre  syntaxique dont  le type  en ocaml  vous est
   fourni ci-dessous *)

type var = char
type linstr =
  | Skip
  | Incr of var
  | Reset of var
  | Seq of linstr * linstr
  | Loop of int * linstr 

let chiffre : (int, char) ranalist =
  let valchiffre : char -> int option = fun c ->
    match c with
    | '0' .. '9' -> Some (Char.code c - Char.code '0')
    |_ -> None
  in terminal_res valchiffre

let lettre : (char, char) ranalist =
  let char_lettre : char -> char option = fun c ->
    match c with
    | 'a' .. 'z' -> Some c
    |_ -> None
  in terminal_res char_lettre

let rec p_P : (linstr, char) ranalist = fun l -> l |>
                                                  (terminal 'R' -+> lettre ++> fun a -> epsilon_res (Reset (a)))
                                                  +| (terminal 'I' -+> lettre ++> fun a -> epsilon_res (Incr (a)))
                                                  +| (terminal 'L' -+> chiffre ++> fun a -> terminal '(' -+> p_S ++> fun b -> terminal ')' -+> epsilon_res (Loop (a, b)))

and p_S : (linstr, char) ranalist = fun l -> l |>
                                               (p_P ++> fun a -> p_S ++> fun b -> epsilon_res (Seq (a, b)))
                                               +| (terminal ';' -+> p_S)
                                               +| (epsilon_res (Skip));;


let test s = p_P (lexer s)

let _ = test prog1
let _ = test prog2

(* Interpréteur *)
(* Nous allons maintenant écrire  un interpréteur pour les programmes
   écrit dans notre petit langage. *)
    
type etat = int list
type config = etat * linstr

let (set : char -> int -> etat  -> etat) = fun x v e ->
  match x, e with
  | 'a', [_;vb] -> [v;vb]
  | 'b', [va;_] -> [va;v]
  | _,_ -> failwith "ce langage ne comprend que les variables a et b"
let (get : char  -> etat -> int) = fun x e ->
  match x, e with
  | 'a', [va;_vb] -> va
  | 'b', [_;vb] -> vb
  | _,_ -> failwith "ce langage ne comprend que les variables a et b"

let init: etat = [0;0]
    
(* Question 2 [**]

   Écrire une fonction qui exécute une instruction d'un programme *)
let rec (faire_un_pas : linstr ->  etat -> config) =
  fun p e -> match p with
  | Skip -> (e, p)
  | Incr v  -> ((set v ((get v e)+1) e), p)
  | Reset v -> ((set v 0 e), p)
  | Seq (i1, i2) -> let (etat, linstr) = (faire_un_pas i1 e) in (faire_un_pas i2 etat)
  | Loop (b, i) -> match b with
                         | 0 -> (e, Skip)
                         | _ -> faire_un_pas (Seq (i, Loop (b-1, i))) e
;;
    
(* Écrire une fonction qui exécute toutes les instructions d'un programme  *)

(* Je n'ai pas eu le temps de finir, et donc de faire executer


let rec (boucleExecution : linstr ->  etat -> config) =
  fun p e -> match p with
  | Skip -> (e, p)
  | _ -> boucleExecution (faire_un_pas );;

let (executer : linstr -> etat) =
  fun p ->
  raise (TODO "executer") *)

(***********************************************************************************)
(* Extensions *)

(* [***] Modifier  votre   interpréteur  pour  qu'il  compte   le  nombre
   d'instruction exécutée.

   nb : toutes les instructions comptent, même l'entrée dans une boucle.
*)
let (executer_et_compter : linstr -> int * etat) =
  fun p ->
  raise (TODO "executer_et_compter")

(* [***] Étendez  votre grammaire, votre p_P, et  votre executer pour
   traiter le cas du prog3 ci-dessous qui utilise des Threads *)
let prog3 = "R b; { R a; L 3 (I a) || R b; L 4 (I b) }"

type linstrt =
  | Skip
  | Incr of var
  | Reset of var
  | Seq of linstrt * linstrt
  | Threads of linstrt * linstrt
  | Loop of int * linstrt

let (executer_t : linstrt -> etat) =
  fun p ->
  raise (TODO "executer_t")

let (executer_et_compter_t : linstrt -> int * etat) =
  fun p ->
  raise (TODO "executer_et_compter_t")

(* [***] Modifiez  votre code en remplacant dans  ranalist les listes
   par des listes paresseuses à l'aide du fichier anacomb_lazy.ml qui
   vous est fournit.

   Si vous  décidez de traiter  cette question, changez la  valeur de
   l'identificateur lazy_list ci-dessous *)
let lazy_list = false

(***********************************************************************************)
(* Questions  de rattrapage (à ne  faire que si vous  n'arrivez pas à
   faire au moins 2 des questions précédentes) *)

(* [*]  Écrivez des versions de  get et set qui  fonctionnent avec un
   nombre quelconque de variables *)
let (set2 : char -> int -> etat  -> etat) = fun x v e ->
  raise (TODO "set2")
let (get2 : char  -> etat -> int) = fun x e ->
  raise (TODO "get2")

(* [*]  Écrivez des versions de  get et set qui  utilisent des arbres
   binaires de recherche plutôt que des listes *)
let (set3 : char -> int -> etat  -> etat) = fun x v e ->
  raise (TODO "set3")
let (get3 : char  -> etat -> int) = fun x e ->
  raise (TODO "get3")
