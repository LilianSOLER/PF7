(*Benjamin Bracquier et Lilian Soler*)
(**
Objectif de ce suppport de TD :
familiarisation avec les AST winstr pour le langage WHILE.
*)

(* ------------------------------------------------------------ *)
(** * Familiarisation avec les AST winstr pour le langage WHILE *)

(** ** Syntaxe abstraite *)
Inductive aexp :=
| Aco : nat -> aexp (* constantes *)
| Ava : nat -> aexp (* variables *)
| Apl : aexp -> aexp -> aexp
| Amu : aexp -> aexp -> aexp
| Amo : aexp -> aexp -> aexp
.

Inductive bexp :=
| Btrue : bexp
| Bfalse : bexp
| Bnot : bexp -> bexp
| Band : bexp -> bexp -> bexp
| Bor : bexp -> bexp -> bexp
| Beq : bexp -> bexp -> bexp (* test égalité de bexp *)
| Beqnat : aexp -> aexp -> bexp (* test égalité d'aexp *)
.

Inductive winstr :=
| Skip   : winstr
| Assign : nat -> aexp -> winstr
| Seq    : winstr -> winstr -> winstr
| If     : bexp -> winstr -> winstr -> winstr
| While  : bexp -> winstr -> winstr
.

(** Le langage IMP : comme WHILE mais sans While *)
Inductive instr :=
| ISkip   : instr
| IAssign : nat -> aexp -> instr
| ISeq    : instr -> instr -> instr
| IIf     : bexp -> instr -> instr -> instr
.

(** Définir les AST des programmes suivants *)
(** x3 := 5 * x2 *)
Example P1 : instr := IAssign 3 (Amu (Aco 5) (Ava 2)).

(** x2 := x2 + 1 *)
Example P2 : instr := IAssign 2 (Apl (Ava 2) (Aco 1)).

(** if x1 = x3 then (x2 := x2 + 1; x2 := x2 + 1) else x3 := 5 * x2 *)
Example P3 : instr := IIf (Beqnat (Ava 1) (Ava 3)) (ISeq (IAssign 2 (Apl (Ava 2) (Aco 1))) (IAssign 2 (Apl (Ava 2) (Aco 1)))) (IAssign 3 (Amu (Aco 5)  (Ava 2))). 

(** ** Sémantique fonctionnelle *)

Inductive state :=
  | Nil : state
  | Cons : nat -> state -> state
.

(** On se donne des notations préalables pour faciliter la présentation *)
Notation "[]" := Nil.
Notation "x :: y" := (Cons x y).

(** L'appel [get i s] rend la valeur associée à xi dans l'état s *)
Fixpoint get (i: nat) (s: state) : nat :=
  match s with
  | []     => 0
  | v :: s' =>
    match i with
    | O => v
    | S i' => get i' s'
    end
  end.

(** *** Sémantique fonctionnelle de aexp*)
Fixpoint evalA (a: aexp) (s: state) : nat :=
  match a with
  | Aco n => n
  | Ava x => get x s
  | Apl a1 a2 =>  evalA a1 s + evalA a2 s
  | Amu a1 a2 =>  evalA a1 s * evalA a2 s
  | Amo a1 a2 =>  evalA a1 s - evalA a2 s
  end.


(** *** Sémantique fonctionnelle de bexp*)
Definition eqboolb b1 b2 : bool :=
  match b1, b2  with
  | true, true   => true
  | false, false => true
  | _ , _        => false
  end.

Fixpoint eqnatb n1 n2 : bool :=
   match n1, n2 with
  | O, O         => true
  | S n1', S n2' => eqnatb n1' n2'
  | _, _         => false
  end.

 Fixpoint evalB (b : bexp) (s : state) : bool :=
  match b with
  | Btrue => true
  | Bfalse => false
  | Bnot b => negb (evalB b s)
  | Band e1 e2 => (evalB e1 s) && (evalB e2 s)
  | Bor e1 e2 => (evalB e1 s) || (evalB e2 s)
  | Beq e1 e2 => eqboolb (evalB e1 s) (evalB e2 s)
  | Beqnat n1 n2 => eqnatb (evalA n1 s) (evalA n2 s)
  end.


(** *** Sémantique fonctionnelle de IMP *)

(** La mise à jour d'une variable [v] par un nouvel entier [n]
    dans un état [s] s'écrit [update s v n'].
    Cette fonction n'échoue jamais et écrit la valeur à sa place même
    si elle n'est pas encore définie dans l'état [s]. *)

(** À définir en TD *)
(** [update i v s] rend l'état dans lequel xi vaut [v],
    les valeurs des autres variables étant celles de [s].
    Attention à bien traiter tous les cas, notament ceux
    où l'état est représenté par une liste vide : tout se passe
    comme si, à la place, on avait une liste comprenant
    suffisamment de 0 (valeur par défaut).
 *)
Fixpoint update (i:nat) (v:nat) (s:state) : state :=
  match s 



(** Quelques états pour faire des tests *)
(** S1 est un état dans lequel la variable "x0" vaut 1 et la variable "x1"
    vaut 2 et toutes les autres valent 0 (valeur par défaut) *)

Example S1 := 1 :: 2 :: Nil.
Example S2 := 0 :: 3 :: Nil.
Example S3 := 0 :: 7 :: 5 :: 41 :: Nil.

Example S4 :=
  let s1 := update 4 1 S1 in
  let s2 := update 3 2 s1 in
  let s3 := update 2 3 s2 in
  let s4 := update 2 3 s3 in
  update 0 5 s4.
Example test_S4 : S4 = 5 :: 2 :: 3 :: 2 :: 1 :: [].
Proof. Admitted. (*reflexivity. Qed.*)

(** Peut s'écrire dans une premier temps avec update laissé "Admitted". *)
Fixpoint evalI (i : instr) (s : state) : state :=
  match i with
  | ISkip       => s
  | IAssign x a => update x (evalA a s) s
  | ISeq i1 i2  => evalI i2 (evalI i1 s)    
  | IIf b i1 i2 => if evalB b s then evalI i1 s else evalI i2 s       
  end.

(** La pré-commande "Fail" indique que l'on s'attend à un échec *)
(** La présence de [{struct i}] indique que l'argument devant
    décroître structurellement est [i] ;
    Pour [evalI] on aurait pu le préciser aussi mais Coq a su
    reconstruire cette information à partir du corps de la fonction.
*)
Fail Fixpoint evalW (i : winstr) (s : state) {struct i} : state :=
  (** à compléter, en expliquant le diagnostic rendu par Coq *)
  match i with
  | Skip       => s
  end.

(** ** Tests *)

Example test1 : evalI P1 S1 = 1 :: 2 :: 0 :: 0 :: [].
Proof. reflexivity. Qed.

Example test2 : evalI P1 S4 = 5 :: 2 :: 3 :: 15 :: 1 :: [].
Proof. reflexivity. Qed.

Example test3 : evalI P3 S1 = 1 :: 2 :: 0 :: 0 :: [].
Proof. reflexivity. Qed.

Example test4 : evalI P3 S4 = 5 :: 2 :: 5 :: 2 :: 1 :: [].
Proof. reflexivity. Qed.

