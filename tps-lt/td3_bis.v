(* énoncé identique à TD03_nat_Exp.v, avec
  - suppression des entraînements sur les listes et sur nat
  - une correction de get
  - des tests devant fonctionner sur eval
  - renomme, decale, bexp à faire 
  *)

(**
Deux objectifs dans ce TD :
- deux structures linéaires qui serviront constamment,
  les listes et les entiers naturels,
  et les pricipes de récurrence associés
- extensions des expressions arithmétiques
*)

(** * Entiers naturels *)

(** En mathématiques, les entiers ne sont plus une notion primitive depuis
    les travaux de Dedekind et Peano au 19e siècle : ils sont obtenus
    à partir de deux constructions élémentaires :
    - l'entier nul, que l'on notera O ;
    - le successeur d'un entier [n] déjà construit, que l'on notera [S n].
    C'est exactement ce que l'on obtient avec le type inductif suivant.
*)

Print nat.

Fact deux : 2 = S (S O).
Proof. (** regarder le but écrit par Coq *) reflexivity. Qed.

(** * Quelques commandes de recherche d'information *)

(** Quelle est la fonction qui est derrière le symbole "+" ? *)
Locate "+".
(**  Print est connu *)
Print Nat.add.
(** Intégration de l'espace de nommage Nat *)
Import Nat.
Locate "+".
(* Quelles fonctions de type [nat -> nat -> nat] sot disponibles ? *)
Search (nat -> nat -> nat).

(** * AST d'expressions arithmétiques, le retour *)

(** On considère des expressions arithmétiques comprenant
    non seulement des opération et des constantes, mais aussi des noms
    de variables.
    Pour simplifier on considère que ces variables s'écriraient "x0", "x1",
    "x2", etc., ce qui permet de les représenter par un simple entier naturel.
    Noter que les constructeurs [Ana] et [Ava] permettent de distinguer
    la constante 2 de la variable x2.
*)

Inductive aexp :=
| Aco : nat -> aexp (* constantes *)
| Ava : nat -> aexp (* variables *)
| Apl : aexp -> aexp -> aexp
| Amu : aexp -> aexp -> aexp
| Amo : aexp -> aexp -> aexp
.

(* Définir les expressions aexp correspondant à
  (1 + x2) * 3 et  (x0 * 2) + x3
 *)

Definition aexp_ex1 : aexp := Amu (Apl (Aco 1) (Ava 2)) (Aco 3).
Definition aexp_ex2 : aexp := Apl (Amu (Ava 0) (Aco 2)) (Ava 3).


(** Pour évaluer une expression représentée par un tel AST,
    on considère un *état*, c'est à dire une association entre
    chaque nom de variable et un valeur dans [nat].
    On choisit de représenter un tel état par une liste d'entiers,
    avec comme convention :
    - le premier élément de cette liste est la valeur associée à x0
    - le second élément de cette liste est la valeur associée à x1
    - et ainsi de suite ;
    - pour les noms restants, la valeur associée est 0.
    Par exemple, dans l'état Cons 3 (Cons 0 (Cons 8 Nil)),
    la valeur associée à x0 est 3, la valeur associée à x1 est 0,
    la valeur associée à x2 est 8, et la valeur associée à x3, x4, etc.
    est 0.
 *)

Inductive state :=
  | Nil : state
  | Cons : nat -> state -> state
.

Definition s_ex1 : state := Cons 3 (Cons 0 (Cons 8 Nil)).

(* ----------------------------------------------------------------------- *)
(** Définition d'une fonction [get] qui rend la valeur associée à xi dans l'état s *)

Fixpoint get (i: nat) (s: state) : nat :=
  match s with
  | Nil => 0
  | Cons v s' => 
    match i with
    | O => v
    | S i' => get i' s'
    end
  end.

Example get_ex1 : get 2 s_ex1 = 8.
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------------- *)

(** Définir une fonction [eval] qui rend la valeur d'une aexp dans l'état s **)


(** Même si la fonction get ci-dessus a été laissée 'Admitted', elle est 
    utilisable dans les questions suivantes.  **)

Fixpoint eval (a: aexp) (s: state) : nat := 
  match a with
  | Aco n => n
  | Ava i => get i s
  | Apl a1 a2 => eval a1 s + eval a2 s
  | Amu a1 a2 => eval a1 s * eval a2 s
  | Amo a1 a2 => eval a1 s - eval a2 s
  end.

Example eval_ex1_ex1 : eval aexp_ex1 s_ex1 = 27.
Proof. reflexivity. Qed.
Example eval_ex2_ex1 : eval aexp_ex2 s_ex1 = 6.
Proof. reflexivity. Qed.


(* ----------------------------------------------------------------------- *)

(** Définir une fonction [renomme] qui prend une aexp [a] et rend [a] où
    les variables correspondant à x0, x1, x2... ont été respectivement
    renommées en x1, x2, x3...  *)

Fixpoint renomme (a: aexp) : aexp :=
  match a with
  | Aco n => Aco n
  | Ava i => Ava (S i)
  | Apl a1 a2 => Apl (renomme a1) (renomme a2)
  | Amu a1 a2 => Amu (renomme a1) (renomme a2)
  | Amo a1 a2 => Amo (renomme a1) (renomme a2)
  end.

(** Définir une fonction [decale] qui prend un état [s] et rend
    l'état dans lequel la valeur de x0 est 0, 
    la valeur de x1 est la valeur de x0 dans [s],
    la valeur de x2 est la valeur de x1 dans [s], 
    la valeur de x3 est la valeur de x2 dans [s], etc. 
    Indication : ce n'est PAS un Fixpoint *)

Definition decale (s : state) : state := Cons 0 s.
    
    (** Démontrer qu'évaluer une expression renommée dans un environnement
    décalé rend la même chose qu'avant *)

Theorem eval_renomme_decale : forall (a: aexp) (s: state),
eval a s = eval (renomme a) (decale s).
Proof.
  intros a s.
  induction a as [|i|a1 IH1 a2 IH2|a1 IH1 a2 IH2|a1 IH1 a2 IH2].
  - reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
Qed. 

(* ----------------------------------------------------------------------- *)
(** ** Expressions booléennes *)

(** Définir un type d'AST nommé bexp pour des expressions booléennes
    comprenant :
    - les constantes booléennes Btrue et Bfalse
    - un opérateur booléen unaire Bnot
    - des opérateurs booléens binaires Band et Bor
    - un opérateur de comparaison représentant le test d'égalité
      entre deux expressions arithmétiques
*)

Inductive bexp : Set := 
| Btrue : bexp
| Bfalse : bexp
| Bnot : bexp -> bexp
| Band : bexp -> bexp -> bexp
| Bor : bexp -> bexp -> bexp
| Beq : bexp -> bexp -> bexp.


(** L'environnenent initial de Coq comprend, en plus de [nat],
    un type énuméré nommé [bool à deux valeurs nommées [true] et [false] 
    ainsi que des fonctions telles que la disjonction entre deux valeurs
    de type [bool].
    Vous pouvez découvrir tout cela au moyen de la commande "Print bool"
    et de la commande Search indiquée ci-dessus, mais on vous demande de 
    reprogrammer les fonctions booléennes par vous-même en utilisant, comme 
    pour [coulfeu], match with suivant le schéma :

      match blabla_booléen with
      | true => ...
      | false => ...
      end

    L'opération de comparaison entre deux entiers devra aussi être programmée.

    Définir une fonction d'évaluation sur bexp en s'appuyant sur ces fonctions.
*)


Fixpoint evalb (b: bexp) (s: state) : bool :=
  match b with
    | Btrue => true
    | Bfalse => false
    | Bnot b' => match evalb b' s with
                | true => false
                | false => true
                end
    | Band b1 b2 => match evalb b1 s, evalb b2 s with
                    | true, true => true
                    | _, _ => false
                    end
    | Bor b1 b2 => match evalb b1 s, evalb b2 s with
                    | false, false => false
                    | _, _ => true
                    end
    | Beq b1 b2 => match evalb b1 s , evalb b2 s with
                    | true, true | false, false => true
                    | _, _ => false
                    end
    end.


Definition bexp_ex1 := Bnot ( Btrue ).
Definition bexp_ex2 := Band ( Btrue ) ( Bfalse ).
Definition bexp_ex3 := Bor ( Btrue ) ( Bfalse ).

Example evalb_ex1_ex1 : evalb bexp_ex1 s_ex1 = false.
Proof. reflexivity. Qed.
Example evalb_ex2_ex1 : evalb bexp_ex2 s_ex1 = false.
Proof. reflexivity. Qed.
Example evalb_ex3_ex1 : evalb bexp_ex3 s_ex1 = true.
Proof. reflexivity. Qed.



(* ----------------------------------------------------------------------- *)