(*SOLER Lilian - INFO 4 - TD + 1h*)

(**
Deux objectifs dans ce TD :
- deux structures linéaires qui serviront constamment,
  les listes et les entiers naturels,
  et les pricipes de récurrence associés
- extensions des expressions arithmétiques
*)

(** * Listes et entiers naturels *)

(** ** Listes *)

(**
On oublie pour l'instant les entiers prédéfinis en Coq,
car on les refera à partir de zéro (c'est le cas de le dire).

Pour avoir des listes de quelque chose, on reprend donc le type
des couleurs vu auparavant.
On verra plus tard que, comme en OCaml, Coq permet de
travailler sur des listes d'éléments dont le type n'est pas fixé
a priori.
 *)

 Inductive coulfeu : Set :=
 | Vert : coulfeu
 | Orange : coulfeu
 | Rouge : coulfeu
.

Inductive listc : Set  :=
 | Nilc  : listc
 | Consc : coulfeu -> listc -> listc
.

Example l1 := Consc Vert (Consc Rouge Nilc).
Example l2 := Consc Orange (Consc Orange Nilc).

(** La fonction la plus importante sur les listes est la concaténation,
   vue en PF sous le nom append.
   Elle se définit récursivement par analyse (ou filtrage) du *premier* argument
*)

Fixpoint app u v : listc :=
 match u with
 | Nilc       => v
 | Consc x u' => Consc x (app u' v)
 end.

Compute (app l1 l2).

(** Exercice à faire à la maison :
   tenter de définir app par filtrage du second argument *)

(** Remarque : pour une définition récursive on écrit
   [Fixpoint app u v := ]
   plutôt que
   [Definition app := fun u v => ].
*)

(** On commence par deux lemmes dont l'énoncé est semblable
   ([Nilc] est neutre à gauche et à droite de [app])
   mais dont les démonstrations sont très différentes *)

Theorem app_Nilc_l : forall l, app Nilc l = l.
Proof.
 intro l. cbn [app]. reflexivity.
Qed.

(** Exprimer cette preuve en français *)

Theorem app_Nilc_r : forall l, app l Nilc = l.
Proof.
 intro l. cbn [app]. (* aucun effet : pourquoi ? *) (* Pcq l peut être cons ou nil donc il ne peut rien faire*)
  induction l as [(* Nil *) | (* Cons *) x l' Hrecl']. (* on fait une induction sur l *)
  - reflexivity.
  - cbn [app]. rewrite Hrecl'. reflexivity.
Qed.

(** Lemme fondamental : app est associative *)

Theorem app_assoc : forall u v w, app u (app v w) = app (app u v) w.
Proof.
 intros u v w. (** équivalent à intro u. intro v. intro w. *)
 (** Comme app analyse son premier argument on tente une récurrence sur u *)
 induction u as [ (* Nil *) | (* Cons *)x u' Hrecu'].
  - cbn [app]. reflexivity.
  - cbn [app]. rewrite Hrecu'. reflexivity.
  Qed.


(* ----------------------------------------------------------------------- *)
(** DEBUT QUESTIONS FACULTATIVES (1) *)

Fixpoint renv u : listc :=
 match u with
 | Nilc       => Nilc
 | Consc x u' => app (renv u') (Consc x Nilc)
 end.

(* Penser à utiliser les théorèmes précédents *)
Lemma app_renv : forall u v, renv (app u v) = app (renv v) (renv u).
Proof.
  intros u v.
  induction u as [ (* Nil *) | (* Cons *)x u' Hrecu'].
  - cbn [app renv]. rewrite app_Nilc_r. reflexivity.
  - cbn [app renv]. rewrite Hrecu'. rewrite app_assoc. reflexivity.
Qed.

Lemma renv_renv : forall u, renv (renv u) = u.
Proof.
  intro u.
  induction u as [ (* Nil *) | (* Cons *)x u' Hrecu'].
    - cbn[renv]. reflexivity.
    - cbn[renv app]. rewrite app_renv. rewrite Hrecu'. cbn[renv app]. reflexivity.
Qed.
(** FIN QUESTIONS FACULTATIVES (1) *)
(* ----------------------------------------------------------------------- *)

(** ** Entiers naturels *)

(** En mathématiques, les entiers ne sont plus une notion primitive depuis
   les travaux de Dedekind et Peano au 19e siècle : ils sont obtenus
   à partir de deux constructions élémentaires :
   - l'entier nul, que l'on notera O ;
   - le successeur d'un entier [n] déjà construit, que l'on notera [S n].
   C'est exactement ce que l'on obtient avec le type inductif suivant.
*)

Inductive nat : Set :=
| O : nat
| S : nat -> nat
.

Check (S (S O)). (** représente l'entier noté usuellement 2 *)

(** En comparant les définitions de [nat] et de [listc], on voit
   que les entiers naturels sont analogues à des listes décolorées.
   Scoop : la récurrence structurelle sur nat correspond exactement à
   la récurrence usuelle sur les entiers !
   L'opération qui correspond à [app], mais sur [nat], est tout
   simplement l'addition.
   Les exercices suivants peuvent être résolus en procédant de manière
   analogue à ce qui a été fait sur les listes.
*)

Fixpoint plus (n m : nat) : nat := 
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
(** remplacer ". Admitted" par " := bonne_définition ." *)

Theorem plus_0_l : forall n, plus O n = n.
Proof.
  intro n. cbn [plus]. reflexivity.
Qed.

Theorem plus_0_r : forall n, plus n O = n.
Proof.
  intro n.
  induction n as [ (* O *) | (* S *) n' Hrecn'].
  - cbn [plus]. reflexivity.
  - cbn [plus]. rewrite Hrecn'. reflexivity.
Qed.


(** Pour les exercices suivants une récurrence structurelle simple suffit,
   il faut bien choisir la variable qur laquelle elle porte *)

Theorem plus_assoc : forall n m p, plus n (plus m p) = plus (plus n m) p.
Proof.
  intros n m p.
  induction n as [ (* O *) | (* S *) n' Hrecn'].
  - cbn [plus]. reflexivity.
  - cbn [plus] . rewrite Hrecn' . reflexivity.
Qed.


(* ----------------------------------------------------------------------- *)
(** DEBUT QUESTIONS FACULTATIVES (2) *)

Theorem plus_Sm_r : forall n m, plus n (S m) = S (plus n m).
Proof.
  intros n m.
  induction n as [ (* O *) | (* S *) n' Hrecn'].
    - cbn [plus]. reflexivity.
    - cbn [plus]. rewrite Hrecn'. reflexivity.
Qed.    


(* Penser à utliser les théorèmes précédents *)
Theorem plus_com : forall n m, plus n m = plus m n.
Proof.
  intros n m.
  induction n as [ (* O *) | (* S *) n' Hrecn'].
    - cbn [plus]. rewrite plus_0_r. reflexivity.
    - cbn [plus]. rewrite plus_Sm_r. rewrite Hrecn'. reflexivity. 
Qed.

(** Longueur d'une liste :
   il est plus simple de la définir avec [S] plutôt qu'avec [plus]
*)
Fixpoint long (l : listc) : nat := 
  match l with 
    | Nilc => O
    | Consc c l' => S (long l')
  end.

Theorem long_app : forall u v, long (app u v) = plus (long u) (long v).
Proof.
  intros u v.
  induction u as [(*Nilc*) | (*Consc*) c l Hrecl'].
    - cbn [app plus long]. reflexivity.
    - cbn [app plus long]. rewrite Hrecl'. reflexivity.
Qed.

(** FIN QUESTIONS FACULTATIVES (2) *)
(* ----------------------------------------------------------------------- *)

(** Les entiers naturels de Coq sont définis exactement comme ci-dessus *)

(** On annule ce qui a été fait depuis notre définition de nat,
   pou retrouver la situation fournie par Coq. *)
Reset nat.
Print nat.

(** Mais on a dispose alors facilités de notation, par exemple,
   [S (S O)] s'écrit [2] *)

Fact deux : 2 = S (S O).
Proof. (** regarder le but écrit par Coq *) reflexivity. Qed.

(** * Quelques commandes de recherche d'information *)

(** Quelle est la fonction qui est derrière le symbole "+" ? *) (* sum *)
Locate "+".
(**  Print est connu *)
Print Nat.add.
(** Intégration de l'espace de nommage Nat *)
Import Nat.
Locate "+".
(* Quelles fonctions de type [nat -> nat -> nat] sot disponibles ? *) (* Bcp *)
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
 (1 + x2) * 3 et  (x1 * 2) + x3
*)

Definition a1 : aexp := Amu (Apl (Aco 1) (Ava 2)) (Aco 3).
Definition a2 : aexp := Apl (Amu (Ava 1) (Aco 2)) (Ava 3).



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

(* ----------------------------------------------------------------------- *)
(** DEBUT QUESTIONS FACULTATIVES (3) *)

(** Définir une fonction [get] qui rend la valeur associée à xi dans l'état s *)

Fixpoint get (i: nat) (s: state) : nat :=
   match S, i with
      | Nil, _ => 0
      | Cons n s', O => n
      | Cons n s', S i' => get i' s'
   end.

(** Définir une fonction [set] qui associe la valeur n à xi dans l'état s *)

(** FIN QUESTIONS FACULTATIVES (3) *)
(* ----------------------------------------------------------------------- *)

(** Définir une fonction [eval] qui rend la valeur d'une aexp dans l'état s *)

(** Même si la fonction get ci-dessus a été laissée 'Admitted', elle est 
   utilisable dans les questions suivantes.  *)

Fixpoint eval (a: aexp) (s: state) : nat := 
  match a with
  | Aco n => n
  | Ava i => get i s
  | Apl a1 a2 => plus (eval a1 s) (eval a2 s)
  | Amu a1 a2 => mult (eval a1 s) (eval a2 s)
  | Amo a1 a2 => minus (eval a1 s) (eval a2 s)
  end.



(* ----------------------------------------------------------------------- *)
(** DEBUT QUESTIONS FACULTATIVES (4) *)

(** Définir une fonction [renomme] qui prend une aexp [a] et rend [a] où
   les variables correspondant à x0, x1, x2... ont été respectivement
   renommées en x1, x2, x3...  *)

Fixpoint renomme (a: aexp) : aexp. Admitted.

(** Définir une fonction [decale] qui prend un état [s] et rend
   l'état dans lequel la valeur de x0 est 0, 
   la valeur de x1 est la valeur de x0 dans [s],
   la valeur de x2 est la valeur de x1 dans [s], 
   la valeur de x3 est la valeur de x2 dans [s], etc. 
   Indication : ce n'est PAS un Fixpoint *)

Definition decale (s : state) : state := Cons 0 s.

(** Démontrer qu'évaluer une expression renommée dans un environnement
   décalé rend la même chose qu'avant *)

(** FIN QUESTIONS FACULTATIVES (4) *)
(* ----------------------------------------------------------------------- *)


(* ----------------------------------------------------------------------- *)
(** DEBUT QUESTIONS FACULTATIVES (5) *)

(** ** Expressions booléennes *)

(** Définir un type d'AST nommé bexp pour des expressions booléennes
   comprenant :
   - les constantes booléennes Btrue et Bfalse
   - un opérateur booléen unaire Bnot
   - des opérateurs booléens binaires Band et Bor
   - un opérateur de comparaison représentant le test d'égalité
     entre deux expressions arithmétiques
*)

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

(** FIN QUESTIONS FACULTATIVES (5) *)
(* ----------------------------------------------------------------------- *)