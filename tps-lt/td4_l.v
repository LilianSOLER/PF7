(**
Trois objectifs dans ce TD :
- Raisonner avec apply ... pour utiliser
  hypothèses implicatives et/ou quantifiées universellement)
- Utiliser des hypothèses de récurrence implicatives et/ou
   quantifiées universellement
- Utiliser une hypothèse indiquant une égalité entre deux 
  constructeurs différents, ce qui est "manifestement impossible"
*)

(* ---------------------------------------------------------------------- *)
(** * Partie 1 : raisonnement, tactiques refine et apply *)

(** ** Rappels sur les tactiques *)
(**

- intro x
  a le même effet que
  refine (fun x => _)

- apply f
  a le même effet que
  refine f, ou
  refine (f _), ou
  refine (f _ _), etc.
  suivant le type de [f].

  Exemple

  f : T1 -> T2
  ============
  T2

  On peut ici utiliser refine (f _), il restera à trouver
  quelque chose de type T1.

  - destruct E as [ (* Cons1 *) x | (* Cons2 *) | (* Cons3 *) y z]
    a le même effet que
    refine (match E with
             | Cons1 x => _
             | Cons2 => _
             | Cons3 y z => _
             end).

    où E a un type inductif de constructeurs Cons1 Cons2 et Cons3
    ayant respectivement 1, 0 et 2 arguments.
 *)

(** ** Rappels sur les structures en arbre *)
(**
    1) on a vu des structures de données destinées à la
    programmation (listes, etc.), et des structures de données
    destinées au raisonnement, appelées arbres de preuve,
    qui se manipulent de la même manière.

    2) On a vu également que les types de structures de données pour
    la programmation ont eux même un type, l'univers Set.
 *)

(** ** L'univers Prop *)
(**
    Les arbres de preuve sont dans un univers parallèle à Set,
    appelé Prop.

    Remarque : en particulier, les égalités sont dans Prop.
*)

(*

Corerction get td3

Fixpoint get (i:int) (s:state) :nat := 
  match s with
  | nil => 0
  | cons (j,v) s' => match i with
                     | 0 => v
                     | S i' => get i' s'
                     end
  end.

  or 

  match S, i with
  | nil, _ => 0
  | cons (j,v) s', 0 => v
  | cons (j,v) s', S i' => get i' s'
  end.

  get 0 Nil = 0
  get 0 x::q = x
  get (S i) Nil = 0
  get (S i) x::q = get i q
*)
Check (2 = 2).

Section sec_ABC.
  (** Considérons des propositions arbitraires A B C... *)
  Variable A B C : Prop.
  (** ... et des prédicats arbitraires P Q R sur nat *)
  Variable P Q R : nat -> Prop.

 (** Preuve à faire uniquement avec refine/intro/apply *)
 (** Faire également Show Proof après les invications de
     tactiques pour voir la preuve en train de se former. *)
  Lemma impl_trans:
    (A -> B) -> (B -> C) -> (A -> C).
  Proof.
    intros H1 H2 H3.
    apply H2.
    apply H1.
    apply H3.
  Qed.

  (** Preuve à faire uniquement avec intro/apply *)
  Lemma combi_S:   (A -> B -> C) -> (A -> B) -> A -> C.
  Proof.
    (* À compléter *)
  intros H1 H2 H3.
  apply H1.
  apply H3.
  apply H2.
  apply H3.
  Qed.

  (* Preuve à faire uniquement avec intro/apply *)
  Lemma forall_impl_trans:
    (forall n:nat, P n -> Q n) ->
    (forall n:nat, Q n -> R n) ->
    (forall n:nat, P n -> R n).
  Proof.
    intros H1 H2 n H3.
    apply H2.
    apply H1.
    apply H3.
  Qed.
End sec_ABC.


(* -------------------------------------------------------------------------- *)
(** * Partie 2 : équivalence entre égalité des entiers et eqnatb rendant true *)

(** eqnatb renvoie true ssi ses arguments représentent le même entier naturel *)

Fixpoint eqnatb n1 n2 :=
   match n1,n2 with
  | O,O => true
  | S n1', S n2' => eqnatb n1' n2'
  | _,_ => false
  end.

(** ** 2.1 Le sens le plus facile (récurrence simple) *)

Lemma eqnatb_eq_1 : forall n, eqnatb n n = true.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - cbn[eqnatb]. apply IHn'.
Qed.


Lemma eqnatb_eq : forall n1 n2, n1 = n2 -> eqnatb n1 n2 = true.
Proof.
  intros n1 n2 H.
  induction H.
  - rewrite eqnatb_eq_1. reflexivity.
Qed.

  

(* Facultatif : preuve directe sans utiliser eqnatb_eq_1 *)
Lemma eqnatb_eq_direct : forall n1 n2, n1 = n2 -> eqnatb n1 n2 = true.
Proof.
  (* À compléter: utiliser clear avant induction. *)
  (* La tactique clear [hy] retire l'hypothèse [hy] du but. *)
  intros n1 n2 H.
  rewrite H.
  clear H.
  induction n2 as [|n2' IHn2'].
  - reflexivity.
  - cbn[eqnatb]. apply IHn2'.
Qed.

(** ** 2.2 Le sens le plus difficile (récurrence quantifiée + preuve par cas) *)

(*** 2.2.1 Lemme préparatoire *)

(** Nouvelle tactique :
la tactique [change _expr_] permet de remplacer la conclusion
par une autre propriété convertible c'est-à-dire equivalente par calcul.

exemple:

===========
2 + 1 = 6
-> change (3 = 3 * 2)

Cela permet de "décalculer" un résultat de fonction.
 *)

Lemma absurd: 5 = 4 -> 15 = 12.
Proof.
  intros e.
  (** faire apparaitre 5 et 4 dans un même contexte
      en utilisant la tactique [change] *)
  (* À compléter *)
  (* change (... 5 ... = ... 4 ...). *)

  (* discriminate e.*)

  change(3 * 5 = 3 * 4).
  rewrite e.
  reflexivity.
Qed.
(* facultatif *)
Lemma true_false_eg : true = false -> forall n1 n2 : nat, n1 = n2.
Proof.
  intro etf. intros n1 n2.
  (** Definir une fonction f tq [f true = n1] et [f false = n2]   *)
  (* À compléter *)
  (* pose (f (b:bool) := ... *)
  pose(f (b:bool) := if b then n1 else n2).
  change(f true = f false).
  rewrite etf.
  reflexivity.

    (*discriminate.*)
Qed.

(*** 2.2.2 Réciproque de 2.1 *)
(** Dans l'exercice ci-dessous, il faut bien identifier la propriété de n1
    sur laquelle porte la récurrence *)
Lemma eq_eqnatb : forall n1 n2, eqnatb n1 n2 = true -> n1 = n2.
Proof.
  intros n1 n2 H.
  cbn[eqnatb] in H.
  induction n1 as [|n1' IHn1'], n2 as [|n2' IHn2'].
  - reflexivity.
  - discriminate.
  - discriminate.
  -  
Admitted.



(** ** 2.3 Équivalence, tactique split *)

(** On peut utiliser split pour prouver une équivalence
    par décomposition en deux implications *)

Print iff.

Lemma eq_iff_eqnatb : forall n1 n2, eqnatb n1 n2 = true <-> n1 = n2.
Proof.
  split.
  - intro H.
    induction n1, n2.
    + reflexivity.
    + discriminate.
    + discriminate.
    + 

Admitted.
