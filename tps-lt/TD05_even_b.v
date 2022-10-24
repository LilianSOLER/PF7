(*travail fait par benjamin bracquier et lilian soler*)
(**
Objectif de ce suppport de TD :
initiation aux relations ou prédicats définis inductivement,
pour préparer la définition des sémantiques relationnelles.
*)

(* Les exercices sont faciles, progressifs, et sont prévus
   pour une durée d'environ 1/2h).
*)

(* ------------------------------------------------------------ *)
(** * Relations ou prédicats définis inductivement *)

(** ** Prédicats à 1 argument sur un type énuméré  *)

(** Commençons par un prédicat très simple qui indique comment
    sélectionner quelques valeurs dans un type énuméré. *)


Inductive coul : Set :=
| violet : coul
| indigo : coul
| bleu : coul
| vert : coul
| jaune : coul
| orange : coul
| rouge : coul
.

(** Rappel : on ne peut PAS définir un autre type qui partage des
    constructeurs avec un type déjà défini. *)
Fail Inductive coulfeu : Set :=
| vert : coulfeu
| orange : coulfeu
| rouge : coulfeu
.

Definition ATTENTION_QUESTION_EN_COMMENTAIRE_1 : bool.
(**
Pourquoi interdire à un constructeur d'être dans des types inductifs différents ?
 *)
(* car il pourrait avoir des confusions
 *)
Admitted .

(** Mais on peut définir un prédicat sur coul qui est démontrable
    pour vert orange et rouge (et seulement pour ces derniers). *)

Inductive estCoulfeu : coul -> Prop :=
| Fver : estCoulfeu vert
| Fora : estCoulfeu orange
| Frou : estCoulfeu rouge
.

(** Par exemple on peut démontrer que vert satisfait ce prédicat. *)
Example exemple_feu_vert : estCoulfeu vert.
Proof.
  apply Fver.
Qed.

(** Certains feux de circulation ne présentent que les deux couleurs
    vert et rouge. *)

Inductive feu2couls : coul -> Prop :=
| F2ver : feu2couls vert
| F2rou : feu2couls rouge
.

(** On veut démontrer que le second prédicat implique le premier. *)

Lemma feu2couls_estCoulfeu : forall c, feu2couls c -> estCoulfeu c.
Proof.
  intro c.
  (** On essaie d'abord un raisonnement par cas sur [c].*)
  destruct c.
  (** Beaucoup de cas inutiles (et qui requièrent une technique spéciale).
      Donc on essaye une meilleure stratégie. *)
  Undo 1.
  (** Introduction de l'hypothèse sur [c]. *)
  intro f2c.
  (** Il suffit de raisonner par cas sur les deux façons
      dont [f2c] peut être construite *)
  refine (match f2c with F2ver => _ | F2rou => _ end).
  clear.
  (** Même chose en utilisant la tactique destruct sur l'HYPOTHÈSE [f2c] *)
  Undo 2.
  destruct f2c as [ (*F2ver*) | (*F2rou*) ].
  - apply Fver.
  - refine Frou.
Qed.

(** Exercice *)

(** Sur le modèle du prédicat estCoulfeu, définir un autre prédicat nommé boivr,
    qui sélectionne les couleurs bleu, orange, indigo, vert et rouge. *)

(* Inductive boivr à compléter *)

Inductive boivr : coul -> Prop :=
|bbleu: boivr bleu
|borange: boivr orange
|bindigo: boivr indigo
|bvert: boivr vert
|brouge: boivr rouge
.

(** Démontrer ensuite : *)

Lemma estCoulfeu_boivr : forall c, estCoulfeu c -> boivr c.
Proof.
  (** compléter *)
intro c .
intro ecf .
destruct ecf as [(*bvert*)|(*borange*) |(*brouge*) ] .
-apply bvert .
-apply borange .
-apply brouge .
Qed .

(** ** Relations à 2 arguments sur un type énuméré *)

(** Les relations inductives permettent de représenter des fonction partielles
    i.e., qui ne sont pas définies partout. Voici un exemple où coulsuiv
    est définie pour vert, orange et rouge, mais pas pour les autres couleurs
    prévues dans coul. *)

Inductive coulsuiv : coul -> coul -> Prop :=
| CSv : coulsuiv vert orange
| CSo : coulsuiv orange rouge
| CSr : coulsuiv rouge vert
.

(** Exercice (même technique qu'auparavant) *)

Lemma coulsuiv_estCoulfeu : forall c1 c2, coulsuiv c1 c2 -> estCoulfeu c1.
Proof.
  (** compléter *)
intros c1 c2 .
intro cs .
destruct cs as [(*Fver*) |(*Fora*) |(*Frou*) ] .
-apply Fver .
-apply Fora .
-apply Frou .
Qed .

(** ** Prédicat even sur nat *)

(** De même que les types inductifs de données peuvent être récursifs,
    par exemple nat ou aexp, les prédicats inductifs peuvent être
    récursifs. C'est le cas de even, présenté au CM4. *)

Inductive even : nat -> Prop :=
| E0 : even 0
| E2 : forall n, even n -> even (S (S n))
.

(** Exercice : démontrer que 6 est pair. *)

Example ev10 : even 10.
Proof.
  refine (E2 8 _).
  apply (E2 6).
  apply E2.
  apply E2 .
  apply E2 .  
  apply E0 .
  Qed .
Print ev10.

Definition ATTENTION_QUESTION_EN_COMMENTAIRE_2 : bool.
(** Exercice :
    - quel est le type et la signification de E2 4 ?
    - quel est le type et la signification de E2 5 ?
*)
(* E2 4 est even et correspond à E2 4(E2 2(E2 0 E0 ))
   E2 5 est even mais n'arrivera jamais à la fin
 *)
Admitted.


(** Entiers atteignables en ajoutant des 2 ou des 7 en partant de 0. *)
Inductive p2p7 : nat -> Prop :=
| PP0 : p2p7 0
| PP2 : forall n, p2p7 n -> p2p7 (2 + n)
| PP7 : forall n, p2p7 n -> p2p7 (7 + n)
.

(** Exercice : démontrer de 3 façons que 11 est atteignable par p2p7. *)
Example p2p7_11_methode1 : p2p7 11.
Proof.
  refine (PP7 4 _) .
  apply PP2 .
  apply PP2 .
  apply PP0 .
  Qed .
Example p2p7_11_methode2 : p2p7 11.
Proof.
  refine (PP2 9 _).
  apply PP2 .
  apply PP7 .
  apply PP0 .
  Qed .


  
Example p2p7_11_methode23 : p2p7 11.
Proof.
  refine (PP2 9 _) .
  apply PP7.
  apply PP2 .
  apply PP0 .
Qed .

Print p2p7_11_methode2.

(** Démontrer que tout entier pair satisfait p2p7. *)

Theorem even_p2p7 : forall n, even n -> p2p7 n.
Proof.
  intros n en.
  (** Comme il y a une infinité d'entiers pairs, une preuve par cas
      ne suffit pas. On procède par récurrence structurelle sur les
      façons de démontrer [even n], autrement les formes possibles
      d'arbres de preuve pour [en].
      On a deux cas, celui où [en] est [E0], et celui où [en]
      est de la forme [E2 n' en'], avec [en' : even n'] ;
      dans ce dernier cas, on a droit à une hypothèse de récurrence
      sur en', assurant que [n'] satisfait p2p7.
  *)
  induction en as [ (*E0*) | (*E2*) n' evn' Hrec_evn'].
  - apply PP0.
  - (** Facultatif : mise sous une forme clairement adaptée à p2p7 *)
    change (p2p7 (2 + n')).
    (** Utilisation du constructeur approprié de p2p7 *)
    apply PP2.
    (** Utilisation de l'hypothèse de récurrence *)
    apply Hrec_evn'.
Qed.

(** Il est instructif de démontrer le même théorème par une
    fonction récursive. *)

Fixpoint fct_even_p2p7 n (en : even n) : p2p7 n :=
  match en with
  | E0 => PP0
  | E2 n' evn' => PP2 n' (fct_even_p2p7 n' evn')
  end.

(** On peut transformer un arbre de preuve de [even 4]
    en un arbre de preuve de [p2p7 4] *)
Compute fct_even_p2p7 4 (E2 2 (E2 0 E0)).

(** La somme de deux entiers pairs est paire *)
Lemma even_plus : forall n m, even n -> even m -> even (n + m).
Proof.
  intros n m evn evm.
  induction evn as [(*E0*) |(*E2*) n' evn' Hrec_evn'] .
  -apply evm .
  -change (even (S (S (n' + m)))).
  apply E2 .
  apply Hrec_evn' .
Qed .

   


(** Exercice facultatif :
    en donner une preuve sous forme de fonction. *)

Fixpoint fct_even_plus n m (evn : even n) (evm : even m) : even (n + m).
  (** A compléter *)
Admitted.

(* Les multiples de 4 sont pairs *)
Inductive mul4 : nat -> Prop :=
| M4_0 : mul4 0
| M4_4 : forall n, mul4 n -> mul4 (S (S (S (S n))))
.

Lemma mul4_even : forall n, mul4 n -> even n.
Proof.
  intros n m4n.
  (** Terminer par récurrence structurelle sur [m4n] *)
Admitted.
