(** * INITIATION A COQ *)

(**
Le début de ce fichier a été présenté en cours.
Il est demandé de le réviser à la maison et de le terminer
en préparation du TD suivant.
- Lire attentivement les commentaires explicatifs
- sous emacs/Proof-general,
  - pour avancer d'une étape, faire C-c C-n
  - pour reculer, C-c C-p
  - pour aller d'un coup à la position du curseur, C-c RET.
  D'autres raccourcis sont disponibles, regarder les menus Proof-General et Coq.
*)


(** ** Généralités *)

(** Coq est primitivement un langage de programmation particulier.
    Comme OCaml, c'est un langage fonctionnel typé.
    Son système de types est beaucoup plus riche que celui de OCaml,
    ce qui permet en particulier d'énoncer des formules logiques,
    et éventuellement de les démontrer.

    Dans un premier temps, on se focalise sur l'aspect programmation,
    et les formules logiques considérées sont de simples égalités.
 *)

(** Un script Coq est une suite de déclarations de types, de valeurs,
    (très souvent : des fonctions), d'énoncés de théorèmes suivis
    de leur preuve.

    On a également des requêtes pour obtenir des informations,
    calculer des expressions.
*)


(** À RETENIR : EN COQ, TOUT FINIT PAR UN POINT '.' *)

(** ** Types énumérés *)

(** Le type qui s'écrirait en OCaml
type coulfeu =
  | Vert
  | Orange
  | Rouge

se définit en Coq presque de la même façon.
*)

Inductive coulfeu : Set :=
  | Vert : coulfeu
  | Orange : coulfeu
  | Rouge : coulfeu
.

(** Comme en OCaml, [blabla : machin] se lit "[blabla] a pour type [machin]".
    Ainsi la déclaration précédente indique que [Vert], [Orange] et [Rouge]
    sont de type coulfeu.
    Par ailleurs, en Coq tout a un type ; la déclaration ci-dessus indique que
    le type de [coulfeu] est [Set], cf. notes de cours.
*)

(** ** Définition d'une valeur fonctionnelle *)

Definition coul_suiv : coulfeu -> coulfeu :=
  fun c =>
    match c with
    | Vert => Orange
    | Orange => Rouge
    | Rouge => Vert
    end.

(** La commande Check permet d'obtenir le type d'une expression.
    Elle vérifie que l'expression est bien typée. *)

Check coul_suiv.
Check (coul_suiv Vert).

(** La commande Eval permet de calculer une expression. *)

Eval compute in (coul_suiv Vert).

(** Raccourci *)
Compute (coul_suiv Vert).

(** ** Premier théorème, tactiques cbn et reflexivity *)

Theorem ex1_coul_suiv : coul_suiv (coul_suiv Vert) = Rouge.
Proof. cbn [coul_suiv]. reflexivity. Qed. (** cbn = call by name *)

(** Remarque : on peut énoncer une théorème à prouver au moyen d'autres
mots-clé, notamment Lemma (pour un résultat auxiliaire) ou Example
(pour un théorème très simple servant à tester le résultat d'une fonction
sur une entrée particulière.
Ces mots-clé sont équivalents, le choix de l'un ou l'autre est affaire de
convention ou d'usage.
Ici on aurait donc plutôt utilisé  Example.
Example ex1_coul_suiv : coul_suiv (coul_suiv Vert) = Rouge.
*)


(** Une *tactique* est une commande permettant de faire progresser une preuve *)

(** On a utilisé ci-dessus les tactiques suivantes :
    - cbn [nom_de_fonction] : évaluation (partielle) de [nom_de_fonction]
    - reflexivity : reconnaissance que les deux membres de l'égalité
                    à prouver sont identiques (preuve de x = x).
 *)

(** ATTENTION À BIEN TERMINER PAR "Qed." *)

(** ** Variables *)

(** Les preuves par réflexivité fonctionnent non seulement
    entre des expressions constantes identiques, mais aussi
    entre des expressions comportant des variables. *)

(** On a la possibilité en Coq (mais pas en OCaml) de déclarer
    des variables :
    ce sont des noms dont on connaît simplement le type.
    Il faut que ces noms soient déclarés dans une portée
    (domaine de visibilité) définie par une section.
*)

(** Ouverture d'une section dans laquelle on va faire quelques
    preuves par réflexivité. *)

Section sec_refl.
  Variable c : coulfeu.
  (** Signification intuitive : "soit [c] une [coulfeu] inconnue". *)

  Theorem th1_refl_simple : c = c.
  (** Remarquer que le but contient un environnement comportant
      l'hypothèse [c : coulfeu]. *)
  Proof. reflexivity. Qed.

  Check c.

(** Fermeture de la section,
    ce qui clôt la portée des variables, ici [c : coulfeu]. *)
End sec_refl.

Fail Check c.
Fail Definition x := Vert + 2.

(* -------------------------------------------------------------------  *)
(** Vu jusqu'ici dans ls CM1 2020, en fait juste avant le End sec_refl. *)
(* -------------------------------------------------------------------  *)

(** ** Principe de Leibniz : tactique rewrite *)

Section sec_reec.
  Variable c : coulfeu.
  Hypothesis crou : c = Rouge.
  (** Signification intuitive, par analogie avec la ligne d'avant :
      "soit [crou] une preuve inconnue de [c = Rouge]". *)

  Theorem coul_suiv_Rouge : coul_suiv c = Vert.
  Proof.
    rewrite crou.
    cbn [coul_suiv].
    reflexivity.
  Qed.

End sec_reec.

(** ** Raisonnement par cas : tactique destruct *)

Section sec_cas.
  Variable c : coulfeu.

  Theorem th3_coul_suiv : coul_suiv (coul_suiv (coul_suiv c)) = c.
  Proof.
    (** reflexivity ne fonctionne pas. *)
    Fail reflexivity.
    (** Il faut raisonner par cas sur les trois valeurs de [c] possibles *)
    (** Cela va donner lieu à trois sous-buts, un pour chaque cas. *)
    destruct c as [ (*Vert*) | (*Orange*) | (*Rouge*) ].
    - cbn [coul_suiv]. reflexivity.
    - cbn. reflexivity.
    - reflexivity.
  Qed.

  Print Vert.
  Print th3_coul_suiv.

End sec_cas.

(** ** Raisonnement universel : tactique intro *)

(** Il est possible d'énoncer des formules quantifiées universellement.
    Par exemple : [forall c : coulfeu, c = c].
 *)

Theorem th_refl_gen : forall c : coulfeu, c = c.
Proof.
  (** Pour la démontrer, la première étape consiste à dire
      "soit [c0] une couleur arbitraire, démontrons [c0 = c0]." *)
  intro c0.
  (** Remarquer que intro a introduit l'hypothèse [c0 : coulfeu]. *)
  (** On a déjà vu que reflexivity fonctionne dans cette situation. *)
  reflexivity.
Qed.

(** La tactique intro sert également à démontrer une implication. *)
Theorem th_crou_gen : forall c : coulfeu, c = Rouge -> coul_suiv c = Vert.
Proof.
  intro c0.
  (** Pour démontrer [c0 = Rouge -> coul_suiv c0 = Vert],
      on suppose [c0 = Rouge]
      et on doit alors prouver [coul_suiv c0 = Vert]
      sous cette hypothèse supplémentaire ;
      lorsque l'on introduit une hypothèse, on lui donne un nom. *)
  intro c0rou.
  (** Le raisonnement sous-jacent est :
      soit c0rou une preuve arbitraire (inconnue) de [c0 = Rouge],
      on peut s'en servir pour démontrer coul_suiv [c0 = Vert]. *)
  rewrite c0rou. cbn [coul_suiv]. reflexivity.
Qed.

(** Remarque : on est souvent amené à effectuer plusieurs introductions
    successives. On emploie alors le raccourci intros (au pluriel).
    Sur l'exemple précédent cela donne ceci : *)
Theorem th_crou_gen_bis : forall c : coulfeu, c = Rouge -> coul_suiv c = Vert.
Proof.
  intros c0 c0rou.
  rewrite c0rou. cbn [coul_suiv]. reflexivity.
Qed.

(** * Début du travail à faire à la maison *)

(** *** Exercice: Variante du précédent avec section *)

Section sec_variante_th_crou_gen.
  Variable c : coulfeu.
  Hypothesis crou : c = Rouge.
  Theorem th_crou_demi_gen : c = Rouge -> coul_suiv c = Vert.
  Proof.
    rewrite crou.
    cbn [coul_suiv].
    reflexivity.
  Qed.
    (** à compléter *)


  (* Quand une démonstration est incomplète, on peut passer à la suite
   * à l'aide de Admitted  au lieu de Qed.
   * Ne pas oublier de remplacer Admitted par Qed quand on a réussi ! *)

End sec_variante_th_crou_gen.

(** *** Exercice: Preuve par cas d'un théorème avec forall *)

Lemma suivsuivsuiv_id : forall c:coulfeu, coul_suiv (coul_suiv (coul_suiv c))=c.
Proof.
  intros c.
  destruct c as [ (*Vert*) | (*Orange*) | (*Rouge*) ].
  - cbn [coul_suiv]. reflexivity.
  - cbn [coul_suiv]. reflexivity.
  - cbn [coul_suiv]. reflexivity.
Qed.
(** à compléter ici *)

(** ** Type inductif et récurrence structurelle : arbres binaires tricolores *)

Inductive arbin : Set :=
  | F : coulfeu -> arbin
  | N : arbin -> arbin -> arbin.

(**
Pour définir une fonction récursive (l'équivalent de let rec
en OCaml) on utilise le mot clé [Fixpoint].
 *)

Fixpoint renva a : arbin :=
  match a with
  | F c => F c
  | N g d => N (renva d) (renva g)
  end.

(** *** Exercice: prouver que renverser deux fois un arbre rend le même arbre *)
Theorem renva_renva : forall a, renva (renva a) = a.
Proof.
  intro a.
  (** Tentative de raisonnement par cas sur a *)
  (** Les noms mis dans chaque cas (c pour le premier, a2 a2 pour le second)
      désignent les composantes des constructeurs respectivement F puis N *)
  destruct a as [ (* F *) c
                | (* N *) a1 a2 ].
  - cbn [renva]. reflexivity.
  - cbn [renva].
    (** Il apparaît qu'un simple raisonnement par cas est insuffisant, *)
    (** donc on arrete tout... *)
 Abort.

(** ... et on recommence en raisonnant par récurrence structurelle *)
Theorem renva_renva : forall a, renva (renva a) = a.
Proof.
  intro a.
  (** récurrence structurelle sur le type inductif arbin *)
  (** Remarquer l'analogie avec l'utilisation de la tactique destruct :
      les noms mis dans chaque cas (c pour le premier, a2 a2 pour le second)
      désignent les composantes des constructeurs respectivement F puis N
      mais en complément, on ajoute deux noms pour les hypothèses de récurrence,
       Hrec_a1 pour celle sur a1 et Hrec_a2 pour celle sur a2 *)
  induction a as [ (* F *) c
                 | (* N *) a1 Hrec_a1 a2 Hrec_a2 ].
  - cbn [renva]. reflexivity.
  - cbn [renva]. rewrite Hrec_a2. rewrite Hrec_a1. reflexivity.
    (* à compléter *)
Qed.

(** Fin du travail à faire à la maison. *)
