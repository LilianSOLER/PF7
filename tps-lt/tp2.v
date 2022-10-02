(** INITIATION A LΑ RÉCURRENCE EN COQ *)
(* TP 2 - Benjamin Bracquier + Lilian Soler *)

(*
Le TD est destiné à exprimer en Coq la preuve par récurrence
sur les expressions arithmétiques vue au TD1.
*)

(**
Attention : il faut être capable de rédiger sous forme de texte usuel
le raisonnement formalisé en Coq, soit avant, soit a posteriori.
*)

(** * Expressions arithmétiques *)

(** ** Définitions *)

(** On considère une variante simplifiée des expressions arithmétiques vues en cours/TD,
    ne comportant des opérateurs que pour l'addition et la multiplication.
    On utilisera le type nat (entiers naturels de Coq) pour représenter les entiers
    et on nommera les différents constructeurs/opérateurs
    Cst (pour les naturels), Apl et Amu pour l'addition et la multiplication *)

    Inductive aexp : Set := 
    | Cst : nat -> aexp 
    | Apl : aexp -> aexp -> aexp 
    | Asub : aexp -> aexp -> aexp
    | Amu : aexp -> aexp -> aexp.
    (* à compléter *)
    
    (* Définir les expressions aexp correspondant à
      (1 + 2) * 3 et  (1 * 2) + 3
     *)
    
    Definition exp_1 :=  Amu (Apl (Cst 1)  (Cst 2)) (Cst 3).
    Definition exp_2 := Apl (Amu (Cst 1) (Cst 2)) (Cst 3).
    
    (** Définir en Coq la fonction d'évaluation sémantique fonctionnelle Sf de aexp
        en utilisant les operateurs arithmétiques de Coq sur le type nat : + *       *)
    
    Fixpoint eval (a: aexp) : nat :=
      match a with
      | Cst n => n
      | Apl a1 a2 => (eval a1) + (eval a2)
      | Asub a1 a2 => (eval a1) - (eval a2)
      | Amu a1 a2 => (eval a1) * (eval a2)
      end.
      (* à compléter *)
    
    (** Evaluer avec Eval ou Compute la sémantique de exp_1 et exp_2 *)
    
    Check (eval exp_1).
    Check (eval exp_2).

    Compute (eval exp_1).
    Compute (eval exp_2).
    
    (** Nombre de feuilles *)
    
    (** Définir en Coq la fonction de calcul du nombre de feuilles dans un
        arbre d'expression (c'est-à-dire le nombre de constantes de
        l'expression) *)
    
    Fixpoint nbf (a:aexp) :=
      match a with
        | Cst n => 1
        | Apl a1 a2 => (nbf a1) + (nbf a2)
        | Asub a1 a2 => (nbf a1) + (nbf a2)
        | Amu a1 a2 => (nbf a1) + (nbf a2)
      end.
    
    (** ** Raisonnement par cas sur un AST *)
    
    (** Écrire une fonction qui transforme une expression
       (ou plus exactement un AST d'expression) de la façon suivante :
       - si l'expression représente une constante, rendre la constante 1
       - si l'expression représente une somme, rendre la constante 2
       - si l'expression représente un produit, rendre la constante 3
     *)
    
    Definition categorise (a:aexp) :=
      match a with
        | Cst n => Cst 1
        | Apl a1 a2 => Cst 2
        | Asub a1 a2 => Cst 2
        | Amu a1 a2 => Cst 3
      end.
    
    (** Démontrer que le résultat de la fonction précédente
        rend un AST de taille 1 au sens de nbf.
        Raisonner par cas en utilisant la tactique destruct.
     *)
    
    Lemma nbf_cat : forall a, nbf (categorise a) = 1.
    Proof.
      destruct a as [ (*Cst*) | (*Apl*) | (*Asub*) | (*Amu*)].
    - cbn [categorise]. cbn[nbf] . reflexivity.
    - cbn [categorise]. cbn[nbf] . reflexivity.
    - cbn [categorise]. cbn[nbf] . reflexivity.
    - cbn [categorise]. cbn[nbf] . reflexivity.
    Qed.
    
    (** Nombre d'opérateurs *)
    
    (** Définir en Coq la fonction de calcul du nombre de noeuds dans un
        arbre d'expression (c'est-à-dire le nombre d'opérateurs binaires de
        l'expression) *)
    
    Fixpoint nbo (a:aexp) :=
      match a with
        | Cst n => 0
        | Apl a1 a2 | Asub a1 a2 | Amu a1 a2 => nbo a1 + nbo a2 + 1
      end.
    
    (** Démontrer la relation entre nbf et nbo par récurrence structurelle *)
    
    (** On utilisera dans la suite quelques lemmes simples d'arithmétique *)
    
    Require Import Arith. Import Nat.
    Check add_assoc.
    
    Lemma nbf_nbo_plus_1: forall a:aexp, nbf a = nbo a + 1.
    Proof.
      intro a.
      induction a as [ (*Cst*) n
                     | (*Apl*) e1 Hrec_e1 e2 Hrec_e2
                     | (*Amu*) e1 Hrec_e1 e2 Hrec_e2
                     | (*Asub*) e1 Hrec_e1 e2 Hrec_e2 ].
        - reflexivity.
        - cbn [nbo nbf]. rewrite Hrec_e1. rewrite Hrec_e2. rewrite add_assoc. 
    
      (* à compléter *)
    Admitted.
    
    (** Transformation d'expressions *)
    
    
    (* Écrire une fonction qui transforme une expression
     * en remplaçant toutes les constantes par 1
     * et tous les opérateurs binaires par +
     *)
    
    Fixpoint transform (a:aexp) :=
      match a with
        | Cst n => Cst 1
        | Apl a1 a2 | Asub a1 a2 | Amu a1 a2 => Apl (transform a1) (transform a2)
      end.
    
    (** Évaluer la fonction transform sur les expressions exp_1 et exp_2 *)
    
    Compute (transform exp_1).
    Compute (transform exp_2).
  
    (** Montrer maintenant que l'évaluation de transform e donne le nombre
     * de feuilles de e (nbf e). *)
    
    Lemma eval_transform_nbf : forall a, eval (transform a) = nbf a.
    
    Proof.
      intro a.
      induction a as [ (*Cst*) n
                     | (*Apl*) e1 Hrec_e1 e2 Hrec_e2
                     | (*Amu*) e1 Hrec_e1 e2 Hrec_e2
                     | (*Asub*) e1 Hrec_e1 e2 Hrec_e2 ].
        - reflexivity.
        - cbn [transform eval nbf]. rewrite Hrec_e1. rewrite Hrec_e2. reflexivity.
        - cbn [transform eval nbf]. rewrite Hrec_e1. rewrite Hrec_e2. reflexivity.
        - cbn [transform eval nbf]. rewrite Hrec_e1. rewrite Hrec_e2. reflexivity.
    Qed.
    
    (** Simplification d'expressions *)
    
    (* Définir ici la fonction simpl0 du TD1 *)
    
    Definition simpl0 (a:aexp) :=
      match a with
      | Cst n => Cst n
      | Apl (Cst 0) e => e
      | Apl e (Cst 0) => e
      | Amu (Cst 1) e => e
      | Amu e (Cst 1) => e
      | Amu (Cst 0) e => Cst 0
      | Amu e (Cst 0) => Cst 0
      | Asub e (Cst 0) => e
      | _ => a
      end.
    
    (* ------------------------------------------------------------------------------- *)
    (*                     LΑ SUITE EST FACULTATIVE POUR LE DM.                        *)
    (*                                                                                 *)
    (* Vous êtes bien sûr encouragés à la faire si vous êtes à l'aise avec ce qui a    *)
    (* été vu jusqu'ici.                                                               *)
    (* ------------------------------------------------------------------------------- *)
    
    (* Prouver que simpl0 préserve le résultat de l'évaluation *)
    
    (* On introduit une tactique utilisateur signifiant :
       prouver les cas "0 + e2" et "0 * e2", 
       considérant à l'avance que tous les autres cas se prouvent par simplification et 
       réflexivité.
       A ce stade on va simplement utiliser cette tactique, son fonctionnement
       sera expliqué plus tard.
    *)
    Ltac cas_simpl0 e :=
      refine ( match e with
               | Apl (Cst 0) e2 => _
               | Amu (Cst 0) e2 => _
               | _ => eq_refl _
               end).
    
    (** Deux lemmes utiles *)
    Check add_0_l.
    Check mul_0_l.
    
    Lemma eval_simpl0: forall a, eval (simpl0 a) = eval a.
    Proof.
      intro a. cas_simpl0 a.
      - cbn [simpl0]. cbn [eval]. rewrite add_0_l. reflexivity.
      (* à compléter *)
    Admitted.
    
    (* écrire la fonction simpl_rec qui applique récursivement simpl0 à toutes les sous-expressions. *)
    
    Fixpoint simpl_rec (a:aexp) :=
      (* à compléter *)
    
    (* Prouver que simpl_rec préserve l'évaluation des expressions *)
    
    Lemma eval_simpl_rec: forall a, eval(simpl_rec a) = eval a.
    Proof.
      (* à compléter *)
    Admitted.
    