Require Import String.

Definition prenom : string := "Eve".
Definition nom : string := "Poitevin".

(* *)

Inductive arbint : Set :=
  | F : arbint
  | N : arbint -> nat -> arbint  -> arbint
.

Fixpoint taille (a : arbint) : nat :=
  match a with
  | F => 0
  | N g n d => taille g + S (taille d)
  end.

Fixpoint arb_S (a : arbint) : arbint :=
  match a with
  | F => F
  | N g n d => N (arb_S g) (S n) (arb_S d)
  end.

(* ComplÃ©ter la preuve. *)
Lemma meme_taille_arb_S : forall a, taille (arb_S a) = taille a.
Proof.
  intro a.
  induction a as [ | ].
  - cbn [arb_S]. reflexivity.
  - cbn [arb_S]. cbn [taille]. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

(* QCM (Ã  questions binaires) *)
(* Dans ce qui suit remplacer ". Admitted." par ":= votre reponse."
   si vous connaissez la bonne rÃ©ponse, ou laisser ". Admitted." sinon.*)

(* Question 1 :
  la preuve prÃ©cÃ©dente est par rÃ©currence sur a *)
Definition reponse_1 : bool:= true.

(* Question 2 :
   la preuve prÃ©cÃ©dente est par rÃ©currence sur la taille de a *)
Definition reponse_2 : bool:= false.

(* Question 3 :
   dans la preuve prÃ©cÃ©dente, combien y a-t-il d'hypothÃ¨ses de rÃ©currence ? *)
Definition reponse_3 : nat:= 2.
