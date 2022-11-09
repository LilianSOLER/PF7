(* Consigne générale : remplacer les
              Admitted.
   par votre preuve ou votre définition et mettre Qed.
   Ne changer pas le nom des fonctions ou théorèmes demandés.

  Pré et post-condition : ce fichier compile sans erreur

   Il y a 3 types de questions :
   - des questions [**] que vous devriez être capable de réussir si vous avez fait
     et compris le projet
   - des questions [***] plus difficiles et apportant plus de points
   - des questions [*] que vous n'avez pas besoin de traiter si vous avec réussi
     des questions mieux étoilées

   Une question peut rapporter des points si la solution proposée débute
   correctement.

   Il n'est pas nécessaire de traiter toutes les questions pour obtenir la note maximale.
   *)

Require Import String.

Definition prenom : string := "Eve".
Definition nom : string := "Poitevin".

(* ------------------------------------------------------------ *)
Require Import List.
Require Import Arith.
Import List.ListNotations.

(* ================================================================================= *)
(* Questions inspirées du projet

   On considère le langage LOOP, pour lequel on peut
   - manipuler 1 ou 2 variables (désignées ici par les numéros 0 et 1)
   - exécuter des instructions en séquence (";")
   - incrémenter une des variables
   - remettre la valeur d'une variable à 0
   - boucler un nombre de fois désigné par une constante entière

   *)

Definition var := nat.

Inductive linstr:=
| Skip : linstr
| Incr : var -> linstr
| Reset : var -> linstr
| Seq : linstr -> linstr -> linstr
| Loop : nat -> linstr -> linstr.

Definition state := list nat.

Definition init : state := [0; 0].

Definition incr_var (v:var) (s:state) : state :=
  match v, s with
  | 0, v0 :: l => S v0 :: l
  | 1, v0 :: v1 :: l => v0 :: S v1 :: l
  | _, _ => init
  end.

Definition reset_var (v:var) (s:state) : state :=
  match v, s with
  | 0, v0 :: l => 0 :: l
  | 1, v0 :: v1 :: l => v0 :: 0 :: l
  | _, _ => init
  end.

(* Sémantique naturelle (à grands pas) *)
Inductive SNL: linstr -> state -> state -> Prop :=
| SN_Skip : forall s,
    SNL Skip s s
| SN_Incr : forall s v,
    SNL (Incr v) s (incr_var v s)
| SN_Reset : forall s v,
    SNL (Reset v) s (reset_var v s)
| SN_Seq: forall s0 s1 s2 i1 i2,
    SNL i1 s0 s1 -> SNL i2 s1 s2 -> SNL (Seq i1 i2) s0 s2
| SN_Loop_0 : forall s i,
    SNL (Loop 0 i) s s
| SN_Loop_S : forall nn s0 s1 s2 i,
    SNL i s0 s1 -> SNL (Loop nn i) s1 s2 ->
    SNL (Loop (S nn) i) s0 s2.

(* Sémantique Opérationnelle Structurelle (à petits pas) *)
Inductive config :=
| Inter : linstr -> state -> config
| Final : state -> config.

Inductive SOS_1: linstr -> state -> config -> Prop :=
| SOS_Skip : forall s,
    SOS_1 Skip s (Final s)
| SOS_Incr : forall v s,
    SOS_1 (Incr v) s (Final (incr_var v s))
| SOS_Reset : forall v s,
    SOS_1 (Reset v) s (Final (reset_var v s))
| SOS_Seqf     : forall i1 i2 s s1,
    SOS_1 i1 s (Final s1) ->
    SOS_1 (Seq i1 i2) s (Inter i2 s1)
| SOS_Seqi     : forall i1 i1' i2 s s1,
    SOS_1 i1 s (Inter i1' s1) ->
    SOS_1 (Seq i1 i2) s (Inter (Seq i1' i2) s1)
| SOS_Loop_0 : forall i s,
    SOS_1 (Loop 0 i) s (Final s)
| SOS_Loop_S : forall nn i s,
    SOS_1 (Loop (S nn) i) s (Inter (Seq i (Loop nn i)) s).

Inductive SOS : config -> config -> Prop :=
| SOS_stop  : forall c, SOS c c
| SOS_again : forall i1 s1 c2 c3,
              SOS_1 i1 s1 c2 -> SOS c2 c3 ->
              SOS (Inter i1 s1) c3.

(* Version fonctionnelle de SOS_1 *)
(* [**] Question 1 *)
Fixpoint SOS_f (i:linstr) (s:state) : config :=
  match i with
  | Skip => Final s
  | Incr v => Final (incr_var v s)
  | Reset v => Final (reset_var v s)
  | Seq i1 i2 => match SOS_f i1 s with
                 | Final s1 => Inter i2 s1
                 | Inter i1' s1 => Inter (Seq i1' i2) s1
                 end
  | Loop 0 i => Final s
  | Loop (S nn) i => Inter (Seq i (Loop nn i)) s
  end.


(* Exemples *)

Definition A:var := 0.

Definition A2_2 :=  Loop 2 (Loop 2 (Incr A)).

(* [**] Question 2.1 *)
Lemma SN_A2_2 : SNL (A2_2) [0] [4].
Proof.
  cbv [A2_2].
  eapply SN_Loop_S.
  eapply SN_Loop_S.
  apply SN_Incr.
  cbn.
  eapply SN_Loop_S.
  apply SN_Incr.
  cbn.
  eapply SN_Loop_0.
  eapply SN_Loop_S.
  eapply SN_Loop_S.
  apply SN_Incr.
  cbn.
  eapply SN_Loop_S.
  apply SN_Incr.
  cbn.
  eapply SN_Loop_0.
  apply SN_Loop_0.
Qed.
  
(* [**] Question 2.2 *)
Lemma SOS_A2_2 : SOS (Inter A2_2 [0]) (Inter (Loop 1 (Loop 2 (Incr A))) [2]).
Proof.
  eapply SOS_again.
  cbv[A2_2].
  eapply SOS_Loop_S.
  eapply SOS_again.
  eapply SOS_Seqi. eapply SOS_Loop_S.
  eapply SOS_again.
  eapply SOS_Seqi. eapply SOS_Seqf. eapply SOS_Incr.
  eapply SOS_again.
  eapply SOS_Seqi. eapply SOS_Loop_S.
  eapply SOS_again.
  eapply SOS_Seqi. eapply SOS_Seqf. eapply SOS_Incr.
  eapply SOS_again.
  eapply SOS_Seqf. eapply SOS_Loop_0.
  cbv.
  eapply SOS_stop.
Qed.

(* Trois questions de rattrapage 
   si vous n'arrivez pas à faire des questions [**] ou [***] *)

Definition A1 := Seq (Incr A) (Seq (Reset A) (Incr A)).

(* [*] Question 3.1 *)
Lemma SN_A1 : SNL (A1) [0] [1].
Proof.
Admitted.

(* [*] Question 3.2 *)
Lemma SOS_A1 : SOS (Inter A1 [0]) (Final [1]).
Proof.
Admitted.

(* [*] Question 3.3 *)
Lemma loop_0 : forall x prog,
    SOS (Inter (Loop 0 prog) [x])
        (Final [x]).
Proof.
Admitted.

(* Lemme que l'on pourra utiliser sans démonstration ;
   vous pouvez aussi le démontrer *)
(* [***] Question 4 *)
Theorem SOS_trans : forall c1 c2 c3, SOS c1 c2 -> SOS c2 c3 -> SOS c1 c3.
Proof.
intros c1 c2 c3.
  intros c12 c23.
  induction c12 as [ | ].
  - apply c23.
  - eapply SOS_again.
    + apply H.
    + apply IHc12.
      apply c23.
Qed.

(* Lemme à utiliser SANS DÉMONSTRATION *)
Fixpoint SOS_seq i1 i2 s1 s2 (so : SOS (Inter i1 s1) (Final s2)) :
  SOS (Inter (Seq i1 i2) s1) (Inter i2 s2).
Admitted.

(* Suite de lemmes aboutissant au théorème MUL *)
(* Des lemmes arithmétiques utiles sont suggérés au besoin *)
(* [***] Question 5.1 *)
Check Nat.add_succ_r.
Lemma PLUS : forall p x,
    SOS (Inter (Loop p (Incr A)) [x]) (Final [p+x]).
Proof.
Admitted.

(* [**] Question 5.2 *)
Check Nat.add_comm.
Corollary PLUS_seq : forall p x prog,
    SOS (Inter (Seq (Loop p (Incr A)) prog) [x])
        (Inter                        prog  [x + p]).
Proof.
Admitted.

(* [**] Question 5.3 *)
Lemma MUL_S : forall n p x,
    SOS (Inter (Loop (S n) (Loop p (Incr A))) [x])
        (Inter (Loop n     (Loop p (Incr A))) [x + p]).
Proof.
Admitted.

(* [***] Question 5.4 *)
Check Nat.add_0_r.
Check Nat.add_assoc.
Lemma MUL_S_iter : forall n p x,
    SOS (Inter (Loop n (Loop p (Incr A))) [x])
        (Inter (Loop 0 (Loop p (Incr A))) [x + n * p]).
Proof.
Admitted.

(* [*] Question 5.5 *)
Lemma MUL_np : forall n p,
    SOS (Inter (Loop n (Loop p (Incr A))) [0])
        (Inter (Loop 0 (Loop p (Incr A))) [n * p]).
Proof.
Admitted.

(* [**] Question 5.6 *)
Theorem MUL : forall n p, SOS (Inter (Loop n (Loop p (Incr A))) [0]) (Final [n*p]).
Proof.
Admitted.


(* ================================================================================ *)

(* On essaie de donner une sémantique fonctionnelle au langage LOOP *)
(* La tentative suivante échoue *)
Fail Fixpoint evalL (i : linstr) (s : state) {struct i} : state :=
  match i with
  | Skip => s
  | Incr v => incr_var v s
  | Reset v => reset_var v s
  | Seq i1 i2 => evalL i2 (evalL i1 s)
  | Loop 0 i => s
  | Loop (S n) i => evalL (Loop n i) (evalL i s)
  end.

(* Voici une définition en deux temps qui est acceptée *)
Fixpoint iter_fun (n:nat) (f: state -> state) (s:state) : state :=
  match n with
  | 0 => s
  | S nn => f (iter_fun nn f s)
  end.

Fixpoint evalL (i : linstr) (s : state) {struct i} : state :=
  match i with
  | Skip => s
  | Incr v => incr_var v s
  | Reset v => reset_var v s
  | Seq i1 i2 => evalL i2 (evalL i1 s)
  | Loop n i => iter_fun n (evalL i) s
  end.

(* [***] Question 6 *)
(* Expliquer en remplissant ce commentaire

À REMPLIR

- La première tentative échoue parce que...

- La seconde définition est acceptée parce que...

 *)

(* ================================================================================ *)
(* Questions de rattrapage (à ne faire que si vous n'arrivez pas à
   faire au moins 2 des questions précédentes) *)

(* [*] Question 7 *)

Lemma loop_skip_nil : forall n, evalL (Loop n Skip) [] = [].
Proof.
Admitted.

(* [*]  Question 8 *)
(* Écrivez des versions de incr et reset qui fonctionnent avec un
   nombre quelconque de variables *)

Fixpoint reset_var_qq (v:var) (s:state) : state.
Admitted.



Fixpoint incr_var_qq (v:var) (s:state) : state.
Admitted.
