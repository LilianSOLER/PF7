Inductive listN : Set :=
 | Nil : listN
 | Cons : nat -> listN -> listN.

Fixpoint app (u1 : listN) (u2 : listN) : listN :=
  match u1 with
   | Nil => u2
   | Cons x r1 => Cons x (app r1 u2)
  end.

Infix "::" := Cons (at level 60, right associativity).
Notation "[ ]" := Nil (format "[ ]").
Infix "@" := app (right associativity, at level 60).

(* Révisions (utile pour la suite) *)
Theorem app_neutre_droite : forall u, u @ [] = u.
Proof.
Admitted.

Theorem app_assoc : forall u1 u2 u3, (u1 @ u2) @ u3 = u1 @ (u2 @ u3).
Proof.
Admitted.

Fixpoint rv (u : listN) : listN :=
  match u with
   | [] => []
   | x :: u' => (rv u') @ (x :: [])
  end.

Fixpoint rv_acc (u : listN) (a : listN) : listN :=
  match u with
   | [] => a
   | x :: u' =>  rv_acc u' (x :: a)
  end.

Theorem rv_acc_rv_bis : forall u a, rv_acc u a = rv u @ a.
Proof.
  intro u.
  induction u as [ | 

(* Trouver le lemme auxiliaire utile ! *)
Theorem rv_acc_rv : forall u, rv_acc u [] = rv u.
Proof.
Admitted.

(* Si temps disponible *)

Lemma rv_app : forall u v, rv (u @ v) = rv v @ rv u.
Proof.
Admitted.

Theorem rv_rv : forall u, rv (rv u) = u.
Proof.
Admitted.
