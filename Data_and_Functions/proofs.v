(* Example of proof by simplification *)
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

(* 
In Coq, we use tactics to manipulate the goal and context, where Coq 
will keep track of the goal and context for us 

Tactics (used in the previous proof) :
  "intros" - introduces things into our context
             whatever been quantified
  "simpl" - simplifies our goal running a few steps of computation
  "reflexivity" - named after the property of equality (all things are equal to themselves
  "Qed" - quod erat demonstrandum, latin for 'that which was to be proved'

*)

(* Example of proof by rewriting *)
Theorem plus_id_example : forall (n m: nat), 
  n = m -> n + n = m + m.

(* The way a proof with implies ('->') works is: you have to prove what's to the right of 
the arrow... but you may assume what's to the left. *)

Proof. 
  (* move both quantifiers int othe context *)
  intros n m .
  (* move the hypothesis into the context *)
  intros H.
  (* rewrite the goal usign the hypothesis *)
  rewrite -> H.
  reflexivity. Qed.

(* (The arrow symbol in the rewrite has nothing to do with implication:
 it tells Coq to apply the rewrite from left to right. To rewrite from 
right to left, you can use rewrite <-.  *)

(* Example of proof by case analysis *)
Theorem plus_1_neq_firsttry : forall n : nat, beq_nat (n + 1) 0