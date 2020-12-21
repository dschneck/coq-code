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

(* Exercise *)
Theorem plus_id_exercise : forall n m o : nat, 
  n = m -> m = o -> n + m = m + o.

Proof. intros n m o. intros H. rewrite <- H.
intros G. rewrite -> G. reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat, 
  m = S n-> 
  m * (1 + n) = m * m.

Proof. intros n m. intros H. rewrite -> H.
simpl. reflexivity. Qed.


(* Example of proof by case analysis *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem plus_1_neq_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.

Proof. intros n. simpl. Abort.

(* More tactics
  "Abort" - ends the proof but doesn't prove it
  "destruct" - tells Coq to consider seperate cases on a
                a variable in the context

*)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
 
Proof. 
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity. Qed.

(* The annotation "as [| n']" is called an intro pattern. 
It tells Coq what variable names to introduce in each subgoal

The - signs on the second and third lines are called bullets, 
and they mark the parts of the proof that correspond to each generated subgoal.

The destruct tactic can be used with any inductively defined datatype.
 *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.

Proof. intros b. destruct b.
  - reflexivity.
  - reflexivity. Qed.

(* Note that the destruct here has no as clause because none of the subcases 
of the destruct need to bind any variables, so there is no need to specify
any names. (We could also have written as [|], or as [].)
*)

Theorem andb_commutative : forall b c, andb b c = andb c b.

Proof. intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
 Qed.

Theorem and3b_commutative : forall b c d, andb (andb b c) d = andb (andb b d ) c.

Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.

(* You can perform the destructing in the same
 command as the intros. *)

Theorem plus_1_neg_0' : forall n : nat, 
  beq_nat (n + 1) 0 = false.
 
Proof.
  intros [|n].
      - reflexivity.
      - reflexivity. 
Qed.

(* Exercise 1 *)

Lemma minus_n_O : forall n : nat, n = n - 0.

Proof. intros n. destruct n as [a|b].
  - reflexivity.
  - reflexivity.
 Qed.

Theorem andb_commutative'' :
  forall b c : bool, andb b c = andb c b.

(* If there are no arguments to name, we can just write [] *)
Proof. intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise 2 need to come back and finish this one*)

Theorem andb_true_elim2 : forall b c : bool, 
  andb b c = true -> c = true.

Proof. intros b c. destruct c as [c'|c']. Abort.

(* Exercise 3 *)
Theorem zero_nbeq_plus_1 : forall n : nat, 
  beq_nat 0 (n + 1) = false.
 
Proof. intros []. 
  - reflexivity.
  - reflexivity.
Qed.

(* I should come back to this section to understand 
 how i can translate coq proofs into paper proofs *)
 












