(* Proof by Induction *)

(* The following proof works, but the one after does not *)
Theorem  plus_left_side: forall n : nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_n_O_firsttry : forall n : nat, 
  n = n + 0.
Proof. intros n. simpl. (* Does nothing! *) Abort.

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof. intros n. destruct n as [| n'].
  - (* n = 0 *)
    reflexivity. (* So far so good *)
  - (* n = S n' *)
    simpl. (*... but here we are stuck again *)
  Abort.
 

(* 
Here is the principle of induction over natural numbers: 
If P(n) is some proposition involving a natural number n 
and we want to show that P holds for all numbers n, we can 
reason like this:
  > show that P(O) holds; show that, for any n', if P(n')
  > holds, then so does P(S n'); conclude that P(n) holds
  > for all n.


*)

Theorem plus_N_O : forall n : nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0*) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'.
  reflexivity. Qed.

(* 
The previous Theorem and proof written on paper 

Theorem : For any n,
  n = n + 0

Proof : By induction on n.
  First, suppose n = 0. We must show
    0 = 0 + 0
    
    This follows directly from the definition of +
 
  Next, suppose n = S n', where (as our IH)
    n' = n' + 0
    
    We must show 
      S n' = (S n') + 0
      
      which is immediate from the induction hypothesis. 
  Qed.

*)

Theorem minus_diag : forall n, minus n n = 0.
Proof. intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.
(* 
When applied to a goal that contains quantified variables, 
the induction tactic will automatically move them into the 
context as needed.
*)

(* Exercise 1 *)
Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof. induction n as [|n' IHn'].
  - reflexivity.
  -simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof. intros n m. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof. intros n m. induction n as [|n' IHn'].
  - simpl. induction m as [|m' IHm'].
    + reflexivity.
    + simpl. rewrite <- IHm'. reflexivity.
  - simpl. induction m as [|m' IHm'].
    + rewrite -> IHn'. simpl. reflexivity.
    + simpl. rewrite -> IHn'. rewrite <- IHm'. simpl. rewrite <- IHn'.
    



(* Proofs within proofs *)




















