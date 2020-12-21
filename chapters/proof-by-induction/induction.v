Theorem plus_n_O_firsttry : forall n : nat, 
  n = n + 0.
Proof. intros n. simpl. (* Does nothing! *) Abort.

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof. intros n. destruct n as [| n'].
  (* n = 0 *)

