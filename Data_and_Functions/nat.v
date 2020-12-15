(* The next couple of commands are from bool.v but their
needed to make sense of the first part of this file *)

Inductive bool : Type :=
	| true : bool
	| false: bool.

Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => b2
    | false => false
   end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.


Module NatPlayground.

Inductive nat : Type :=
  | O : nat (* O is a natural number (note that this is the letter "O," not the numeral "0")*)
  | S : nat -> nat. (* S can be put in front of a natural number to yield another one \u2014 if n is a natural number, then S n is too *)

(* The following is the predecessor function, returns the nat before the nat given *)
Definition pred (n:nat) : nat :=
  match n with
  | O => O
  | S n' => n' (* "if n has the form S n' for some n', then return n'." *)
  end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n:nat) : nat :=
  match n with 
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).

Check S.

Check pred.

Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).
Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n:nat) (m:nat) : nat :=
  match n with 
  | O => m
  | S n'=> S (plus n' m)
  end.

Compute (plus 3 2).






















