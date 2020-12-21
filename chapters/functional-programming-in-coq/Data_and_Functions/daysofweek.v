(* Definition f (n : nat) : nat := n + 1.
Eval compute  in f 3. *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(* "The assertion we've just made can be proved by observing that 
both sides of the equality evaluate to the same thing, after some simplification."*) 
Proof. simpl. reflexivity. Qed.


Inductive bool : Type :=
  | true: bool
  | false: bool.

Definition is_weekday (d:day) : bool :=
  match d with
    | monday => true
    | tuesday => true
    | wednesday => true
    | thursday => true
    | friday => true
    | saturday => false
    | sunday => false
  end.


Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => negb b2
    | false => true
  end.

Example test_nandb1: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.






