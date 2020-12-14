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

Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition addb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => b2
    | false => false
   end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.


(* Unit tests for the logical operators *)
Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(* The Notation command defines a new symbolic notation for an existing definition *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.










