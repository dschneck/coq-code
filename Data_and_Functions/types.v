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

(* The Notation command defines a new symbolic notation for an existing definition *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => negb b2
    | false => true
  end.

(* Every expression in Coq has a type, describing what sort of thing it computes. 
The Check command asks Coq to print the type of an expression. *)

Check true.

Check negb true.

(* Functions like negb itself are also data values, just like true and false.
 Their types are called function types, and they are written with arrows. *)

Check negb.

(*  The response to the top can be read as: "Given an input of type bool, this function produces
 an output of type bool." *)

Check andb.

(* The types we have defined so far are examples of "enumerated types": their definitions explicitly
 enumerate a finite set of elements, each of which is just a bare constructor.*)





(* Compound types *)
Inductive rgb : Type :=
  | red : rgb (* Constructor expression *)
  | green : rgb (* Constructor expression *)
  | blue : rgb. (* Constructor expression *)

Inductive color : Type :=
  | black : color
  | white : color
  | primary : rgb -> color.

Definition monochrome (c:color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

(* TIP: Coq matches patterns in order from top to bottom *)

Definition isred (c:color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false (* "_" is the wildcard pattern *)
  end.

Example test_isred : (isred (primary red)) = true.
Proof. simpl. reflexivity. Qed.

































