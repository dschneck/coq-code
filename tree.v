Inductive tree : Set :=
  | empty : tree
  | node : tree -> tree -> tree. (* Constructor that takes to subtrees and returns a tree *)

Print tree_ind.

Fixpoint size t := (* Returns the size of a tree *)
  match t with
    | empty => 0
    | node t1 t2 => S (plus(size t1)(size t2))
  end.

Fixpoint swap t := (* Swaps nodes in a tree with their subtrees ?*)
  match t with
    | empty => empty
    | node t1 t2 => node (swap t1) (swap t2)
  end.

Theorem swap_size: forall t, size t = size (swap t).

Proof. intros t. induction t.
  - auto. (* Tactic that will prove base cases IDK why *)
  - simpl. f_equal. (* got rid of the successors *) rewrite <- IHt1. rewrite <- IHt2. reflexivity.
Qed.