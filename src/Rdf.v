From Coq Require Import Lists.ListSet.
From Coq Require Import Init.Nat.
From Coq Require Import Strings.String.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Inductive node : Type :=
  | Null
  | Const (c : nat)
  | Var (s : string).

Definition is_const (n : node) : bool :=
  (match n with
   | Const _ => true
   | otherwise => false
   end).

Definition is_var (n : node) : bool :=
  (match n with
   | Var _ => true
   | otherwise => false
   end).

Check (Const 5) : node.
Check (Var "x") : node.
Check (Null) : node.

(*
An idea to define triples
Inductive trpl : Type :=
  | triple (s p o : node).
 *)

Definition eqb_node (n1 n2 : node) : bool :=
  (match n1, n2 with
   | (Null), (Null) => true
   | (Const c1), (Const c2) => c1 =? c2
   | (Var s1),(Var s2) => eqb s1 s2
   | e1,e2 => false
   end).

Example eqb_null_node :  eqb_node (Null) (Null) = true.
Proof. reflexivity. Qed.
Example eqb_const_eq_node:  eqb_node (Const 5) (Const 5) = true.
Proof. reflexivity. Qed.
Example eqb_const_neq_node:  eqb_node (Const 5) (Const 0) = false.
Proof. reflexivity. Qed.
Example eqb_var_eq_node :  eqb_node (Var "x") (Var "x") = true.
Proof. reflexivity. Qed.
Example eqb_var_neq_node :  eqb_node (Var "x") (Var "y") = false.
Proof. reflexivity. Qed.

(*
TODO
eqb_node_refl
eqb_node_true
eqb_node_false
*)
Theorem eq_nat_eq_const : forall (n1 n2:nat) , (n1 = n2) <-> (Const n1) = (Const n2).
(* TODO *)
Admitted.

Theorem eq_string_eq_const : forall (s1 s2:string) , (s1 = s2) <-> (Var s1) = (Var s2).
(* TODO *)
Admitted.
(* alias for triple of nodes type *)
Definition triple := (node * node * node)%type. 

Check ((Null), (Const 1), (Var "foo")): triple.


(*
   Inductive rdf : Type :=
  | graph (triples : list triple).
 *)

(* Not sure if its a good idea to have a set, 
 may be we want some order on the triples *)
Definition graph := set triple.

(* Check [((Const 5),(Const 5), (Const 5))].
   Check (set_add ((Const 5),(Const 5), (Const 5)) empty_set). *)
(* Check (set ((Const 5),(Const 5), (Const 5)),  ((Var "x"),(Const 1),(Const 2))  ) : graph.
 *)
