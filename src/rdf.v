From Coq Require Import Strings.String.
From Coq Require Import Lists.ListSet.

Inductive node : Type :=
  | Const (c : nat)
  | Var (s : string).

Check (Const 5) : node.
Check (Var "x") : node.

(*Inductive trpl : Type :=
  | triple (s p o : node).
 *)

Definition triple := (node * node * node)%type. 

Check ((Const 5), (Const 1),(Const 8)): triple. 
Check ((Var "x"), (Const 1), (Var "foo")): triple.


(*
   Inductive rdf : Type :=
  | graph (triples : list triple).
 *)
Check set.
Definition graph := set triple.
Check graph.

(* Check [((Const 5),(Const 5), (Const 5))].
   Check (set_add ((Const 5),(Const 5), (Const 5)) empty_set). *)
(* Check (set ((Const 5),(Const 5), (Const 5)),  ((Var "x"),(Const 1),(Const 2))  ) : graph.
 *)
