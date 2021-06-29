From Coq Require Import Strings.String.

Inductive node : Type :=
  | Const (c : nat)
  | Var (s : string).

Check (Const 5) : node.
Check (Var "x") : node.

Inductive trpl : Type :=
  | triple (s p o : node).

(* Notation triple := (node * node * node). *)
(* Definition triple := (node * node * node). *)

Check (triple (Const 5) (Const 1) (Const 8)): trpl. (* TODO why fails *)
Check (triple (Var "x") (Const 1) (Var "foo")): trpl.

(* Check ((Const 5),(Const 2),(Const 1)). *)

Inductive rdf : Type :=
  | graph (triples : list trpl).

