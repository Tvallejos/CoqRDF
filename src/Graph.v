From Coq Require Import Lists.ListSet.
From RDF Require Import Triples.
From RDF Require Import Node.
Definition graph := set trpl.

Check (set_add eq_dec_triple (triple (Const 1) (Const 1) (Const 1)) (empty_set trpl)): graph.

Definition eqb_graph (g g': graph) : bool :=
  (match (set_diff eq_dec_triple g g') with
   | nil => true
   | otherwirse => false
   end).

Example eqb_graph_test : 
  eqb_graph (empty_set trpl) (empty_set trpl) = true.
Proof. reflexivity. Qed.
Example eqb_graph_test2 : 
  eqb_graph (set_add eq_dec_triple (triple (Const 5) (Const 4) (Const 3)) (empty_set trpl)) (empty_set trpl) = false.
Proof. reflexivity. Qed.
