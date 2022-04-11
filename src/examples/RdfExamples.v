From RDF Require Import Term.
From RDF Require Import Rdf. 
From Coq Require Import Strings.String.
From Coq Require Import Lists.ListSet.

Check (triple (Bnode "a") (Lit 1) (Iri "foo")): trpl.

Check (set_add eq_dec_node (Iri "x") (set_add eq_dec_node (Lit 5) (empty_set term))).

Example example_in_graph : set_In (Lit 12) (set_add eq_dec_node (Lit 12) (set_add eq_dec_node (Lit 5) (empty_set term))).
Proof. simpl. destruct (eq_dec_node (Lit 12) (Lit 5)) eqn:E.
  - simpl. left. symmetry. apply e.
  - simpl. right. left. reflexivity.
Qed.

Check (set_add eq_dec_triple (triple (Lit 1) (Lit 1) (Lit 1)) (empty_set trpl)): graph.

(* image of mapping Const 2 of 1,1,1 => 2,1,2*)
Compute (image (set_add eq_dec_triple (triple (Lit 1) (Lit 1) (Lit 1)) (empty_set trpl)) 
  (fun _ => Lit 2)): graph.

Example eqb_graph_test : 
  eqb_graph (empty_set trpl) (empty_set trpl) = true.
Proof. reflexivity. Qed.
Example eqb_graph_test2 : 
  eqb_graph (set_add eq_dec_triple (triple (Lit 5) (Lit 4) (Lit 3)) (empty_set trpl)) (empty_set trpl) = false.
Proof. reflexivity. Qed.

