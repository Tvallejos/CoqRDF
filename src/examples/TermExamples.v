From RDF Require Import Term.
From Coq Require Import Strings.String.

Check (Lit 5) : term.
Check (Bnode "b") : term.
Check (Iri "A") : term.

Example eqb_bnode_ex :  eqb_node (Bnode "b") (Bnode "b") = true.
Proof. reflexivity. Qed.
Example eqb_lit_eq_node_ex:  eqb_node (Lit 5) (Lit 5) = true.
Proof. reflexivity. Qed.
Example eqb_lit_neq_node:  eqb_node (Lit 5) (Lit 0) = false.
Proof. reflexivity. Qed.
Example eqb_iri_eq_node :  eqb_node (Iri "x") (Iri "x") = true.
Proof. reflexivity. Qed.
Example eqb_iri_neq_node :  eqb_node (Iri "x") (Iri "y") = false.
Proof. reflexivity. Qed.
