From Coq Require Export Strings.String.
From Coq Require Import Arith.Arith.
From RDF Require Import Rdf.

Definition total_map (A : Type) := node -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (n : node) (v : A) :=
  fun n' => eqb_node n n' then v else m n'.
