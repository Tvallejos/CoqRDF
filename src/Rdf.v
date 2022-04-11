From Coq Require Import Lists.ListSet.
From Coq Require Import Init.Nat.
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From RDF Require Import Term.
From RDF Require Import Maps.
From RDF Require Import Triple.


(* Not sure if its a good idea to have a set, 
 may be we want some order on the triples *)
Definition graph := set trpl.

Definition image (g : graph) (μ : term -> term) : graph :=
  set_map eq_dec_triple (fun t => app_μ_to_triple μ t) g.

Definition eqb_graph (g g': graph) : bool :=
  (match (set_diff eq_dec_triple g g') with
   | nil => true
   | otherwirse => false
   end).

Inductive world : Type :=
  | res (I L B : set term) (P : set_inter eq_dec_term I (set_inter eq_dec_term L B) = empty_set term).

Definition proj_I (w : world) : set term :=
  match w with
  | res i _ _ _ => i
  end.
Definition proj_L (w : world) : set term :=
  match w with
  | res _ l _ _ => l
  end.

Definition proj_B (w : world) : set term :=
  match w with
  | res _ _ b _ => b
  end.
Definition proj_IL (w : world) : set term:=
  set_union eq_dec_term (proj_I w) (proj_L w).

Definition isomorphism (w : world) (g g': graph) :=
  exists μ : term -> term,
  relabelling (proj_IL w) (proj_B w) μ -> (image g μ) = g'.

