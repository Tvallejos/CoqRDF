From Coq Require Import Lists.ListSet.
From Coq Require Import Init.Nat.
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From RDF Require Import Node.
From RDF Require Import Triples.
From RDF Require Import Maps.
From RDF Require Import Graph.



Definition image (g : graph) (μ : node -> node) : graph :=
  set_map eq_dec_triple (fun t => app_μ_to_triple μ t) g.

(* image of mapping Const 2 of 1,1,1 => 2,1,2*)
Compute (image (set_add eq_dec_triple (triple (Const 1) (Const 1) (Const 1)) (empty_set trpl)) 
  (fun _ => Const 2)): graph.

Inductive world : Type :=
  | res (I L B : set node).

Definition proj_I (w : world) : set node :=
  match w with
  | res i _ _ => i
  end.
Definition proj_L (w : world) : set node :=
  match w with
  | res _ l _ => l
  end.

Definition proj_B (w : world) : set node :=
  match w with
  | res _ _ b => b
  end.
Definition proj_IL (w : world) : set node:=
  set_union eq_dec_node (proj_I w) (proj_L w).

Definition isomorphism (w : world) (g g': graph) :=
  exists μ : node -> node,
  relabelling (proj_IL w) (proj_B w) μ -> (image g μ) = g'.

