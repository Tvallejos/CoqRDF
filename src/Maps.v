From Coq Require Export Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.ListSet.
From RDF Require Import Node.


Definition total_map (A : Type) := node -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (n : node) (v : A) :=
  fun n' => if eqb_node n n' then v else m n'.

Definition map_lit (nod : node) (μ : node -> node) : bool :=
  (is_lit (μ nod)).

Definition map_bnode (nod : node) (μ : node -> node) : bool :=
  (is_bnode (μ nod)).

Definition map_lit_or_bnode (nod : node) (μ : node -> node) : bool :=
  map_lit nod μ || map_bnode nod μ.

(* want to define this as property of μ given IL B*)
Definition mapping (IL B : set node) (μ : node -> node) :=
  forall nod : node,
  (set_In nod IL -> map_lit nod μ = true) /\ (set_In nod B -> map_lit_or_bnode nod μ = true).

(* want to define this as property of μ given IL B*)
Definition relabelling (IL B : set node) (μ : node -> node) :=
  forall nod : node,
  (set_In nod IL -> map_lit nod μ = true) /\ (set_In nod B -> map_bnode nod μ = true).

(*
Definition mapping (nod : node) (IL B : set node) (μ : node -> node) : bool :=
  (match nod with
   | Const _ => if set_In_dec nod IL then map_const nod μ else true
   | Var _ => if set_In nod B then map_var_or_const nod μ else true
   | otherwise => true
   end).
 *)

       (* (is_const n /\ set_In n IL -> map_const) \/ () *)
(* 
   Definition mapping2 (IL : set node) (μ : node -> node) : bool :=
  set_map IL μ.
 *)
(* 
   Definition blank_node_mapping (IL B: set node) (μ : node -> node) :=
 *)
  
