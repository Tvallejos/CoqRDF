From Coq Require Export Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.ListSet.
From RDF Require Import Term.


Definition total_map (A : Type) := term -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (t : term) (v : A) :=
  fun t' => if eqb_term t t' then v else m t'.

Definition maps_to_lit (t : term) (μ : term -> term) : bool :=
  (is_lit (μ t)).

Definition maps_to_iri (t : term) (μ : term -> term) : bool :=
  (is_iri (μ t)).

Definition maps_to_bnode (t : term) (μ : term -> term) : bool :=
  (is_bnode (μ t)).

Definition maps_to_lit_or_bnode (t : term) (μ : term -> term) : bool :=
  maps_to_lit t μ || maps_to_bnode t μ.

(* want to define this as property of μ given IL B*)
Definition mapping (IL B : set term) (μ : term -> term) :=
  forall t : term,
  (set_In t IL -> maps_to_lit t μ = true) /\ (set_In t B -> maps_to_lit_or_bnode t μ = true).

(* want to define this as property of μ given IL B*)
Definition relabelling (IL B : set term) (μ : term -> term) :=
  forall t : term,
  (set_In t IL -> maps_to_lit t μ = true) /\ (set_In t B -> maps_to_bnode t μ = true).

(*
Definition mapping (nod : term) (IL B : set term) (μ : term -> node) : bool :=
  (match nod with
   | Const _ => if set_In_dec nod IL then map_const nod μ else true
   | Var _ => if set_In nod B then map_var_or_const nod μ else true
   | otherwise => true
   end).
 *)

       (* (is_const n /\ set_In n IL -> map_const) \/ () *)
(* 
   Definition mapping2 (IL : set term) (μ : term -> term) : bool :=
  set_map IL μ.
 *)
(* 
   Definition blank_node_mapping (IL B: set term) (μ : term -> term) :=
 *)
  
