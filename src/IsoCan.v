From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From RDF Require Import Rdf Triple Term.
(* From Coq Require Import List. *)




Section IsoCan.
  (* Axiom todo : forall A,A. *)
  Variable I B L: eqType.
  Let rdf_graph:= (rdf_graph I B L).
  Let triple:= (triple I B L).
  Let term:= (term I B L).
  Let relabeling:= (Rdf.relabeling).

  Definition isocanonical_function (M : B -> B) (g : rdf_graph) :=
    iso g (Rdf.relabeling M g) /\
      forall (h : rdf_graph), iso g h <-> (relabeling M g) = (relabeling M h).

  Section IsoCanAlgorithm.
    Variable hash : eqType.
    Variable hashTerm : term -> hash.
    Hypothesis perfectHashingSchemeTerm : injective hashTerm.
    Variable hashBag : (seq hash -> hash).
    Hypothesis hashBag_assoc : forall (l l1 l2 l3: seq hash) (perm : l = l1 ++ l2 ++ l3),
        hashBag ([:: hashBag (l1 ++ l2)] ++ l3) = hashBag (l1 ++ [:: hashBag (l2 ++ l3)]).
    Hypothesis hashBag_comm : forall (l l1 l2: seq hash) (perm : l = l1 ++ l2),
        hashBag l = hashBag (l2 ++ l1).
  End IsoCanAlgorithm.
  (* Hypothesis rdf_total_order   *)







End IsoCan.
