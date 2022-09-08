
From mathcomp Require Import all_ssreflect fingraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term IsoCan.

Definition code_nat (n : nat) := GenTree.Leaf n.

Definition decode_nat (x : GenTree.tree nat) : option nat :=
  match x with
  | GenTree.Leaf n => Some n
  | _ => None
  end.

Lemma cancel_code_decode : pcancel code_nat decode_nat. by case. Qed.
Definition nat_canCountMixin := PcanCountMixin cancel_code_decode.
Canonical nat_countType :=
  Eval hnf in CountType nat nat_canCountMixin.

Section test.
  (* Variable (b1 b2 : B) (pred : I). *)
  (* Definition t1 := @Bnode I B L b1. *)
  (* Definition t2 := @Bnode I B L b1. *)
  (* Definition p := @Iri I B L pred. *)
  (* Definition trpl1 : triple I B L. *)
  (* Proof. refine (mkTriple t1 _ _). *)
  (*        - exact (@b_in_ib I B L b2). *)
  (*        - exact (@i_in_i I B L pred). *)
  (* Qed. *)

  (* Definition trpl2 : triple I B L. *)
  (* Proof. refine (mkTriple t2 _ _). *)
  (*        - exact (@b_in_ib I B L b1). *)
  (*        - exact (@i_in_i I B L pred). *)
  (* Qed. *)

  (* Compute k_mapping (mkRdfGraph [:: trpl1 ]). *)
  (* Compute k_mapping (mkRdfGraph [:: trpl1 ; trpl2]). *)
  
  Definition trpl3 : triple nat_countType nat_countType nat_countType.
  Proof. refine (mkTriple (@bnode_from_b nat nat nat 5) _ _).
         - exact (@b_in_ib nat nat nat 6).
         - exact (@i_in_i nat nat nat 42).
  Defined.

  Definition trpl4 : triple nat_countType nat_countType nat_countType.
  Proof. refine (mkTriple (@bnode_from_b nat nat nat 6) _ _).
         - exact (@b_in_ib nat nat nat 5).
         - exact (@i_in_i nat nat nat 42).
  Defined.
  Definition g := @mkRdfGraph nat_countType nat_countType nat_countType [:: trpl3].

  Definition all_maps := permutations (@ak_mapping nat_countType nat_countType nat_countType nat_countType 0 1%nat 2 0 (fun x=> size x) g).

  Time Compute all_maps.
  Definition all_maps2 := map (mapi (app_n (@mark_bnode' nat_countType nat_countType nat_countType nat_countType 0 1%nat 2 (fun x=> size x) ))) (permutations (bnodes (@init_hash nat_countType nat_countType nat_countType nat_countType 0 g))).
  Time Compute all_maps2.

  Definition mus := map (@build_mapping_from_seq nat_countType nat_countType nat_countType nat_countType 0 id) all_maps2.

  Time Compute mus.
  Definition isocans := map (fun mu => relabeling mu (mkRdfGraph [:: trpl3 ])) mus.
  Time Compute isocans.

  Compute (Order.min g g).
  Eval lazy in (Order.min g g).
  Eval vm_compute in (Order.min g g).



  Eval lazy in foldl Order.min (mkRdfGraph [:: trpl3 ]) isocans.
  Compute @k_mapping nat_countType nat_countType nat_countType nat_countType 0 1%nat 2 0 id (fun x=> size x) (mkRdfGraph [:: trpl3 ]).

End test.
