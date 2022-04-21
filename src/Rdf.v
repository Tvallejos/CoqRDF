From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Term.
(* From RDF Require Import Maps. *)
From RDF Require Import Triple.

Section rdf.
  Variable I B L: eqType.
  Let term:= (term I B L).
  Let triple:= (triple I B L).

  Record rdf_graph := mkRdfGraph {
                         graph : seq triple
                       ; subject_in_IB : forall (t : triple), t \in graph -> is_in_ib (subject t) == true
                       ; predicate_in_I : forall (t : triple), t \in graph -> is_in_i (predicate t) == true
                       ; object_in_IBL : forall (t : triple), t \in graph -> is_in_ibl (object t) == true
                       }.

  Definition eqb_rdf (g1 g2 : rdf_graph) : bool :=
    eqseq (graph g1) (graph g2).

  Lemma graph_inj : forall (g1 g2: rdf_graph),
      graph g1 == graph g2 ->
      g1 = g2.
  Proof. move=> [g1 sib1 pi1 oibl1] [g2 sib2 pi2 oibl2] /= /eqP geq.
  Admitted.
  

  Definition rdf_eqP : Equality.axiom eqb_rdf.
  Proof.
    rewrite /Equality.axiom => x y.
    apply: (iffP idP) => //= [| ->]; case: x y=> [g1 sib1 pi1 oibl1] [g2 sib2 pi2 oibl2]. move=> /eqP //= geq.
    apply: graph_inj => //=. by rewrite geq eq_refl.
    rewrite /eqb_rdf //=. elim g2 => [//|h t IHt]=> //=. rewrite eq_refl //=.
  Qed.


  Definition relabeling (g : rdf_graph) (μ : B -> B) : seq triple :=
    map (fun t => relabeling t μ) (graph g).

  (* Definition eqb_graph (g g': rdf_graph) : bool := *)
  (*   (match (set_diff eq_dec_triple (graph g) (graph g')) with *)
  (*    | nil => true *)
  (*    | otherwirse => false *)
  (*    end). *)

  (* Inductive world : Type := *)
  (* | res (I L B : set term) (P : set_inter eq_dec_term I (set_inter eq_dec_term L B) = empty_set term). *)

  (* Definition proj_I (w : world) : set term := *)
  (*   match w with *)
  (*   | res i _ _ _ => i *)
  (*   end. *)
  (* Definition proj_L (w : world) : set term := *)
  (*   match w with *)
  (*   | res _ l _ _ => l *)
  (*   end. *)

  (* Definition proj_B (w : world) : set term := *)
  (*   match w with *)
  (*   | res _ _ b _ => b *)
  (*   end. *)
  (* Definition proj_IL (w : world) : set term:= *)
  (*   set_union eq_dec_term (proj_I w) (proj_L w). *)

  (* Definition isomorphism (w : world) (g g': rdf_graph) := *)
  (*   exists μ : term -> term, *)
  (*     relabelling (proj_IL w) (proj_B w) μ -> (image g μ) = g'. *)

End rdf.

