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

  Lemma eq_ir : forall (g1 g2: seq triple)
                  (geq : g1 = g2)
                  (p : triple -> bool)
                  (fallt : forall (t : triple) (ting1 : t \in g1), p t == true),
    forall (t : triple) (ting2 : t \in g2), p t == true.
  Proof. move=> g1 g2 eqg p fallt. by rewrite -eqg.
  Qed.


  Lemma graph_inj : forall (g1 g2: rdf_graph),
      graph g1 == graph g2 ->
      g1 = g2.
  Proof. move=> [g1 sib1 pi1 oibl1] [g2 sib2 pi2 oibl2] /= /eqP geq.
         have: sib2 = eq_ir geq sib1.
         (* apply eq_irrelevance. *)
  Admitted.
  
  Definition rdf_eqP : Equality.axiom eqb_rdf.
  Proof.
    rewrite /Equality.axiom => x y.
    apply: (iffP idP) => //= [| ->]; case: x y=> [g1 sib1 pi1 oibl1] [g2 sib2 pi2 oibl2]. move=> /eqP //= geq.
    apply: graph_inj => //=. by rewrite geq eq_refl.
    rewrite /eqb_rdf //=. elim g2 => [//|h t IHt]=> //=. rewrite eq_refl //=.
  Qed.

  Definition relabelingG (g : seq triple) (μ : B -> B) : seq triple :=
    map (fun t => relabeling t μ) g.

  Lemma relabelingG_preserves_subject_in_IB : forall (g : seq triple) (μ : B -> B)
                                               (siib : forall (t : triple), t \in g -> is_in_ib (subject t) == true),
    forall (t : triple), t \in (relabelingG g μ) -> is_in_ib (subject t) == true.
  Proof. move=> g μ all_s_in_ib t mem_tg. destruct t => //=.
  Qed.

  Lemma relabelingG_preserves_predicate_in_I : forall (g : seq triple) (μ : B -> B)
                                                (pii : forall (t : triple), t \in g -> is_in_i (predicate t) == true),
    forall (t : triple), t \in (relabelingG g μ) -> is_in_i (predicate t) == true.
  Proof. move=> g μ all_s_in_ib t mem_tg. destruct t => //=.
  Qed.

  Lemma relabelingG_preserves_object_in_IBL : forall (g : seq triple) (μ : B -> B)
                                               (oiibl : forall (t : triple), t \in g -> is_in_ibl (object t) == true),
    forall (t : triple), t \in (relabelingG g μ) -> is_in_ibl (object t) == true.
  Proof. move=> g μ all_s_in_ib t mem_tg. destruct t => //=.
  Qed.

  Definition relabeling (g : rdf_graph) (μ : B -> B) : rdf_graph :=
    let (g',siib,pii,oiibl) := g in
    {|
      graph := relabelingG g' μ;
      subject_in_IB := relabelingG_preserves_subject_in_IB siib;
      predicate_in_I := relabelingG_preserves_predicate_in_I pii;
      object_in_IBL := relabelingG_preserves_object_in_IBL oiibl
    |}.

  Definition is_iso (g1 g2 : rdf_graph) (μ : B -> B) : bool :=
    eqb_rdf g1 (relabeling g2 μ) && eqb_rdf (relabeling g1 μ) g2.

  Definition iso (g1 g2 : rdf_graph):= exists (μ : B -> B), is_iso g1 g2 μ == true.

  (* Lemma iso_refl : forall (g : rdf_graph), iso g g. *)
  (* Proof. rewrite /iso /is_iso /relabeling //=. exists id. *)



End rdf.

