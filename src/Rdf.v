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
                       ; subject_in_IB : all (fun t => is_in_ib (subject t)) graph
                       ; predicate_in_I : all (fun t => is_in_i (predicate t)) graph
                       ; object_in_IBL : all (fun t => is_in_ibl (object t)) graph
                       }.

  Definition eqb_rdf (g1 g2 : rdf_graph) : bool :=
    eqseq (graph g1) (graph g2).

  Lemma eq_ir : forall (g1 g2: seq triple)
                  (geq : g1 = g2)
                  (p : triple -> bool)
                  (fallt : all p g1),
                  all p g2.
  Proof. move=> g1 g2 eqg p fallt. by [rewrite -eqg].
  Qed.


  Lemma graph_inj : forall (g1 g2: rdf_graph),
      graph g1 == graph g2 ->
      g1 = g2.
  Proof. move=> [g1 sib1 pi1 oibl1] [g2 sib2 pi2 oibl2] /= /eqP geq.
         have: sib2 = (eq_ir geq sib1). apply eq_irrelevance.
         have: pi2 = (eq_ir geq pi1). apply eq_irrelevance.
         have: oibl2 = (eq_ir geq oibl1). apply eq_irrelevance. move => eqoibl eqpi eqsib.
         rewrite eqsib eqpi eqoibl. erewrite <-geq. f_equal; apply eq_irrelevance.
         Qed.
  
  Definition rdf_eqP : Equality.axiom eqb_rdf.
  Proof. rewrite /Equality.axiom => x y.
    apply: (iffP idP) => //= [| ->]; case: x y=> [g1 sib1 pi1 oibl1] [g2 sib2 pi2 oibl2]. move=> /eqP //= geq.
    apply: graph_inj => //=. by rewrite geq eq_refl.
    rewrite /eqb_rdf //=. elim g2 => [//|h t IHt]=> //=. rewrite eq_refl //=.
  Qed.

  Definition relabelingG (g : seq triple) (μ : B -> B) : seq triple :=
    map (fun t => relabeling t μ) g.

  Lemma relabelingG_preserves_subject_in_IB (g : seq triple) (μ : B -> B) :
    all (fun t => is_in_ib (subject t)) g ->
    all (fun t => is_in_ib (subject t)) (relabelingG g μ).
  Proof. move=> /allP sin. apply /allP => [[s p o /= sint pint oint]] => tg. apply sint. 
  Qed.

  Lemma relabelingG_preserves_predicate_in_I (g : seq triple) (μ : B -> B) :
    all (fun t => is_in_i (predicate t)) g ->
    all (fun t => is_in_i (predicate t)) (relabelingG g μ).
  Proof. move=> /allP pin. apply /allP => [[s p o /= sint pint oint]] => tg . apply pint.
  Qed.

  Lemma relabelingG_preserves_object_in_IBL (g : seq triple) (μ : B -> B) :
    all (fun t => is_in_ibl (object t)) g ->
    all (fun t => is_in_ibl (object t)) (relabelingG g μ).
  Proof. move=> /allP oin. apply /allP => [[s p o /= sibt pibt oint]] => tg . apply oint.
  Qed.

  Lemma relabel_ (g : seq triple) (μ : B -> B) : (all (fun t => is_in_ib (subject (relabeling t μ))) g) -> all (fun t => is_in_ib (subject t)) (relabelingG g μ).
  Proof.
    move=> /all_sigP H. apply /allP => [[s p o sin pin oin]] /= => _. apply sin.
    Qed.

  Definition relabeling (g : rdf_graph) (μ : B -> B) : rdf_graph :=
    let (g',siib,pii,oiibl) := g in
    {|
      graph := relabelingG g' μ;
      subject_in_IB :=  relabelingG_preserves_subject_in_IB μ siib;
      predicate_in_I := relabelingG_preserves_predicate_in_I μ pii;
      object_in_IBL := relabelingG_preserves_object_in_IBL μ oiibl
    |}.

  Definition is_iso (g1 g2 : rdf_graph) (μ : B -> B) : bool :=
    eqb_rdf g1 (relabeling g2 μ) && eqb_rdf (relabeling g1 μ) g2.

  Definition iso (g1 g2 : rdf_graph):= exists (μ : B -> B), is_iso g1 g2 μ.

  (* Lemma iso_refl : forall (g : rdf_graph), iso g g. *)
  (* Proof. rewrite /iso /is_iso /relabeling //=. exists id. *)



End rdf.

