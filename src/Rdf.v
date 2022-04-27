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
    (graph g1) == (graph g2).

  Lemma eqb_rdf_refl (g : rdf_graph) : eqb_rdf g g.
  Proof. by rewrite /eqb_rdf. Qed.

  Lemma eqb_rdf_symm (g1 g2 : rdf_graph) : eqb_rdf g1 g2 = eqb_rdf g2 g1.
  Proof. by rewrite /eqb_rdf. Qed.

  Lemma eq_ir : forall (g1 g2: seq triple)
                  (geq : g1 = g2)
                  (p : triple -> bool)
                  (fallt : all p g1),
      all p g2.
  Proof. move=> g1 g2 eqg p fallt. by [rewrite -eqg].
  Qed.

  Lemma graph_inj : forall (g1 g2: rdf_graph),
      eqb_rdf g1 g2 ->
      g1 = g2.
  Proof.
    move=> [g1 sib1 pi1 oibl1] [g2 sib2 pi2 oibl2] /= /eqP /= geq.
    have eqsib: sib2 = (eq_ir geq sib1);
      have eqpi : pi2 = (eq_ir geq pi1);
      have eqoibl: oibl2 = (eq_ir geq oibl1); try apply eq_irrelevance.
    rewrite eqsib eqpi eqoibl. erewrite <-geq. f_equal; apply eq_irrelevance. 
  Qed.
  
  Definition rdf_eqP : Equality.axiom eqb_rdf.
  Proof. rewrite /Equality.axiom => x y.
         apply: (iffP idP) => //= [| ->]; case: x y=> [g1 sib1 pi1 oibl1] [g2 sib2 pi2 oibl2]. apply graph_inj. apply eqb_rdf_refl. 
  Qed.

  Definition relabelingG (μ : B -> B) (g : seq triple) : seq triple :=
    map (relabeling μ) g.

  Lemma relabelingG_id (g : seq triple) : relabelingG id g = g.
  Proof. rewrite /relabelingG. apply /eqP. elim g => [//|h t /eqP iht] /=. rewrite relabeling_id. by rewrite iht. Qed.
  
  (* map_comp: *)
  (*   forall [T1 T2 T3 : Type] (f1 : T2 -> T3) (f2 : T1 -> T2) (s : seq T1), *)
  (*   [seq (f1 \o f2) i | i <- s] = [seq f1 i | i <- [seq f2 i | i <- s]] *)

  Lemma relabelingG_comp (g : seq triple) (μ12 μ23 : B -> B) :
    relabelingG (μ23 \o μ12) g = (relabelingG μ23 \o (relabelingG μ12)) g.
  Proof. rewrite /relabelingG /=. elim g => [//|h t iht] /=. rewrite relabeling_comp /=. f_equal; apply iht.
  Qed.

  Lemma relabelingG_preserves_subject_in_IB (g : seq triple) (μ : B -> B) :
    all (fun t => is_in_ib (subject t)) g ->
    all (fun t => is_in_ib (subject t)) (relabelingG μ g).
  Proof. move=> /allP sin. apply /allP => [[s p o /= sint pint oint]] => tg. apply sint. 
  Qed.

  Lemma relabelingG_preserves_predicate_in_I (g : seq triple) (μ : B -> B) :
    all (fun t => is_in_i (predicate t)) g ->
    all (fun t => is_in_i (predicate t)) (relabelingG μ g).
  Proof. move=> /allP pin. apply /allP => [[s p o /= sint pint oint]] => tg . apply pint.
  Qed.

  Lemma relabelingG_preserves_object_in_IBL (g : seq triple) (μ : B -> B) :
    all (fun t => is_in_ibl (object t)) g ->
    all (fun t => is_in_ibl (object t)) (relabelingG μ g).
  Proof. move=> /allP oin. apply /allP => [[s p o /= sibt pibt oint]] => tg . apply oint.
  Qed.

  Definition relabeling (μ : B -> B) (g : rdf_graph): rdf_graph :=
    let (g',siib,pii,oiibl) := g in
    {|
      graph := relabelingG μ g';
      subject_in_IB :=  relabelingG_preserves_subject_in_IB μ siib;
      predicate_in_I := relabelingG_preserves_predicate_in_I μ pii;
      object_in_IBL := relabelingG_preserves_object_in_IBL μ oiibl
    |}.

  Lemma relabeling_id (g : rdf_graph) : relabeling id g = g.
  Proof. apply graph_inj. case g=> g' sin pin oin. rewrite /relabeling /= /eqP /eqb_rdf /=. by rewrite /eqP relabelingG_id.
  Qed.

  Lemma relabeling_comp (g : rdf_graph) (μ12 μ23: B -> B) :
    (relabeling μ23 \o (relabeling μ12)) g = relabeling (μ23 \o μ12) g.
  Proof. apply graph_inj. rewrite /eqb_rdf. apply /eqP.
         case g=> g' sin pin oin /=. by rewrite relabelingG_comp.
  Qed.

  Definition is_iso (g1 g2 : rdf_graph) (μ : B -> B) :=
    eqb_rdf g1 (relabeling μ g2) && eqb_rdf (relabeling μ g1) g2.

  Definition iso (g1 g2 : rdf_graph):= exists (μ : B -> B),
      (* (bijective μ) -> *)
      is_iso g1 g2 μ.

  Lemma iso_refl (g : rdf_graph) : iso g g.
  Proof. rewrite /iso /is_iso. exists id. by rewrite relabeling_id eqb_rdf_refl.
  Qed.

  Lemma iso_symm (g1 g2 : rdf_graph) : iso g1 g2 <-> iso g2 g1.
  Proof. rewrite /iso /is_iso. split=> [[μ] /andP [liso riso]|[μ] /andP [liso riso]];
                                      exists μ; apply /andP; split; rewrite eqb_rdf_symm; try apply riso; apply liso. Qed.

  Lemma iso_trans (g1 g2 g3: rdf_graph) : iso g1 g2 -> iso g2 g3 -> iso g1 g3.
  Proof. rewrite /iso /is_iso => [[μ12] /andP [/eqP  eqb12 /eqP eqb21]] [μ23] /andP [/eqP eqb23 /eqP eqb32].
         exists (μ23 \o μ12). apply /andP. split.
         apply /eqP. rewrite -relabeling_comp /=.
         rewrite eqb12. have g2rel: g2 = (relabeling μ23 g3). apply graph_inj. apply /eqP. apply eqb23.
         rewrite g2rel.
         (* need bijective μ!!!*)
  Abort.

End rdf.

