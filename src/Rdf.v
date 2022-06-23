From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Term.
From RDF Require Import Triple.

Section Rdf.

  Record rdf_graph {I B L : Type}:= mkRdfGraph {
                                       graph : seq triple
                                     ; subject_in_IB : all (fun t => @is_in_ib I B L (subject t)) graph
                                     ; predicate_in_I : all (fun t => @is_in_i I B L (predicate t)) graph
                                     ; object_in_IBL : all (fun t => @is_in_ibl I B L (object t)) graph
                                     }.

  Section PolyRdf.
    Variables I B L : Type.
    
    Definition terms (g : @rdf_graph I B L) : seq term :=
      flatten (map (fun t => terms_triple t) (graph g)).

    Definition bnodes (g : @rdf_graph I B L) : seq term :=
      filter (fun t => is_bnode t) (terms g).
    
    Definition add_sib (ts : seq triple) (pall : all (fun t => is_in_ib (subject t)) ts) (t : triple) : all (fun t => @is_in_ib I B L (subject t)) (t::ts).
    Proof. induction (t::ts).
           - apply all_nil.
           - rewrite /=. apply /andP ; split. by case a=> /= _ _ _ -> _ _. apply IHl.
    Qed.

    Definition add_i (ts : seq triple) (pall : all (fun t => is_in_i (predicate t)) ts) (t : triple) : all (fun t => @is_in_i I B L (predicate t)) (t::ts).
    Proof. induction (t::ts).
           - apply all_nil.
           - rewrite /=. apply /andP ; split. by case a=> /= _ _ _ _ -> _. apply IHl.
    Qed.

    Definition add_ibl (ts : seq triple) (pall : all (fun t => is_in_ibl (object t)) ts) (t : triple) : all (fun t => @is_in_ibl I B L (object t)) (t::ts).
    Proof. induction (t::ts).
           - apply all_nil.
           - rewrite /=. apply /andP ; split. by case a=> /= _ _ _ _ _ ->. apply IHl.
    Qed.

    Definition add_triple (sg : option (@rdf_graph I B L)) (t : (@triple I B L)) : option (@rdf_graph I B L).
    Proof. destruct sg as [g |].
           - destruct g as [g' sib ip ibl].
             exact (Some {|
                        graph := t :: g' ;
                        subject_in_IB := (@add_sib g' sib t) ;
                        predicate_in_I := (@add_i g' ip t) ;
                        object_in_IBL := (@add_ibl g' ibl t)
                      |}).
           - exact None.
    Defined.

    Definition relabeling_seq_triple (μ : B -> B) (g : seq (@triple I B L)) : seq triple := map (relabeling_triple μ) g.

    Lemma relabeling_seq_triple_comp_P (g1 g2 : seq triple) (eqb : g1 = g2) (μ : B->B) :
      relabeling_seq_triple μ g1 = relabeling_seq_triple μ g2. by rewrite eqb. Qed.

    Lemma relabeling_seq_triple_comp (μ1 μ2 : B -> B) (g : seq triple) : relabeling_seq_triple μ1 (relabeling_seq_triple μ2 g) = (relabeling_seq_triple μ1 \o (relabeling_seq_triple μ2)) g.
    Proof. by []. Qed.

    Lemma relabeling_seq_triple_preserves_subject_in_IB (g : seq triple) (μ : B -> B) :
      all (fun t => @is_in_ib I B L (subject t)) g ->
      all (fun t => @is_in_ib I B L (subject t)) (relabeling_seq_triple μ g).
    Proof. induction g => [//| /=]. move=> /andP [sinh sint]. apply /andP. split. case a => [s p o /= sintt pint oint].
           by rewrite relabeling_term_preserves_is_in_ib in sintt; apply sintt.
           by apply IHg; apply sint.
    Qed.

    Lemma relabeling_seq_triple_preserves_predicate_in_I (g : seq triple) (μ : B -> B) :
      all (fun t => is_in_i (predicate t)) g ->
      all (fun t => is_in_i (predicate t)) (relabeling_seq_triple μ g).
    Proof. induction g => [//| /=]. move=> /andP [pinh pin]. apply /andP. split. case a => [s p o /= sintt pint oint].
           by rewrite relabeling_term_preserves_is_in_i in pint; apply pint.
           by apply IHg; apply pin.
    Qed.

    Lemma relabeling_seq_triple_preserves_object_in_IBL (g : seq triple) (μ : B -> B) :
      all (fun t => is_in_ibl (object t)) g ->
      all (fun t => is_in_ibl (object t)) (relabeling_seq_triple μ g).
    Proof. induction g => [//| /=]. move=> /andP [oinh ointt]. apply /andP. split. case a => [s p o /= sintt pint oint].
           by rewrite relabeling_term_preserves_is_in_ibl in oint; apply oint.
           by apply IHg; apply ointt.
    Qed.

    Lemma relabeling_seq_triple_id (g : seq triple) : @relabeling_seq_triple id g = g.
    Proof. induction g => [//|]. rewrite /relabeling_seq_triple /=. f_equal.
           by rewrite relabeling_triple_id.
           rewrite /relabeling_seq_triple in IHg. exact IHg.
    Qed.

    Lemma relabeling_seq_triple_comp_simpl (g : seq triple) (μ12 μ23 : B -> B) :
      relabeling_seq_triple (μ23 \o μ12) g = (@relabeling_seq_triple μ23 \o (relabeling_seq_triple μ12)) g.
    Proof. rewrite /relabeling_seq_triple /=.
           elim g => [//|h t iht] /=. rewrite relabeling_triple_comp /=. by f_equal; apply iht.
    Qed.

    Lemma graph_inj : forall (g1 g2: rdf_graph),
        @graph I B L g1 = graph g2 ->
        g1 = g2.
    Proof.
      move=> [g1 sib1 pi1 oibl1] [g2 sib2 pi2 oibl2] /= geq. subst. 
      by f_equal; apply eq_irrelevance.
    Qed.

    Lemma forget_hd {T : Type} (t : T) (st : seq T) {p: T -> bool} (pall: all p (t::st)) : all p st.
    Proof. revert pall=> /=. by move /andP=> [_ ->]. Qed.

    Definition relabeling (μ : B -> B) (g : rdf_graph): rdf_graph :=
      let (g',siib,pii,oiibl) := g in
      {|
        graph := relabeling_seq_triple μ g';
        subject_in_IB :=  relabeling_seq_triple_preserves_subject_in_IB μ siib;
        predicate_in_I := relabeling_seq_triple_preserves_predicate_in_I μ pii;
        object_in_IBL := relabeling_seq_triple_preserves_object_in_IBL μ oiibl
      |}.

    Lemma relabeling_id (g : rdf_graph) : relabeling id g = g.
    Proof. apply graph_inj. case g=> g' sin pin oin /=.
           by rewrite relabeling_seq_triple_id.
    Qed.

    Lemma relabeling_comp (g : rdf_graph) (μ12 μ23: B -> B) :
      (relabeling μ23 \o (relabeling μ12)) g = relabeling (μ23 \o μ12) g.
    Proof. 
      induction g => [//]. rewrite /relabeling /=. apply graph_inj => /=.
      by rewrite relabeling_seq_triple_comp_simpl.
    Qed.

    Lemma relabeling_seq_triple_ext (μ1 μ2 : B -> B) : μ1 =1 μ2 -> forall g : seq (@triple I B L), relabeling_seq_triple μ1 g = relabeling_seq_triple μ2 g.
    Proof. move => μpqeq. elim=> [//|h t IHt] /=. rewrite IHt. f_equal. by apply relabeling_triple_ext. Qed.

    Lemma relabeling_ext  (μ1 μ2 : B -> B) :  μ1 =1 μ2 -> forall g, relabeling μ1 g = relabeling μ2 g.
    Proof. move=> μpweq g. induction g. apply /graph_inj => /=. by apply relabeling_seq_triple_ext. Qed.

    Lemma relabeling_comp_simpl (μ1 μ2 : B -> B) (g : rdf_graph) : relabeling μ1 (relabeling μ2 g) = relabeling (μ1 \o μ2) g.
    Proof. by rewrite -relabeling_comp. Qed.

  End PolyRdf.
  Section EqRdf.
    Variables I B L : eqType.
    
    Definition eqb_rdf (g1 g2 : @rdf_graph I B L) : bool :=
      (graph g1) == (graph g2).
    Lemma eqb_rdf_refl (g : rdf_graph) : eqb_rdf g g.
    Proof. by rewrite /eqb_rdf. Qed.

    Lemma eqb_rdf_symm (g1 g2 : rdf_graph) : eqb_rdf g1 g2 = eqb_rdf g2 g1.
    Proof. by rewrite /eqb_rdf. Qed.

    Definition rdf_eqP : Equality.axiom eqb_rdf.
    Proof. rewrite /Equality.axiom => x y.
           apply: (iffP idP) => //= [| ->];
                               case: x y=> [g1 sib1 pi1 oibl1] [g2 sib2 pi2 oibl2]. rewrite /eqb_rdf => /eqP /= geq. subst. by apply graph_inj. by apply eqb_rdf_refl.
    Qed.

    Canonical rdf_eqType := EqType rdf_graph (EqMixin rdf_eqP).

    Lemma bijective_eqb_rdf mu nu g1 g2 : cancel mu nu -> eqb_rdf g1 (relabeling mu g2) ->  eqb_rdf g2 (relabeling nu g1).
    Proof.
      move=> cancel_mu_nu. rewrite /eqb_rdf => /eqP /graph_inj ->. 
      rewrite relabeling_comp_simpl.
      have /relabeling_ext-> : nu \o mu =1 id by [].
      rewrite relabeling_id; exact: eqb_rdf_refl.
    Qed.

    Definition is_iso (g1 g2 : @rdf_graph I B L) (μ : B -> B) :=
      (bijective μ) /\ eqb_rdf g1 (relabeling μ g2).

    Definition iso (g1 g2 : rdf_graph):= exists (μ : B -> B),
        is_iso g1 g2 μ.

    Lemma iso_refl (g : rdf_graph) : iso g g.
    Proof. rewrite /iso /is_iso; exists id; split.
           exists id => //.
           by rewrite relabeling_id eqb_rdf_refl.
    Qed.

    Lemma iso_symm (g1 g2 : rdf_graph) :
      iso g1 g2 <-> iso g2 g1.
    Proof.
      rewrite /iso /is_iso.
      split; case=> mu [mu_bij heqb_rdf]; case: (mu_bij)=> [nu h1 h2];
                                                         (exists nu; split; [exact: bij_can_bij h1 | exact: bijective_eqb_rdf heqb_rdf]).
    Qed. 

    Lemma iso_trans (g1 g2 g3: rdf_graph) : iso g1 g2 -> iso g2 g3 -> iso g1 g3.
    Proof. rewrite /iso /is_iso /eqb_rdf => [[μ1 [bij1 /eqP /graph_inj eqb1]] [μ2 [bij2 /eqP /graph_inj eqb2]]].
           exists (μ1 \o μ2). split. 
           rewrite /=. apply bij_comp. apply bij1. apply bij2.
           rewrite -relabeling_comp /= -eqb2 -eqb1. by apply eqb_rdf_refl.
    Qed.

    Definition isocanonical_mapping (M : rdf_graph -> rdf_graph) :=
      forall (g : rdf_graph),
        iso (M g) g /\ forall (h : rdf_graph), iso (M g) (M h) <-> iso g h.

  End EqRdf.

  Section CountRdf.
    Variables I B L : countType.

    Definition code_rdf (g : rdf_graph) :=
      let (g',_,_,_) := g in
      GenTree.Node 0 (map (@code_triple I B L) g').

    Definition decode_rdf (x : GenTree.tree nat) : option (@rdf_graph I B L).
    Proof. destruct x.
           - exact None.
           - destruct n as [| n'].
             + induction l as [| t ts IHts].
               * exact (Some (mkRdfGraph
                                (all_nil (fun t => is_in_ib (subject t)))
                                (all_nil (fun t => is_in_i (predicate t)))
                                (all_nil (fun t => is_in_ibl (object t)))
                       )).
               * destruct (@decode_triple I B L t) as [t'|].
                 -- apply (@add_triple I B L IHts t').
                 -- exact None.
             + exact None.
    Defined.

    Lemma cancel_rdf_encode : pcancel code_rdf decode_rdf.
    Proof. case => g sib ii ibl. rewrite /code_rdf /decode_rdf.
           induction g as [| t ts IHts].
           - rewrite /=. f_equal. by apply graph_inj.
           - rewrite /=.
             have cant : (@decode_triple I B L (code_triple t)) = Some t. apply cancel_triple_encode.
             rewrite cant. rewrite IHts.
           - apply (forget_hd sib). apply (forget_hd ii). apply (forget_hd ibl).
             move=> sib' ii' ibl'. rewrite /add_triple /=. f_equal. apply graph_inj. by rewrite /eqb_rdf.
    Qed.

    Definition rdf_canChoiceMixin := PcanChoiceMixin cancel_rdf_encode.
    Definition rdf_canCountMixin := PcanCountMixin cancel_rdf_encode.

    Canonical rdf_choiceType := Eval hnf in ChoiceType rdf_graph rdf_canChoiceMixin.
    Canonical rdf_countType := Eval hnf in CountType rdf_graph rdf_canCountMixin.

    Definition rdf_canPOrderMixin := PcanPOrderMixin (@pickleK rdf_countType).
    Canonical rdf_POrderType := Eval hnf in POrderType tt rdf_graph rdf_canPOrderMixin.

  End CountRdf.
End Rdf.

