From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Term.
From RDF Require Import Triple.

Section Rdf.
  Axiom todo_rdf: forall t, t.

  Record rdf_graph (I B L : Type):= mkRdfGraph {
                                       graph : seq (triple I B L)
                                     }.

  Section PolyRdf.
    Variables I B L : Type.

    Definition empty_rdf_graph : rdf_graph I B L:= mkRdfGraph [::].

    Definition is_ground(g : rdf_graph I B L) : bool :=
      all (@is_ground_triple I B L) (graph g).

    (* assumes shared identifier scope *)
    Definition merge_rdf_graph (g h : rdf_graph I B L) : rdf_graph I B L :=
      todo_rdf _.

    Definition merge_seq_rdf_graph (gs : seq (rdf_graph I B L)) : rdf_graph I B L :=
      foldr merge_rdf_graph empty_rdf_graph gs.

    Definition add_triple (sg : option (rdf_graph I B L)) (t : (triple I B L)) : option (rdf_graph I B L).
    Proof. destruct sg as [g |].
           - destruct g as [g' sib ip ibl].
             exact (Some {|
                        graph := t :: g' ;
                      |}).
           - exact None.
    Defined.

    Definition relabeling_seq_triple (B' : Type) (μ : B -> B') (g : seq (triple I B L)) : seq (triple I B' L) :=
      map (relabeling_triple μ) g.

    Section Relabeling_seq_triple.
      Variable B' : Type.

      Lemma relabeling_seq_triple_comp_P (g1 g2 : seq (triple I B L)) (eqb : g1 = g2) (μ : B -> B') :
        relabeling_seq_triple μ g1 = relabeling_seq_triple μ g2.
      Proof. by rewrite eqb. Qed.

      Lemma relabeling_seq_triple_comp (μ1 μ2 : B -> B) (g : seq (triple I B L)) : relabeling_seq_triple μ1 (relabeling_seq_triple μ2 g) = (relabeling_seq_triple μ1 \o (relabeling_seq_triple μ2)) g.
      Proof. by []. Qed.

      Lemma relabeling_seq_triple_ext (μ1 μ2 : B -> B') : μ1 =1 μ2 -> forall g : seq (triple I B L), relabeling_seq_triple μ1 g = relabeling_seq_triple μ2 g.
      Proof. move => μpqeq. elim=> [//|h t IHt] /=. rewrite IHt. f_equal. by apply relabeling_triple_ext . Qed.
    End Relabeling_seq_triple.

    Lemma relabeling_seq_triple_id (g : seq (triple I B L)) : relabeling_seq_triple id g = g.
    Proof. elim g => [//| a l ihl] /=. by rewrite relabeling_triple_id ihl.
    Qed.

    Lemma relabeling_seq_triple_comp_simpl (g : seq (triple _ _ _)) (μ12 μ23 : B -> B) :
      relabeling_seq_triple (μ23 \o μ12) g = relabeling_seq_triple μ23 (relabeling_seq_triple μ12 g).
    Proof. elim g => [//|h t iht] /=. by rewrite relabeling_triple_comp; f_equal; apply iht.
    Qed.

    Definition relabeling (B' : Type) (μ : B -> B') (g : rdf_graph I B L): rdf_graph I B' L:=
      mkRdfGraph (relabeling_seq_triple μ (graph g)).

    Lemma relabeling_comp (g : rdf_graph I B L) (μ12 μ23: B -> B) :
      (relabeling μ23 \o (relabeling μ12)) g = relabeling (μ23 \o μ12) g.
    Proof. by case g => g'; rewrite /relabeling relabeling_seq_triple_comp_simpl //=.
    Qed.


    Section Relabeling_graph.
      Variable B' : Type.

      Lemma relabeling_id (g : rdf_graph I B L) : relabeling id g = g.
      Proof. case g => g' /=. by rewrite /relabeling relabeling_seq_triple_id.
      Qed.

      Lemma relabeling_ext  (μ1 μ2 : B -> B') :  μ1 =1 μ2 -> forall g, relabeling μ1 g = relabeling μ2 g.
      Proof. move=> μpweq g. by case g=> g'; rewrite /relabeling (relabeling_seq_triple_ext μpweq). Qed.

    End Relabeling_graph.

    Lemma relabeling_comp_simpl (μ1 μ2 : B -> B) (g : rdf_graph I B L) : relabeling μ1 (relabeling μ2 g) = relabeling (μ1 \o μ2) g.
    Proof. by rewrite -relabeling_comp. Qed.

  End PolyRdf.
  Section EqRdf.
    Variables I B L : eqType.

    Definition eqb_rdf (g1 g2 : rdf_graph I B L) : bool :=
      (graph g1) == (graph g2).

    Lemma eqb_rdf_refl (g : rdf_graph I B L) : eqb_rdf g g.
    Proof. by rewrite /eqb_rdf. Qed.

    Lemma eqb_rdf_symm (g1 g2 : rdf_graph I B L) : eqb_rdf g1 g2 = eqb_rdf g2 g1.
    Proof. by rewrite /eqb_rdf. Qed.

    Definition rdf_eqP : Equality.axiom eqb_rdf.
    Proof. rewrite /Equality.axiom => x y.
           apply: (iffP idP) => //= [| ->]; case: x y=> [g1] [g2].
           by rewrite /eqb_rdf => /eqP /= ->.
           by apply eqb_rdf_refl.
    Qed.

    Canonical rdf_eqType := EqType (rdf_graph I B L) (EqMixin rdf_eqP).

    Definition terms (g : rdf_graph I B L) : seq (term _ _ _) :=
      flatten (map (fun t => terms_triple t) (graph g)).

    Definition bnodes (g : rdf_graph I B L) : seq (term _ _ _) :=
      filter (fun t => is_bnode t) (terms g).

    Lemma bijective_eqb_rdf mu nu g1 g2 : cancel mu nu -> eqb_rdf g1 (relabeling mu g2) ->  eqb_rdf g2 (relabeling nu g1).
    Proof.
      move=> cancel_mu_nu. rewrite /eqb_rdf => /eqP /= ->.
      rewrite -relabeling_seq_triple_comp_simpl. 
      have /relabeling_seq_triple_ext-> : nu \o mu =1 id by [].
      rewrite relabeling_seq_triple_id; exact: eqb_rdf_refl.
    Qed.

    Definition is_iso (g1 g2 : rdf_graph I B L) (μ : B -> B) :=
      (bijective μ) /\ eqb_rdf g1 (relabeling μ g2).

    Definition iso (g1 g2 : rdf_graph I B L) := exists (μ : B -> B),
        is_iso g1 g2 μ.

    Lemma iso_refl (g : rdf_graph I B L) : iso g g.
    Proof. rewrite /iso /is_iso; exists id; split.
           exists id => //.
           by rewrite relabeling_id eqb_rdf_refl.
    Qed.

    Lemma iso_symm (g1 g2 : rdf_graph I B L) :
      iso g1 g2 <-> iso g2 g1.
    Proof.
      rewrite /iso /is_iso.
      split; case=> mu [mu_bij heqb_rdf]; case: (mu_bij)=> [nu h1 h2];
                                                         (exists nu; split; [exact: bij_can_bij h1 | exact: bijective_eqb_rdf heqb_rdf]).
    Qed.

    Lemma iso_trans (g1 g2 g3: rdf_graph I B L) : iso g1 g2 -> iso g2 g3 -> iso g1 g3.
    Proof. rewrite /iso/is_iso/eqb_rdf/relabeling => [[μ1 [bij1/eqP eqb1]] [μ2 [bij2/eqP eqb2]]].
           exists (μ1 \o μ2). split.
           by apply bij_comp.
           by rewrite eqb1 eqb2 relabeling_seq_triple_comp_simpl. 
    Qed.

    Definition isocanonical_mapping (M : rdf_graph I B L -> rdf_graph I B L) :=
      forall (g : rdf_graph I B L),
        iso (M g) g /\ forall (h : rdf_graph I B L), iso (M g) (M h) <-> iso g h.

  End EqRdf.

  Section CountRdf.
    Variables I B L : countType.

    Definition code_rdf (g : rdf_graph I B L) :=
      let (g') := g in
      GenTree.Node 0 (map (@code_triple I B L) g').

    Definition decode_rdf (x : GenTree.tree nat) : option (rdf_graph I B L).
    Proof. destruct x.
           - exact None.
           - destruct n as [| n'].
             + induction l as [| t ts IHts].
               * exact (Some (mkRdfGraph [::])).
               * destruct (@decode_triple I B L t) as [t'|].
                 -- apply (@add_triple I B L IHts t').
                 -- exact None.
             + exact None.
    Defined.

    Lemma cancel_rdf_encode : pcancel code_rdf decode_rdf.
    Proof. case => g. rewrite /code_rdf /decode_rdf.
           induction g as [| t ts IHts].
           - by [].
           - by rewrite /= cancel_triple_encode IHts. 
    Qed.

    Definition rdf_canChoiceMixin := PcanChoiceMixin cancel_rdf_encode.
    Definition rdf_canCountMixin := PcanCountMixin cancel_rdf_encode.

    Canonical rdf_choiceType := Eval hnf in ChoiceType (rdf_graph I B L) rdf_canChoiceMixin.
    Canonical rdf_countType := Eval hnf in CountType (rdf_graph I B L) rdf_canCountMixin.

    Definition rdf_canPOrderMixin := PcanPOrderMixin (@pickleK rdf_countType).
    Canonical rdf_POrderType := Eval hnf in POrderType tt (rdf_graph I B L) rdf_canPOrderMixin.

  End CountRdf.
End Rdf.

