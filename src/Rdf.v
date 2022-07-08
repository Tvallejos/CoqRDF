From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Term.
From RDF Require Import Triple.

Section Rdf.
  Axiom todo_rdf: forall t, t.

  Record rdf_graph (I B L : Type) := mkRdfGraph {
                                        graph :> seq (triple I B L) ;
                                     }.

  Section PolyRdf.
    Variables I B L : Type.
    Implicit Type g : rdf_graph I B L.
    Implicit Type t : triple I B L.
    Implicit Type ts : seq (triple I B L).

    Definition empty_rdf_graph := mkRdfGraph [::] : rdf_graph I B L.

    Definition is_ground g : bool :=
      all (@is_ground_triple _ _ _) g.

    (* assumes shared identifier scope *)
    Definition merge_rdf_graph g1 g2 : rdf_graph I B L :=
      todo_rdf _.

    Definition merge_seq_rdf_graph (gs : seq (rdf_graph I B L)) : rdf_graph I B L :=
      foldr merge_rdf_graph empty_rdf_graph gs.

    Definition add_triple (og : option (rdf_graph I B L)) t : option (rdf_graph I B L) :=
      match og with
      | Some ts => Some (mkRdfGraph (t::ts))
      | None=> None
      end.

    Definition relabeling_seq_triple
               (B' B'': Type) (μ : B' -> B'')
               (ts : seq (triple I B' L)) : seq (triple _ B'' _) :=
      map (relabeling_triple μ) ts.

    Section Relabeling_seq_triple.
      Variable B' : Type.

      Lemma relabeling_seq_triple_ext (μ1 μ2 : B -> B') :
        μ1 =1 μ2 -> forall ts, relabeling_seq_triple μ1 ts = relabeling_seq_triple μ2 ts.
      Proof. move => μpqeq. elim=> [//|t ts' IHts] /=.
             by rewrite IHts; f_equal; apply relabeling_triple_ext. Qed.

      Lemma relabeling_seq_triple_comp (B'' : Type) (μ2 : B -> B') (μ1 : B' -> B'') ts :
        relabeling_seq_triple μ1 (relabeling_seq_triple μ2 ts) = relabeling_seq_triple (μ1 \o μ2) ts.
      Proof. by elim ts => [//| t ts' ihts] /=; rewrite relabeling_triple_comp ihts. Qed.

    End Relabeling_seq_triple.

    Lemma relabeling_seq_triple_id ts : relabeling_seq_triple id ts = ts.
    Proof. by elim ts => [//| t ts' ihts] /= ; rewrite relabeling_triple_id ihts.
    Qed.

    Definition relabeling
               (B' B'' : Type) (μ : B' -> B'')
               (g : rdf_graph I B' L) : rdf_graph I B'' L:=
      mkRdfGraph (relabeling_seq_triple μ (graph g)).

    Lemma relabeling_comp (B' B'': Type) g (μ1 : B -> B') (μ2: B' -> B'') :
      relabeling μ2 (relabeling μ1 g) = relabeling (μ2 \o μ1) g.
    Proof. by case g => g'; rewrite /= /relabeling relabeling_seq_triple_comp.
    Qed.

    Section Relabeling_graph.
      Variable B' : Type.

      Lemma relabeling_id g : relabeling id g = g.
      Proof. case g => g' /=. by rewrite /relabeling relabeling_seq_triple_id.
      Qed.

      Lemma relabeling_ext  (μ1 μ2 : B -> B') :  μ1 =1 μ2 -> forall g, relabeling μ1 g = relabeling μ2 g.
      Proof. move=> μpweq g. by case g=> g'; rewrite /relabeling (relabeling_seq_triple_ext μpweq). Qed.

    End Relabeling_graph.
  End PolyRdf.

  Section EqRdf.
    Variables I B L : eqType.
    Implicit Type g : rdf_graph I B L.

    Definition eqb_rdf g1 g2 : bool :=
      (graph g1) == (graph g2).

    Lemma eqb_rdf_refl g : eqb_rdf g g.
    Proof. by rewrite /eqb_rdf. Qed.

    Lemma eqb_rdf_symm g1 g2 : eqb_rdf g1 g2 = eqb_rdf g2 g1.
    Proof. by rewrite /eqb_rdf. Qed.

    Definition rdf_eqP : Equality.axiom eqb_rdf.
    Proof. rewrite /Equality.axiom => x y.
           apply: (iffP idP) => //= [| ->]; case: x y=> [g1] [g2].
           by rewrite /eqb_rdf => /eqP /= ->.
           by apply eqb_rdf_refl.
    Qed.

    Canonical rdf_eqType := EqType (rdf_graph I B L) (EqMixin rdf_eqP).

    Variable g : rdf_graph I B L.
    Variable trm : term I B L.
    Print SetDef.finset.
    (* requieres trm to be finType *)
    Fail Check finset (trm \in g).

    Definition terms g : seq (term I B L) :=
      undup (flatten (map (@terms_triple I B L) (graph g))).

    Definition bnodes g : seq (term I B L) :=
      undup (filter (@is_bnode _ _ _) (terms g)).

    Lemma bijective_eqb_rdf mu nu g1 g2 :
      cancel mu nu -> eqb_rdf g1 (relabeling mu g2) ->  eqb_rdf g2 (relabeling nu g1).
    Proof.
      move=> cancel_mu_nu. rewrite /eqb_rdf => /eqP /= ->.
      rewrite relabeling_seq_triple_comp.
      have /relabeling_seq_triple_ext-> : nu \o mu =1 id by [].
      rewrite relabeling_seq_triple_id; exact: eqb_rdf_refl.
    Qed.

    Definition is_iso g1 g2 (μ : B -> B) :=
      (bijective μ) /\ eqb_rdf g1 (relabeling μ g2).

    Definition iso g1 g2 := exists (μ : B -> B),
        is_iso g1 g2 μ.

    Lemma iso_refl g : iso g g.
    Proof. rewrite /iso /is_iso; exists id; split.
           exists id => //.
           by rewrite relabeling_id eqb_rdf_refl.
    Qed.

    Lemma iso_symm g1 g2 : iso g1 g2 <-> iso g2 g1.
    Proof.
      rewrite /iso /is_iso.
      split; case=> mu [mu_bij heqb_rdf]; case: (mu_bij)=> [nu h1 h2];
                                                           (exists nu; split; [exact: bij_can_bij h1 | exact: bijective_eqb_rdf heqb_rdf]).
    Qed.

    Lemma iso_trans g1 g2 g3 : iso g1 g2 -> iso g2 g3 -> iso g1 g3.
    Proof. rewrite /iso/is_iso/eqb_rdf/relabeling => [[μ1 [bij1/eqP eqb1]] [μ2 [bij2/eqP eqb2]]].
           exists (μ1 \o μ2). split.
           by apply bij_comp.
           by rewrite eqb1 eqb2 relabeling_seq_triple_comp.
    Qed.

    Definition isocanonical_mapping (M : rdf_graph I B L -> rdf_graph I B L) :=
      forall g1, iso (M g1) g1 /\
                   forall g2, iso (M g1) (M g2) <-> iso g1 g2.

  End EqRdf.

  Section CountRdf.
    Variables I B L : countType.
    Implicit Type g : rdf_graph I B L.

    Definition code_rdf g :=
      GenTree.Node 0 (map (@code_triple I B L) g).

    Definition decode_rdf (x : GenTree.tree nat) : option (rdf_graph I B L).
    Proof. destruct x.
           - exact None.
           - destruct n as [| n'].
             + induction l as [| gen gens IHgens].
               * exact (Some (mkRdfGraph [::])).
               * destruct (@decode_triple I B L gen) as [t'|].
                 -- apply (@add_triple I B L IHgens t').
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

    Section FinTypeRdf.
      
      



    End FinTypeRdf.

  End CountRdf.
End Rdf.

