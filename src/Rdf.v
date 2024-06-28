From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Triple Term Util.

(******************************************************************************)
(* This file defines RDF graphs by parameterizing three types for its         *)
(* IRIs, blank nodes, and literals.                                           *)
(* We model RDF graphs using sequences of triples                             *)
(* Every RDF graph is well-formed, that is:                                   *)
(*   * every triple in the graph is well formed                               *)
(*   * every triple in the grpah appears only once                            *)
(*                                                                            *)
(* The definitions and theories of triples are divided in sections,           *)
(* which are organized by the required hypothesis to develop the theories     *)
(* of different operations.                                                   *)
(*                                                                            *)
(* For sequences of triples we define:                                        *)
(*                                                                            *)
(*  ** Predicates                                                             *)
(*      under the lexicographic comparison of le_triple                       *)
(*       lt_st ts1 ts2        ==   ts1 is less than or equal to ts2           *)
(*       le_st ts1 ts2        ==   ts1 is less than or equal to ts2           *)
(*       meet_st ts1 ts2      ==   the meet of t1 and ts2.                    *)
(*       join_st ts1 ts2      ==   the join of t1 and ts2.                    *)
(*                                                                            *)
(* For RDF graphs we define:                                                  *)
(*                                                                            *)
(*  ** Predicates                                                             *)
(*       eqb_rdf g1 g2        ==  g1 compares equal to g2 under set equality  *)
(*       t \in g              ==  t is a member of the underlying             *)
(*                                sequence of g                               *)
(*       is_ground g          ==  every triple in g is ground                 *)
(*       is_pre_iso g1 g2 mu  ==  the blank nodes of g1 and g2 are in a       *)
(*                                one-to-one correspondence under mu          *)
(*       is_iso g1 g2 mu      ==  mu is a pre-isomorphism preserving          *)
(*                                adyacency                                   *)
(*                                                                            *)
(*  ** Blank node relabeling                                                  *)
(*       relabeling mu g      == the relabeling of every triple of g under mu *)
(*                                                                            *)
(*  ** Projections                                                            *)
(*       terms g              == the duplicate free sequence of the terms in  *)
(*                               the triples of g                             *)
(*       bnodes g             == the duplicate free sequence of the terms in  *)
(*                               the triples of g, which are blank nodes      *)
(*                                                                            *)
(* ** Propositions                                                            *)
(*      isocanonical_mapping M  == M is a map from graphs to graphs which     *)
(*                                 1. returns graphs which are isomorphic to  *)
(*                                    the input graph                         *)
(*                                 2. for two graphs g and h, M returns       *)
(*                                    set-equal graphs under M if and and only*)
(*                                    if g and h are isomorphic               *)
(*                                                                            *)
(******************************************************************************)

Section Rdf.

  Record rdf_graph (I B L : eqType) :=
    mkRdfGraph
      {
        graph :> seq (triple I B L) ;
        ugraph : uniq graph
      }.

  Definition mkRdf {I B L : eqType} (s : seq (triple I B L)) :=
    @mkRdfGraph I B L (undup s) (undup_uniq s).

  Section EqRdf.

    Lemma rdf_inj (I B L : eqType) (g1 g2 : rdf_graph I B L) :
      graph g1 = graph g2 ->
      g1 = g2.
    Proof.
      case: g1 g2 => [g1' ug1] [g2' ug2'] /= eq.
      subst; congr mkRdfGraph; exact: eq_irrelevance.
    Qed.

    Section CodeRdf.
      Variables I B L : eqType.

      Definition code_rdf g : (seq (triple I B L))%type :=
        graph g.

      Definition decode_rdf (s : seq (triple I B L)) : option (rdf_graph I B L) :=
        if insub s : {? x | uniq x} is Some us
        then Some (mkRdfGraph (valP us))
        else None.

      Lemma pcancel_code_decode : pcancel code_rdf decode_rdf.
      Proof. case=> g ug=> /= ; rewrite /decode_rdf.
             case: insubP=> [? _ ?|]; last by rewrite ug.
             by congr Some; apply: rdf_inj.
      Qed.

    End CodeRdf.
    Variables I B L : eqType.
    Implicit Type g : rdf_graph I B L.

    Definition eqb_rdf g1 g2 : bool :=
      perm_eq (graph g1) (graph g2).

    Lemma eqb_rdf_refl g : eqb_rdf g g.
    Proof. exact: perm_refl. Qed.

    Lemma eqb_rdf_sym g1 g2 : eqb_rdf g1 g2 = eqb_rdf g2 g1.
    Proof. exact: perm_sym. Qed.

    Lemma eqb_rdf_trans g1 g2 g3: eqb_rdf g1 g2 -> eqb_rdf g2 g3 -> eqb_rdf g1 g3.
    Proof. exact: perm_trans. Qed.

    Definition eqb_ts (ts1 ts2 : seq (triple I B L)) := ts1 == ts2.

    Lemma ts_eqP : Equality.axiom eqb_ts.
    Proof. by move=> x y; apply eqseqP. Qed.

    Canonical rdf_predType (i b l : eqType) :=
      Eval hnf in PredType (pred_of_seq \o (@graph i b l)).

    Implicit Type t : triple I B L.
    Implicit Type ts : seq (triple I B L).

    Definition empty_rdf_graph {i b l : eqType} := @mkRdfGraph i b l [::] (eqxx true) : rdf_graph i b l.

    Definition is_ground_ts ts : bool :=
      all (@is_ground_triple _ _ _) ts.

    Definition is_ground g : bool :=
      is_ground_ts g.

    Definition relabeling_seq_triple
      (B1 B2: Type) (mu : B1 -> B2)
      (ts : seq (triple I B1 L)) : seq (triple I B2 L) :=
      map (relabeling_triple mu) ts.

    Section Relabeling_seq_triple_poly.
      Variable B1 B2 B3 : Type.

      Lemma relabeling_seq_triple_id ts : relabeling_seq_triple id ts = ts.
      Proof. by elim ts => [//| t ts' ihts] /=; rewrite relabeling_triple_id ihts. Qed.

      Lemma relabeling_seq_triple_ext (mu1 mu2 : B -> B1) ts :
        mu1 =1 mu2 -> relabeling_seq_triple mu1 ts = relabeling_seq_triple mu2 ts.
      Proof. move=> mu_eq; apply: eq_map; exact: relabeling_triple_ext. Qed.

      Lemma relabeling_seq_triple_comp (mu2 : B1 -> B2) (mu1 : B2 -> B3) (ts : seq (triple I B1 L)) :
        relabeling_seq_triple mu1 (relabeling_seq_triple mu2 ts) =
          relabeling_seq_triple (mu1 \o mu2) ts.
      Proof.
        by rewrite /relabeling_seq_triple -map_comp; apply: eq_map=> x; rewrite relabeling_triple_comp.
      Qed.

      Lemma relabeling_triple_map_comp (ts : seq (triple I B1 L)) (mu1: B1 -> B2) (mu2 : B2 -> B3) :
        [seq relabeling_triple mu2 i | i <- [seq relabeling_triple mu1 i | i <- ts]] =
          [seq relabeling_triple (mu2 \o mu1) i | i <- ts].
      Proof. have ->: [seq relabeling_triple (mu2 \o mu1) i | i <- ts] = relabeling_seq_triple (mu2 \o mu1) ts by [].
             by rewrite -relabeling_seq_triple_comp.
      Qed.

      Lemma relabeling_seq_triple_nil (mu : B1 -> B2) :
        relabeling_seq_triple mu [::] = [::].
      Proof. by []. Qed.

      Lemma eq_relabeling_seq_triple (mu nu : B1 -> B2) : mu =1 nu -> (relabeling_seq_triple mu) =1 (relabeling_seq_triple nu).
      Proof. move=> feq; elim=> [//| h t IHtl] /=.
             by rewrite (eq_relabeling_triple feq) IHtl.
      Qed.

      Lemma relabeling_ground ts mu : is_ground_ts ts -> relabeling_seq_triple mu ts = ts.
      Proof. elim: ts=> [//| a l IHl] /=/andP[gtrpl gtl].
             by rewrite ground_triple_relabeling // IHl.
      Qed.

    End Relabeling_seq_triple_poly.
    Section Relabeling_seq_triple_eq.

      Lemma relabeling_seq_triple_rel_mem ts1 ts2 (mu : B -> B) :
        ts1 =i ts2 ->
        relabeling_seq_triple mu ts1 =i relabeling_seq_triple mu ts2.
      Proof. by apply eq_mem_map. Qed.

      Lemma relabeling_mem (ts1 ts2: seq (triple I B L)) (mu : B -> B) :
        ts1 =i ts2 -> relabeling_seq_triple mu ts1 =i relabeling_seq_triple mu ts2.
      Proof. by apply eq_mem_map. Qed.

      Lemma relabeling_ext_in (B1 : eqType) (mu1 mu2 : B -> B1) (ts : seq (triple I B L)):
        {in ts, relabeling_triple mu1 =1  relabeling_triple mu2} ->
        relabeling_seq_triple mu1 ts =i relabeling_seq_triple mu2 ts.
      Proof. elim: ts => [//| tr tl ihtl].
             move=> /= eq; rewrite eq; last by rewrite mem_head.
             by move => ?; rewrite !in_cons ihtl // => x xin; apply eq; apply mem_cons.
      Qed.

      Lemma uniq_rdf_graph g : uniq g. Proof. exact: ugraph. Qed.
      Hint Resolve uniq_rdf_graph.

      Lemma bijective_perm_eq_relabeling_st mu nu ts1 ts2 :
      uniq (relabeling_seq_triple nu ts1) ->
      cancel mu nu -> perm_eq (relabeling_seq_triple mu ts2) ts1 -> perm_eq ts2 (relabeling_seq_triple nu ts1).
      Proof. move=> urtnu can_munu /(perm_map (relabeling_triple nu)) peq.
             have can_id: {in ts2, [eta relabeling_triple (nu \o mu)] =1 id}.
             by move=>  [[]s []p []o ? ?] _ //; apply triple_inj=> //=; rewrite can_munu.
             have peq_can: perm_eq ts2 [seq relabeling_triple nu i | i <- relabeling_seq_triple mu ts2].
             by rewrite relabeling_triple_map_comp map_id_in //.
             apply: perm_trans peq_can peq.
      Qed.

      Lemma perm_eq_relab_uniq_ts ts1 ts2 mu (u2 : uniq ts2) : perm_eq (relabeling_seq_triple mu ts1) ts2 -> perm_eq (relabeling_seq_triple mu ts1) ts2 /\ uniq (relabeling_seq_triple mu ts1).
      Proof. by move=> peq; rewrite (perm_uniq peq) peq. Qed.

      Lemma perm_eq_relab_uniq g1 g2 mu : perm_eq (relabeling_seq_triple mu g1) g2 -> perm_eq (relabeling_seq_triple mu g1) g2 /\ uniq (relabeling_seq_triple mu g1).
      Proof. by apply perm_eq_relab_uniq_ts. Qed.

      Lemma relabeling_triple_comp_map (B1 B2 B3 : eqType) (g : rdf_graph I B1 L) (mu12 : B1 -> B2) (mu23 : B2 -> B3) :
        [seq relabeling_triple mu23 i | i <- relabeling_seq_triple mu12 g] =
          relabeling_seq_triple (mu23 \o mu12) g.
      Proof. case g=> g' us=> /=; rewrite -map_comp.
             by elim g'=> [//| h t IHts] /=; last by rewrite relabeling_triple_comp -IHts.
      Qed.

      Lemma perm_eq_comp ts1 ts2 ts3 mu12 mu23:
        perm_eq (relabeling_seq_triple mu12 ts1) ts2 ->
        perm_eq (relabeling_seq_triple mu23 ts2) ts3 ->
        perm_eq (relabeling_seq_triple (mu23 \o mu12) ts1) ts3.
      Proof. by move=> /(perm_map (relabeling_triple mu23)); rewrite relabeling_triple_map_comp; apply perm_trans. Qed.

    End Relabeling_seq_triple_eq.
    Section Rdf_mem.

      Lemma rdf_perm_mem_eq {i b l : eqType} (g1 g2 :rdf_graph i b l) :
        (perm_eq g1 g2) <-> (g1 =i g2).
      Proof. split; first by move=> /perm_mem.
             by move: (ugraph g1) (ugraph g2); apply uniq_perm.
      Qed.

      Lemma rdf_mem_eq_graph g1 g2 :
        g1 =i g2 <-> (graph g1) =i (graph g2).
      Proof. by []. Qed.

    End Rdf_mem.

    Definition relabeling
      (B1 B2 : eqType) (mu : B1 -> B2)
      (g : rdf_graph I B1 L)  (urel : uniq (relabeling_seq_triple mu (graph g))): rdf_graph I B2 L:=
      mkRdfGraph urel.

    Definition relabeling_undup
      (B1 B2 : eqType) (mu : B1 -> B2)
      (g : rdf_graph I B1 L) : rdf_graph I B2 L:=
      mkRdf (relabeling_seq_triple mu (graph g)).

    Section Relabeling_graph.

      Lemma relabeling_comp (B1 B2: eqType) g (mu1 : B -> B1) (mu2: B1 -> B2) :
        forall u1 u2 u12,
          perm_eq (@relabeling B1 B2 mu2 (@relabeling B B1 mu1 g u1) u2) (@relabeling B B2 (mu2 \o mu1) g u12).
      Proof. move=> u1 u2 u12; rewrite rdf_perm_mem_eq /relabeling/==> x /=.
             suffices ->: {| graph := relabeling_seq_triple mu2 (relabeling_seq_triple mu1 g); ugraph := u2 |} = {| graph := relabeling_seq_triple (mu2 \o mu1) g; ugraph := u12 |} by [].
             by apply rdf_inj; rewrite /= relabeling_seq_triple_comp.
      Qed.

      Lemma relabeling_id g : forall us, (@relabeling B B id g us) = g.
      Proof. by case g => g' ug us ; apply rdf_inj=> /=; rewrite relabeling_seq_triple_id. Qed.

      Variable B1 : eqType.

      Lemma relabeling_ext  (mu1 mu2 : B -> B1) g (mu_ext: mu1 =1 mu2) :
        forall u1 u2, @relabeling B B1 mu1 g u1 = @relabeling B B1 mu2 g u2.
      Proof. by move=> u1 u2; apply /rdf_inj; rewrite /= (relabeling_seq_triple_ext _ mu_ext). Qed.

      Lemma relabeling_seq_triple_is_nil (B2 : eqType) (ts : seq (triple I B1 L)) (mu : B1 -> B2) :
        relabeling_seq_triple mu ts = [::] -> ts = [::].
      Proof. by move=> /eqP; rewrite /relabeling_seq_triple map_nil_is_nil=> /eqP->. Qed.

      Lemma relabeling_nil (B2 : eqType) (mu : B1 -> B2) :
        @relabeling B1 B2 mu empty_rdf_graph (eqxx true) = empty_rdf_graph.
      Proof. by apply rdf_inj. Qed.

      Lemma relabeling_cons (B2 : eqType) (mu: B1 -> B2) (trpl : triple I B1 L) (ts : seq (triple I B1 L)) (ucons : uniq (trpl :: ts)) :
        forall us,
          @relabeling B1 B2 mu (mkRdfGraph ucons) us =
            mkRdfGraph (undup_uniq (relabeling_triple mu trpl :: (relabeling_seq_triple mu ts))).
      Proof. by move=> us; apply rdf_inj=> /=; move: us=> /andP[/negPf -> /undup_id ->]. Qed.

      Lemma bijective_eqb_rdf mu nu g1 g2 :
        forall us1 us2,
          cancel mu nu -> eqb_rdf (@relabeling _ _ mu g2 us1) g1 -> eqb_rdf g2 (@relabeling _ _ nu g1 us2).
      Proof.
        by move=> us1 us2 can_munu; rewrite /eqb_rdf/relabeling/=; apply bijective_perm_eq_relabeling_st.
      Qed.

      Lemma eqb_relabeling_comp g1 g2 g3 mu12 mu23:
        forall u1 u2 u3,
          eqb_rdf (@relabeling _ _ mu12 g1 u1) g2 ->
          eqb_rdf (@relabeling _ _ mu23 g2 u2) g3 ->
          eqb_rdf (@relabeling _ _ (mu23 \o mu12) g1 u3) g3.
      Proof. by move=> u1 u2 u3; apply perm_eq_comp. Qed.


    End Relabeling_graph.

    Section Terms_ts.

      Definition terms_ts {i b l : eqType} (ts : seq (triple i b l)) : seq (term i b l) :=
        undup (flatten (map (@terms_triple i b l) ts)).

      Lemma undup_terms_ts ts : undup (terms_ts ts) = (terms_ts ts).
      Proof. by rewrite undup_idem. Qed.

      Lemma uniq_terms_ts (i b l : eqType) (ts : seq (triple i b l)) : uniq (terms_ts ts).
      Proof. by apply undup_uniq. Qed.
      Hint Resolve uniq_terms_ts.

      Remark uniq_tail (T: eqType) a (t : seq T) : (uniq (a :: t)) -> uniq t.
      Proof. by move=> /andP[_ //]. Qed.

      Lemma terms_ts_cons {i b l : eqType} (trpl : triple i b l) (ts : seq (triple i b l)) :
        terms_ts (trpl :: ts) = undup (terms_triple trpl ++ (terms_ts ts)).
      Proof. by case: ts =>  [ // | ? ? /= ]; rewrite undup_cat_r. Qed.

      Lemma mem_triple_terms_ts t ts: t \in ts -> [&& (subject t) \in (terms_ts ts),
              ((predicate t) \in (terms_ts ts)) & ((object t) \in terms_ts ts)].
      Proof. case t=> s p o ? ? /=; elim: ts=> [//|hd tl IHts] /= t_mem.
             apply /and3P; rewrite !terms_ts_cons !mem_undup; move: t_mem; rewrite !in_cons /terms_triple !mem_cat; case/orP.
             + by move=> /eqP <-; rewrite !mem_undup !in_cons !eqxx /= !orbT.
             + by move=> /IHts /and3P[-> -> ->]; rewrite !orbT.
      Qed.

      Section Term_ts_Relabeling.
        Variable B1 B2: eqType.

        Lemma terms_ts_relabeled_mem (ts : seq (triple I B1 L)) (mu: B1 -> B2) :
        (terms_ts (relabeling_seq_triple mu ts)) =i (map (relabeling_term mu) (terms_ts ts)).
        Proof. elim: ts=> [//| h t IHt] /= x.
               by rewrite !terms_ts_cons !mem_undup -mem_map_undup map_cat !mem_cat IHt terms_relabeled_triple_mem.
        Qed.

        Lemma terms_ts_relabeled (ts : seq (triple I B1 L)) (mu : B1 -> B2) (mu_inj: injective mu):
          terms_ts (relabeling_seq_triple mu ts) = [seq relabeling_term mu i | i <- terms_ts ts].
        Proof.
          have /(_ I L) rts_inj := (relabeling_triple_inj mu_inj).
          have /(_ I L) rt_inj := (relabeling_term_inj mu_inj).
          elim: ts=> [//| h tl IHtl].
          have step: undup ([seq relabeling_term mu i | i <- terms_triple h] ++
                            [seq relabeling_term mu i | i <- flatten [seq terms_triple i | i <- tl]]) =
                 undup
                   ([seq relabeling_term mu i | i <- terms_triple h] ++
                      undup [seq relabeling_term mu i | i <- flatten [seq terms_triple i | i <- tl]]) by rewrite undup_cat_r.
          rewrite -undup_map_inj // !terms_ts_cons /= map_cat step.
          by apply f_equal; rewrite IHtl terms_relabeled_triple // undup_map_inj.
        Qed.

      End Term_ts_Relabeling.

      Section Bnodes_ts.
        Definition bnodes_ts (i b l : eqType) (ts : seq (triple i b l)): seq (term i b l) :=
        undup (filter (@is_bnode i b l) (terms_ts ts)).

        Lemma bnodes_ts_cons (trpl : triple I B L) (ts : seq (triple I B L)) :
          bnodes_ts (trpl :: ts) = undup ((bnodes_triple trpl) ++ (bnodes_ts ts)).
        Proof. by rewrite /bnodes_ts terms_ts_cons filter_undup undup_idem undup_cat_r filter_cat. Qed.

        Lemma all_bnodes_ts ts : all (@is_bnode I B L) (bnodes_ts ts).
        Proof. elim: ts=> [// | t ts IHts].
               by rewrite bnodes_ts_cons all_undup all_cat IHts Bool.andb_true_r all_bnodes_triple_is_bnode.
        Qed.

        Lemma all_bnodes_perm ts s:
          perm_eq (bnodes_ts ts) s -> forall x, x \in s -> is_bnode x.
        Proof. by move=> peq x xin; apply (in_all xin); rewrite -(perm_all _ peq) all_bnodes_ts. Qed.

        Lemma uniq_bnodes_ts ts : uniq (bnodes_ts ts).
        Proof. exact: undup_uniq. Qed.
        Hint Resolve uniq_bnodes_ts.

        Lemma i_in_bnodes_ts id ts: Iri id \in bnodes_ts ts = false.
        Proof. by rewrite /bnodes_ts -filter_undup mem_filter. Qed.

        Lemma l_in_bnodes_ts l ts: Lit l \in bnodes_ts ts = false.
        Proof. by rewrite /bnodes_ts -filter_undup mem_filter. Qed.

      Lemma bterms_ts b ts : Bnode b \in (terms_ts ts) -> Bnode b \in (bnodes_ts ts).
      Proof. by move=> mem_term; rewrite mem_undup mem_filter. Qed.

        Section Bnodes_ts_relabeling.
          Variables B1 B2 : eqType.

          Lemma filter_map_rt (trms: seq (term I B1 L)) (us: uniq trms) (mu: B1 -> B2) :
            [seq x <- [seq relabeling_term mu i | i <- trms ] | is_bnode x] =i
                                                                             [seq relabeling_term mu i | i <- trms & is_bnode i].
          Proof. elim: trms us=> [//| hd tl IHtl] [/andP[nin utl]] x /=.
                 case e: (is_bnode hd) nin.
                 by rewrite bnodes_to_bnodes //= in_cons IHtl.
                 have -> : is_bnode (relabeling_term mu hd) = false by move : e; case hd=> //.
                 by rewrite IHtl.
          Qed.

          Lemma bnodes_ts_relabel_mem (ts : seq (triple I B1 L)) (mu: B1 -> B2) :
            bnodes_ts (relabeling_seq_triple mu ts) =i (map (relabeling_term mu) (bnodes_ts ts)).
          Proof. move=> x; rewrite mem_undup -mem_map_undup.
                 by rewrite mem_filter terms_ts_relabeled_mem -mem_filter filter_map_rt.
          Qed.

          Lemma bnodes_ts_relabel_inj (ts: seq (triple I B1 L)) (mu: B1 -> B2) (mu_inj : injective mu):
            bnodes_ts (relabeling_seq_triple mu ts) = (map (relabeling_term mu) (bnodes_ts ts)).
          Proof.
            have /(_ I L) rtmu_inj := relabeling_term_inj mu_inj.
            rewrite /bnodes_ts terms_ts_relabeled // -filter_undup undup_map_inj // -filter_undup.
            elim: (undup (terms_ts ts)) => [// | hd tl IHtl] /=.
                 case e: (is_bnode hd).
                 by rewrite bnodes_to_bnodes // IHtl.
                 have -> : is_bnode (relabeling_term mu hd) = false by move : e; case hd=> //.
                 by rewrite IHtl.
          Qed.

          Lemma bnodes_map_get_bs ts : bnodes_ts ts = map (fun b=> Bnode b) (get_bs (bnodes_ts ts)).
          Proof.
            move: (all_bnodes_ts ts).
            rewrite /bnodes_ts filter_undup // undup_idem -filter_undup.
            elim: [seq x <- undup (flatten [seq terms_triple i | i <- ts]) | is_bnode x]=> [//| []//=b t IHt] al.
            by rewrite -IHt.
          Qed.

          Lemma bterm_eq_mem_get_bs (b: B) ts :
            (@Bnode I B L b) \in terms_ts ts ->
                                 b \in get_bs (bnodes_ts ts).
          Proof. by move=> /bterms_ts; rewrite {1}bnodes_map_get_bs (mem_map  (@bnode_inj I B L)). Qed.

          (* TODO add subgoals as lemmas *)
          Lemma mem_ts_mem_triple_bs t ts b :
            t \in ts -> Bnode b \in bnodes_triple t -> b \in get_bs (bnodes_ts ts).
          Proof. move=> /mem_triple_terms_ts; case t=> [[]]s []p []o ? ? //= /and3P[sint pint oint];
                                                  rewrite /bnodes_triple filter_undup mem_undup ?in_cons in_nil // Bool.orb_false_r=> /eqP[eq]; move: sint oint; rewrite ?eq=> sint oint; rewrite bterm_eq_mem_get_bs //.
                 by move: eq=> /eqP; case/orP=> /eqP[->].
          Qed.

          Lemma can_bs_can_rtbs ts (mu nu: B -> B) :
            {in get_bs (bnodes_ts ts), nu \o mu =1 id} ->
              {in ts, [eta relabeling_triple (nu \o mu)] =1 id}.
          Proof. move=> /= in_getb [s p o sib pii] /mem_ts_mem_triple_bs ing /=; apply triple_inj=> /=.
                 + case: s sib ing  => // b sib ing.
                   by rewrite /= in_getb // ing // /bnodes_triple filter_undup mem_undup in_cons eqxx.
                 + by case: p pii ing  => // b sib /mem_g_mem_triple_b inb /=.
                 + case: o ing  => // b ing /=.
                   by rewrite /= in_getb // ing // /bnodes_triple filter_undup mem_undup mem_filter -mem_rev in_cons eqxx.
          Qed.

        End Bnodes_ts_relabeling.

        Definition get_bts {i b l : eqType} (ts : seq (triple i b l)) : seq b :=
          get_bs (bnodes_ts ts).

        Lemma mem_ts_mem_triple_bts t ts b :
          t \in ts -> Bnode b \in bnodes_triple t -> b \in get_bts ts.
        Proof. by apply mem_ts_mem_triple_bs. Qed.

        Lemma bnodes_map_get_bts ts : bnodes_ts ts = map (fun b=> Bnode b) (get_bts ts).
        Proof. exact: bnodes_map_get_bs. Qed.

        Lemma uniq_get_bs ts : uniq (get_bs (bnodes_ts ts)).
        Proof. by rewrite -(undup_get_bsC (uniq_bnodes_ts ts)) undup_uniq. Qed.
        Hint Resolve uniq_get_bs.

        Lemma uniq_get_bts ts : uniq (get_bts ts).
        Proof. by rewrite uniq_get_bs. Qed.

        Lemma undup_idem_get_bs ts : undup (get_bts ts) = get_bts ts.
        Proof. by rewrite undup_get_bsC. Qed.

        Lemma bterm_eq_mem_get_bts (b: B) ts :
          (@Bnode I B L b) \in terms_ts ts ->
                               b \in get_bs (bnodes_ts ts).
        Proof. by apply bterm_eq_mem_get_bs. Qed.

        Lemma is_ground_get_bts ts : is_ground_ts ts <-> (get_bts ts) = [::].
        Proof. split; rewrite /is_ground_ts/get_bts.
               elim: ts=> [//| a l IHl] /= /andP[ghd gtl].
               suffices ghd_nil : bnodes_triple a = [::].
                 by rewrite /= bnodes_ts_cons ghd_nil /= -undup_get_bs IHl //.
               by apply/eqP; rewrite -is_ground_triple_bnodes_nil.
               move=> /get_bs_nil_all_not_b.
               elim: ts=> [//| a l IHl] /=.
                 rewrite bnodes_ts_cons all_undup all_cat is_ground_not_bnode=> /andP[hdnil tlnil].
                 apply/andP; split; last by apply IHl.
                 move: hdnil. rewrite /bnodes_triple/terms_triple.
                 by case a=> [[]]s []p []o ? ? //; rewrite filter_undup all_undup.
        Qed.


        Lemma perm_relabel_bnodes_ts ts1 ts2 mu :
          perm_eq [seq relabeling_term mu i | i <- bnodes_ts ts1] (bnodes_ts ts2) =
            perm_eq [seq mu i | i <- get_bs (bnodes_ts ts1)] (get_bs (bnodes_ts ts2)).
        Proof. rewrite -(get_bs_map mu (all_bnodes_ts ts1)).
               case e : (perm_eq [seq relabeling_term mu i | i <- bnodes_ts ts1] (bnodes_ts ts2)).
               +  have urt_l : uniq [seq relabeling_term mu i | i <- bnodes_ts ts1] by rewrite (perm_uniq e) //.
                  have urtbs : uniq (get_bs [seq relabeling_term [eta mu] i | i <- bnodes_ts ts1]).
                  by rewrite -undup_get_bsC // undup_uniq.
                  have mem_eq_rt : get_bs [seq relabeling_term [eta mu] i | i <- bnodes_ts ts1] =i get_bs (bnodes_ts ts2).
                  by move=> x; rewrite -!bnode_memP; apply perm_mem.
                  by rewrite uniq_perm //.
               + apply /eqP; rewrite eq_sym; apply /eqP.
                 suffices contra:  perm_eq (get_bs [seq relabeling_term mu i | i <- bnodes_ts ts1]) (get_bs (bnodes_ts ts2)) -> perm_eq [seq relabeling_term mu i | i <- bnodes_ts ts1] (bnodes_ts ts2).
                 by apply (contra_notF contra); rewrite e.

                 move=> contr; apply uniq_perm=> //.
                 by rewrite -(all_bnodes_uniq_bs (map_rel_bnode mu (all_bnodes_ts ts1))) // (perm_uniq contr).
                 have alb := map_rel_bnode mu (all_bnodes_ts ts1).
                 move=> [] //= b ; rewrite ?i_in_bnodes_ts ?l_in_bnodes_ts.
                 have F: Iri b \in [seq relabeling_term mu i | i <- bnodes_ts ts1] -> negb (all (is_bnode (L:=L)) [seq relabeling_term mu i | i <- bnodes_ts ts1]).
                 by move=> contra2; apply /allPn; exists (Iri b).
                 by apply (contra_notF F); rewrite alb.
                 have F: Lit b \in [seq relabeling_term mu i | i <- bnodes_ts ts1] -> negb (all (is_bnode (L:=L)) [seq relabeling_term mu i | i <- bnodes_ts ts1]).
                 by move=> contra2; apply /allPn; exists (Lit b).
                 apply (contra_notF F); rewrite alb //.
                 by rewrite !bnode_memP (perm_mem contr).
        Qed.

        Lemma perm_relabel_bts ts1 ts2 mu :
          perm_eq (map (relabeling_term mu) (bnodes_ts ts1)) (bnodes_ts ts2) =
            perm_eq (map mu (get_bts ts1)) (get_bts ts2).
        Proof. by rewrite perm_relabel_bnodes_ts. Qed.

        Lemma perm_eq_bnodes_relabel ts1 ts2 mu :
          perm_eq (get_bs (bnodes_ts (relabeling_seq_triple mu ts1))) (get_bs (bnodes_ts ts2)) ->
          perm_eq (undup [seq mu i | i <- get_bs (bnodes_ts ts1)]) (get_bs (bnodes_ts ts2)).
        Proof. move=> /perm_mem peqb; apply (uniq_perm (undup_uniq _))=> // x; rewrite -peqb{peqb ts2} mem_undup.
               elim: ts1=> [//| h t IHts].
               rewrite !bnodes_ts_cons -!undup_get_bs mem_undup -mem_map_undup -!get_bs_cat map_cat !mem_cat /= IHts; f_equal.
               case: h=> [[]]// a []// b []// c ? ?; rewrite /bnodes_triple/terms_triple ?filter_undup //.
               have ->:  [seq x <- [:: relabeling_term mu (Bnode a); relabeling_term mu (Iri b);
                              relabeling_term mu (Bnode c)]
                         | is_bnode x] = [:: (Bnode (mu a)); (Bnode (mu c))].
               by [].
               by rewrite -!undup_get_bs -mem_map_undup mem_undup.
        Qed.

        Lemma perm_eq_bts_relabel ts1 ts2 mu :
          perm_eq (get_bts (relabeling_seq_triple mu ts1)) (get_bts ts2) ->
          perm_eq (undup [seq mu i | i <- get_bts ts1]) (get_bts ts2).
        Proof. by apply perm_eq_bnodes_relabel. Qed.

        Lemma perm_eq_bnodes_relabel_inj_in ts1 ts2 mu :
          {in (get_bs (bnodes_ts ts1))&, injective mu} ->
          perm_eq (get_bs (bnodes_ts (relabeling_seq_triple mu ts1))) (get_bs (bnodes_ts ts2)) ->
          perm_eq [seq mu i | i <- get_bs (bnodes_ts ts1)] (get_bs (bnodes_ts ts2)).
        Proof. by move=> inj /perm_eq_bnodes_relabel/perm_undup_map_inj ->. Qed.

        Lemma perm_eq_bts_relabel_inj_in ts1 ts2 mu :
          {in (get_bts ts1)&, injective mu} ->
          perm_eq (get_bts (relabeling_seq_triple mu ts1)) (get_bts ts2) ->
          perm_eq [seq mu i | i <- get_bts ts1] (get_bts ts2).
        Proof. by apply perm_eq_bnodes_relabel_inj_in. Qed.

        Lemma relabeling_term_inj_terms_ts {B2 : eqType} (mu : B -> B2) ts sx sy :
          {in get_bts ts &, injective mu} ->
          sx \in terms_ts ts -> sy \in terms_ts ts ->
                                  relabeling_term mu sx = relabeling_term mu sy ->
                                  sx = sy.
        Proof. case sx; case sy=> /= // bx b_y mu_inj memx memy.
               by move=> [->].
               by move=> [->].
               by move=> [/mu_inj]-> //; rewrite -!bnode_memP !bterms_ts.
        Qed.

        Lemma inj_get_bts_inj_ts {B2: eqType} ts (mu : B -> B2) :
          {in get_bts ts &, injective mu} ->
            {in ts &, injective (relabeling_triple mu)}.
        Proof.
          move=> mu_inj; case=> sx ps ox ? ?; case=> sy py oy ? ? /= /mem_triple_terms_ts /= /and3P[memsx mempx memox] /mem_triple_terms_ts /= /and3P[memsy mempy memoy] [] eqs eqp eqo.
          by apply triple_inj=> /=; apply (relabeling_term_inj_terms_ts mu_inj)=> //.
        Qed.

        Lemma can_bts_can_rtbs ts (mu nu: B -> B) :
          {in get_bts ts, nu \o mu =1 id} ->
            {in ts, [eta relabeling_triple (nu \o mu)] =1 id}.
        Proof. by apply can_bs_can_rtbs. Qed.


      End Bnodes_ts.

      Section Rdf_terms.

        Definition terms {i b l : eqType} (g : rdf_graph i b l) : seq (term i b l) :=
          undup (flatten (map (@terms_triple i b l) (graph g))).

        Lemma terms_graph {i b l: eqType} (g : rdf_graph i b l) :
          terms g = terms_ts (graph g).
        Proof. by case g. Qed.

        Lemma undup_terms g : undup (terms g) = (terms g).
        Proof. by rewrite terms_graph undup_terms_ts. Qed.

        Lemma uniq_terms {i b l : eqType} (g : rdf_graph i b l) : uniq (terms g).
        Proof. by apply undup_uniq. Qed.
        Hint Resolve uniq_terms.

        Lemma terms_cons {i b l : eqType} (trpl : triple i b l)
          (ts : seq (triple i b l)) (us : uniq (trpl :: ts)) :
          terms (mkRdfGraph us) = undup (terms_triple trpl ++ (terms (mkRdfGraph (uniq_tail us)))).
        Proof. by rewrite !terms_graph terms_ts_cons. Qed.

        Lemma mem_triple_terms t g: t \in g -> [&& (subject t) \in (terms g),
              ((predicate t) \in (terms g)) & ((object t) \in terms g)].
        Proof. by rewrite terms_graph; apply mem_triple_terms_ts. Qed.


      End Rdf_terms.

    Section TermRelabeling.
      Variable B1 B2: eqType.

      Lemma terms_relabeled_mem (g : rdf_graph I B1 L) (mu: B1 -> B2) :
        forall us,
        @terms I B2 L (@relabeling B1 B2 mu g us) =i map (relabeling_term mu) (terms g).
      Proof. by move=> ? x; rewrite !terms_graph terms_ts_relabeled_mem. Qed.

      Lemma terms_relabeled (g : rdf_graph I B1 L) (mu: B1 -> B2) (inj_mu : injective mu):
        forall us,
          @terms I B2 L (@relabeling B1 B2 mu g us) = map (relabeling_term mu) (terms g).
      Proof. by move=> /= us; rewrite !terms_graph terms_ts_relabeled. Qed.

    End TermRelabeling.

    Definition bnodes (i b l : eqType) (g : rdf_graph i b l) : seq (term i b l) :=
      bnodes_ts (graph g).

    Remark undup_bnodes g : undup (bnodes g) = bnodes g.
    Proof. exact: undup_idem. Qed.

    Lemma all_bnodes g : all (@is_bnode I B L) (bnodes g).
    Proof. by rewrite all_bnodes_ts. Qed.

    Lemma in_bnodes b g: b \in bnodes g -> is_bnode b.
    Proof. apply /allP. apply all_bnodes. Qed.

    Lemma b_in_bnode_is_bnode b g : bnodes g = [:: b] -> is_bnode b.
    Proof.
      move=> H; have : b \in bnodes g by rewrite H in_cons in_nil eq_refl.
      by apply in_bnodes.
    Qed.

    Lemma bnodes_cons (trpl : triple I B L) (ts : seq (triple I B L)) :
      forall us : uniq (trpl :: ts),
        bnodes {| graph := trpl :: ts; ugraph := us |} = undup ((bnodes_triple trpl) ++ (bnodes {| graph := ts; ugraph := uniq_tail us |})).
    Proof. by rewrite /bnodes/= bnodes_ts_cons. Qed.

    Lemma uniq_bnodes g : uniq (bnodes g).
    Proof. exact: undup_uniq. Qed.
    Hint Resolve uniq_bnodes.

    Lemma i_in_bnodes id g: Iri id \in bnodes g = false.
    Proof. by rewrite /bnodes i_in_bnodes_ts. Qed.

    Lemma l_in_bnodes l g: Lit l \in bnodes g = false.
    Proof. by rewrite /bnodes l_in_bnodes_ts. Qed.

    Section BnodeRelabeling.
      Variable B1 B2: eqType.

      Lemma bnodes_relabel_mem (g: rdf_graph I B1 L) (mu: B1 -> B2) :
        forall us,
        bnodes (@relabeling B1 B2 mu g us) =i (map (relabeling_term mu) (bnodes g)).
      Proof. by move=> ? x; rewrite bnodes_ts_relabel_mem. Qed.

      Lemma bnodes_relabel (g: rdf_graph I B1 L) (mu: B1 -> B2) (inj_mu : injective mu):
        forall us,
          bnodes (@relabeling B1 B2 mu g us) = (map (relabeling_term mu) (bnodes g)).
      Proof. by rewrite /bnodes /= bnodes_ts_relabel_inj. Qed.

      Lemma bterms b g: Bnode b \in (terms g) -> Bnode b \in (bnodes g).
      Proof. by rewrite terms_graph; apply bterms_ts. Qed.

    End BnodeRelabeling.
    End Terms_ts.

    Definition get_b g : seq B :=
      get_bts g.

    Lemma relabeling_term_inj_terms {B2 : eqType} (mu : B -> B2) g sx sy :
      {in get_b g &, injective mu} ->
      sx \in terms g ->
      sy \in terms g ->
        relabeling_term mu sx = relabeling_term mu sy -> sx = sy.
    Proof. apply relabeling_term_inj_terms_ts. Qed.

    Lemma uniq_get_b g : uniq (get_b g).
    Proof. by rewrite /get_b uniq_get_bs. Qed.
    Hint Resolve uniq_get_b.

    Lemma bnodes_map_get_b g : bnodes g = map (fun b=> Bnode b) (get_b g).
    Proof. by rewrite /bnodes -bnodes_map_get_bs. Qed.

    Lemma perm_relabel_bnodes g1 g2 mu :
      perm_eq (map (relabeling_term mu) (bnodes g1)) (bnodes g2) =
        perm_eq (map mu (get_b g1)) (get_b g2).
    Proof. by rewrite perm_relabel_bnodes_ts. Qed.

    Lemma inj_get_b_inj_g {B2: eqType} g (mu : B -> B2) :
      {in get_b g &, injective mu} ->
        {in g &, injective (relabeling_triple mu)}.
    Proof.
      move=> mu_inj; case=> sx ps ox ? ?; case=> sy py oy ? ? /= /mem_triple_terms /= /and3P[memsx mempx memox] /mem_triple_terms /= /and3P[memsy mempy memoy] [] eqs eqp eqo.
        by apply triple_inj=> /=; apply (relabeling_term_inj_terms mu_inj)=> //.
    Qed.

    Lemma map_comp_in_id_ts ts (mu nu: B -> B) :
      [seq (nu \o mu) i | i <- get_bts ts] = get_bts ts ->
        {in (get_bts ts), nu \o mu =1 id}.
    Proof. elim: (get_bts ts)=> [| h t IHtl]; first by move=> _ x; rewrite in_nil //.
           move=> [heq teq] x; rewrite in_cons; case e: (x == h)=> /=.
           + by move: e=> /eqP ->; rewrite heq.
           + apply IHtl; apply teq.
    Qed.

    Lemma map_comp_in_id g (mu nu: B -> B) :
      [seq (nu \o mu) i | i <- get_b g] = get_b g ->
        {in (get_b g), nu \o mu =1 id}.
    Proof. apply map_comp_in_id_ts. Qed.

    Lemma bterm_eq_mem_get_b (b: B) g :
      (@Bnode I B L b) \in terms g ->
                           b \in get_b g.
    Proof. by rewrite terms_graph/get_b; apply bterm_eq_mem_get_bs. Qed.

    Lemma mem_g_mem_triple_b t g b :
      t \in g -> Bnode b \in bnodes_triple t -> b \in get_b g.
    Proof. by apply mem_ts_mem_triple_bs. Qed.

    Lemma can_b_can_rtb g (mu nu: B -> B) :
      {in get_b g, nu \o mu =1 id} ->
        {in g, [eta relabeling_triple (nu \o mu)] =1 id}.
    Proof. by apply can_bs_can_rtbs. Qed.

    Remark id_bij T: bijective (@id T). Proof. by exists id. Qed.
    Hint Resolve id_bij.

    Section Isomorphism.
      Hint Resolve uniq_get_bts.
      Hint Resolve uniq_bnodes_ts.
      Hint Resolve uniq_get_bs.

      Section PreIsomorphism.

        Definition bnode_map_bij (dom cod : seq B) (mu : B -> B) :=
          [&& uniq dom, uniq cod & perm_eq (map mu dom) cod].

        Definition is_pre_iso_ts ts1 ts2 (mu : B -> B) :=
          bnode_map_bij (get_bts ts1) (get_bts ts2) mu.

        Definition is_pre_iso g1 g2 (mu : B -> B) :=
          is_pre_iso_ts g1 g2 mu.

        Lemma is_pre_iso_ts_trans ts1 ts2 ts3 m12 m23 :
          is_pre_iso_ts ts1 ts2 m12 -> is_pre_iso_ts ts2 ts3 m23 -> is_pre_iso_ts ts1 ts3 (m23 \o m12).
        Proof. rewrite /is_pre_iso_ts=> /and3P[_ _ /(perm_map m23)]; rewrite -map_comp=> pe12 /and3P[_ _ pe23].
               by apply /and3P; split=> //; apply: perm_trans pe12 pe23.
        Qed.

        Lemma is_pre_iso_trans g1 g2 g3 m12 m23 :
          is_pre_iso g1 g2 m12 -> is_pre_iso g2 g3 m23 -> is_pre_iso g1 g3 (m23 \o m12).
        Proof. by apply is_pre_iso_ts_trans. Qed.

        Remark is_pre_iso_ts_trans_sym ts1 ts2 m12 m23 :
          is_pre_iso_ts ts1 ts2 m12 -> is_pre_iso_ts ts2 ts1 m23 -> is_pre_iso_ts ts1 ts1 (m23 \o m12).
        Proof. by apply is_pre_iso_ts_trans. Qed.

        Remark is_pre_iso_trans_sym g1 g2 m12 m23 :
          is_pre_iso g1 g2 m12 -> is_pre_iso g2 g1 m23 -> is_pre_iso g1 g1 (m23 \o m12).
        Proof. by apply is_pre_iso_ts_trans_sym. Qed.

        Definition pre_iso_ts ts1 ts2 := exists (mu : B -> B), is_pre_iso_ts ts1 ts2 mu.
        Definition pre_iso g1 g2 := exists (mu : B -> B), is_pre_iso_ts g1 g2 mu.

        Lemma pre_iso_ts_refl ts : pre_iso_ts ts ts.
        Proof. by rewrite /pre_iso_ts /is_pre_iso_ts; exists id; rewrite /bnode_map_bij !uniq_get_bts map_id perm_refl. Qed.

        Lemma pre_iso_refl g : pre_iso g g.
        Proof. by apply pre_iso_ts_refl. Qed.

        Lemma is_pre_iso_ts_inv ts1 ts2 mu :
          is_pre_iso_ts ts1 ts2 mu ->
            exists nu, is_pre_iso_ts ts2 ts1 nu /\
                    map (nu \o mu) (get_bts ts1) = get_bts ts1.
        Proof.
        wlog dflt :/ B.
          move=> hwlog; rewrite /is_pre_iso_ts/get_b/bnode_map_bij.
          case_eq (get_bts ts2) => [e |dflt l <-]; last by apply: hwlog.
          rewrite !uniq_get_bts /=.
          by move/perm_nilP/eqP; rewrite -size_eq0 size_map size_eq0; move/eqP->; exists id.
        rewrite /is_pre_iso_ts => /and3P[_ _ mu_pre_iso].
        wlog map_mu:  mu {mu_pre_iso} / [seq mu i | i <- get_bts ts1] = get_bts ts2.
          move=> hwlog.
          have [rho rhoP] := map_of_seq [seq mu i | i <- get_bts ts1] (get_bts ts2) dflt.
          have {rhoP} rhoP : [seq (rho \o mu) i | i <- get_bts ts1] = get_bts ts2.
          rewrite -map_comp in rhoP; apply: rhoP; first by rewrite (perm_uniq mu_pre_iso).
            by rewrite (perm_size mu_pre_iso).
          have [tau [/and3P[_ _ tauP1] tauP2]] := hwlog _ rhoP.
          exists (tau \o rho); split=> //.
          rewrite /bnode_map_bij perm_sym !uniq_get_bts -tauP2 /=.
          have:=  (perm_map (tau \o rho) mu_pre_iso).
          by rewrite -map_comp.
        have [nu nuP] := map_of_seq (get_bts ts2) (get_bts ts1) dflt.
        have  {nuP} nuP : [seq nu i | i <- get_bts ts2] = get_bts ts1.
          by apply: nuP=> //; rewrite -map_mu size_map.
        exists nu; split=> //.
        - rewrite /bnode_map_bij !uniq_get_bts nuP; exact: perm_refl.
        by rewrite map_comp map_mu.
        Qed.

        Lemma is_pre_iso_inv g1 g2 mu : is_pre_iso g1 g2 mu ->
                              exists nu, is_pre_iso g2 g1 nu /\
                               map (nu \o mu) (get_bts g1) = get_bts g1.
        Proof. by apply is_pre_iso_ts_inv. Qed.

        Lemma pre_iso_ts_sym ts1 ts2 : pre_iso_ts ts1 ts2 <-> pre_iso_ts ts2 ts1.
        Proof. suffices imp h1 h2 : pre_iso_ts h1 h2 -> pre_iso_ts h2 h1 by split; exact: imp.
               by rewrite /pre_iso=> [[mu /is_pre_iso_ts_inv [nu [inv _]]]]; exists nu.
        Qed.

        Lemma pre_iso_sym g1 g2 : pre_iso g1 g2 <-> pre_iso g2 g1.
        Proof. by apply pre_iso_ts_sym. Qed.

        Lemma pre_iso_ts_trans ts1 ts2 ts3 :
          pre_iso_ts ts1 ts2 -> pre_iso_ts ts2 ts3 -> pre_iso_ts ts1 ts3.
        Proof. rewrite /pre_iso=> [[mu12 iso12] [mu23 iso23]].
               by exists (mu23 \o mu12); apply (is_pre_iso_ts_trans iso12 iso23).
        Qed.

        Lemma pre_iso_trans g1 g2 g3 :
          pre_iso g1 g2 -> pre_iso g2 g3 -> pre_iso g1 g3.
        Proof. by apply pre_iso_ts_trans. Qed.

        Lemma is_pre_iso_ts_inj ts1 ts2 mu :
          is_pre_iso_ts ts1 ts2 mu -> {in get_bts ts1 &, injective mu}.
        Proof.
        move=> /and3P[_ _ hmu] b b' hb1 hb'.
        apply: contra_eq => neqb.
        apply/negP=> eqmu.
        have test : perm_eq (get_bts ts1)  (b' :: rem b' (get_bts ts1)).
          by apply: perm_to_rem.
        have {test} /(perm_map mu) /= test : perm_eq (get_bts ts1)  (b' :: b :: rem b (rem b' (get_bts ts1))).
          apply: perm_trans test _. rewrite perm_cons. apply: perm_to_rem.
          by rewrite mem_rem_uniq // inE neqb.
        have hcount : 2 <= count_mem (mu b) (map mu (get_bts ts1)).
          by move/permP: test->; rewrite /= (eqP eqmu) !eqxx.
        have {hcount} : 2 <= count_mem (mu b) (get_bts ts2).
          by move/permP: hmu <-.
        by rewrite count_uniq_mem //; case: (mu b \in get_bts ts2).
        Qed.

        Lemma is_pre_iso_ts_inj2 ts1 ts2 mu :
          is_pre_iso_ts ts1 ts2 mu -> {in get_bts ts1 &, injective mu}.
        Proof. by move=> /and3P[_ _] /perm_uniq equniq; apply/(in_map_injP); rewrite // equniq. Qed.

        Lemma is_pre_iso_inj g1 g2 mu :
          is_pre_iso g1 g2 mu -> {in get_b g1 &, injective mu}.
        Proof. by apply is_pre_iso_ts_inj. Qed.

        Lemma is_pre_iso_ts_bnodes_inj ts1 ts2 mu :
          is_pre_iso_ts ts1 ts2 mu -> {in bnodes_ts ts1 &, injective (relabeling_term mu)}.
        Proof. move=> /is_pre_iso_ts_inj hmu []b // []b' //=;
               rewrite bnodes_map_get_bs !mem_map // => hb1 hb' []=> eq; rewrite ?eq //.
               by congr Bnode; apply hmu.
        Qed.

        Lemma is_pre_iso_bnodes_inj g1 g2 mu :
          is_pre_iso g1 g2 mu -> {in bnodes g1 &, injective (relabeling_term mu)}.
        Proof. by apply is_pre_iso_ts_bnodes_inj. Qed.

        Lemma uniq_relabeling_pre_iso mu (ts : seq (triple I B L)):
          uniq ts ->
          is_pre_iso_ts ts (relabeling_seq_triple mu ts) mu ->
            uniq (relabeling_seq_triple mu ts).
        Proof. by rewrite /is_pre_iso_ts=> uts /is_pre_iso_ts_inj/inj_get_bts_inj_ts ?; rewrite map_inj_in_uniq //. Qed.

      End PreIsomorphism.


      Definition is_effective_iso_ts ts1 ts2 mu :=
       [&& is_pre_iso_ts ts1 ts2 mu,
          uniq (relabeling_seq_triple mu ts1) &
            perm_eq (relabeling_seq_triple mu ts1) ts2].

      Definition is_iso_ts ts1 ts2 mu :=
        is_effective_iso_ts ts1 ts2 mu /\
          (forall t, forall wf_s wf_p, @mkTriple I B L (relabeling_term mu (subject t)) (predicate t) (relabeling_term mu (object t)) wf_s wf_p \in ts2 -> t \in ts1).

      Definition is_iso g1 g2 mu : Prop :=
        is_iso_ts g1 g2 mu.
      (*   [&& is_pre_iso g1 g2 mu, *)
      (*     uniq (relabeling_seq_triple mu g1) & *)
      (*       perm_eq (relabeling_seq_triple mu g1) g2] /\ *)
      (*     (forall t, forall wf_s wf_p, @mkTriple I B L (relabeling_term mu (subject t)) (predicate t) (relabeling_term mu (object t)) wf_s wf_p \in g2 -> t \in g1). *)


      Definition effective_iso_ts ts1 ts2 := exists mu, @is_effective_iso_ts ts1 ts2 mu.
      Definition iso_ts ts1 ts2 := exists mu, @is_iso_ts ts1 ts2 mu.
      Definition effective_iso g1 g2 := effective_iso_ts g1 g2.
      Definition iso g1 g2 := iso_ts g1 g2.

      Remark is_iso_effective_is_pre_iso ts1 ts2 mu: is_effective_iso_ts ts1 ts2 mu -> is_pre_iso_ts ts1 ts2 mu.
      Proof. by move=> /and3P[piso]. Qed.

      Remark is_iso_is_pre_iso g1 g2 mu: is_iso g1 g2 mu -> is_pre_iso g1 g2 mu.
      Proof. move=> [/is_iso_effective_is_pre_iso //]. Qed.

      Definition effective_iso_ts_refl ts : uniq ts -> is_effective_iso_ts ts ts id.
      Proof.
      move=> uts.
      rewrite /is_effective_iso_ts/is_pre_iso_ts/bnode_map_bij.
      by rewrite uniq_get_bts! relabeling_seq_triple_id /= uts /is_pre_iso/is_pre_iso_ts map_id !perm_refl.
      Qed.

      Definition iso_refl g : iso g g.
      Proof. exists id. split; first by case: g; apply effective_iso_ts_refl.
             + move=> t wfs wfp.
               suffices -> : {|
                               subject := relabeling_term id (subject t);
                               predicate := predicate t;
                               object := relabeling_term id (object t);
                               subject_in_IB := wfs;
                               predicate_in_I := wfp
                             |} = t. done.
               by apply triple_inj; rewrite //= relabeling_term_id.
      Qed.

      Section eqb_rdf_perm_eq.
        (* TODO find a place for these lemmas *)

        Lemma peq_terms ts1 ts2 :
          perm_eq ts1 ts2 -> perm_eq (terms_ts ts1) (terms_ts ts2).
        Proof. rewrite /eqb_rdf/terms=> peq.
               by rewrite perm_undup //; apply perm_mem; rewrite perm_flatten //; apply: perm_map peq.
        Qed.

        Lemma eqb_rdf_terms g1 g2 :
          eqb_rdf g1 g2 -> perm_eq (terms g1) (terms g2).
        Proof. by apply peq_terms. Qed.

        Lemma peq_bnodes ts1 ts2 :
          perm_eq ts1 ts2 -> perm_eq (bnodes_ts ts1) (bnodes_ts ts2).
        Proof. move=> /peq_terms eqb.
               by rewrite /bnodes perm_undup //; apply: perm_mem; apply: perm_filter.
        Qed.

        Lemma eqb_rdf_bnodes g1 g2 :
          eqb_rdf g1 g2 -> perm_eq (bnodes g1) (bnodes g2).
        Proof. by apply peq_bnodes. Qed.

        Lemma peq_get_bts ts1 ts2 :
          perm_eq ts1 ts2 -> perm_eq (get_bts ts1) (get_bts ts2).
        Proof. by move=> /peq_bnodes eqb ; apply: perm_pmap eqb. Qed.

        Lemma eqb_rdf_get_b g1 g2 :
          eqb_rdf g1 g2 -> perm_eq (get_b g1) (get_b g2).
        Proof. by move=> /peq_bnodes eqb ; apply: perm_pmap eqb. Qed.

        Lemma peq_get_bts_hom ts1 ts2 mu :
          uniq (relabeling_seq_triple mu ts1) ->
          perm_eq (relabeling_seq_triple mu ts1) ts2 -> perm_eq (undup (map mu (get_bts ts1))) (get_bts ts2).
        Proof. by move=> us /peq_get_bts eqb ; rewrite (perm_eq_bnodes_relabel eqb). Qed.

        Lemma eqb_rdf_get_b_hom g1 g2 mu us :
          eqb_rdf (@relabeling _ _ mu g1 us) g2 -> perm_eq (undup (map mu (get_b g1))) (get_b g2).
        Proof. by apply peq_get_bts_hom. Qed.

      End eqb_rdf_perm_eq.

      Remark eq_effective_iso_ts ts1 ts2 (u1 : uniq ts1) : perm_eq ts1 ts2 -> is_effective_iso_ts ts1 ts2 id.
      Proof.
      have usid: uniq (relabeling_seq_triple id ts1) by rewrite relabeling_seq_triple_id.
      rewrite /is_iso_ts/is_effective_iso_ts usid /is_pre_iso_ts/bnode_map_bij.
      rewrite map_id relabeling_seq_triple_id /= !uniq_get_bts /=.
      by rewrite andbC=> peq; rewrite peq /=; exact: peq_get_bts.
      Qed.

      Remark eqiso_ts ts1 ts2 (u1 : uniq ts1) : perm_eq ts1 ts2 -> iso_ts ts1 ts2.
      Proof.
        exists id; split; first by apply eq_effective_iso_ts.
        + move=> t wfs wfp.
          suffices -> : {|
                          subject := relabeling_term id (subject t);
                          predicate := predicate t;
                          object := relabeling_term id (object t);
                          subject_in_IB := wfs;
                          predicate_in_I := wfp
                        |} = t. by rewrite (perm_mem H).
          by apply triple_inj; rewrite //= relabeling_term_id.
      Qed.

      Remark eqiso g1 g2 : eqb_rdf g1 g2 -> iso g1 g2.
      Proof. by apply : eqiso_ts (uniq_rdf_graph _). Qed.

      Lemma projs_rel (t : triple I B L) (B2 : Type) (mu : B -> B2) :
        (subject (relabeling_triple mu t)) = relabeling_term mu (subject t).
      Proof. by case:t. Qed.

      Lemma projp_rel (t : triple I B L) (B2 : Type) (mu : B -> B2) :
        (predicate (relabeling_triple mu t)) = relabeling_term mu (predicate t).
      Proof. by case:t. Qed.

      Lemma projo_rel (t : triple I B L) (B2 : Type) (mu : B -> B2) :
        (object (relabeling_triple mu t)) = relabeling_term mu (object t).
      Proof. by case:t. Qed.

      Lemma pred_relab (t : triple I B L) (mu : B -> B) :
        predicate (relabeling_triple mu t) = predicate t.
      Proof. by case: t=> ? [] ? //. Qed.

      Lemma not_perm_eq (T : eqType) (s1 s2: seq T) :
        uniq s1 -> uniq s2 -> size s1 = size s2 -> negb (perm_eq s1 s2) -> exists (t : T), (t \in s1) && (t \notin s2).
      Proof.
        move=> us1 us2 eqsize nperm.
        suff : ~~ all (mem s2) s1 by case/allPn=> x s1x s2x; exists x; rewrite s1x.
        apply: contra nperm => s21; apply: uniq_perm=> //.
        have sub12 : {subset s1 <= s2} by move=> x /(allP s21).
        have leqs21 : size s2 <= size s1 by rewrite eqsize.
        by case: (uniq_min_size us1 sub12 leqs21).
      Qed.

      Lemma effective_iso_ts_sym ts1 ts2 (u1 : uniq ts1) : effective_iso_ts ts1 ts2 -> effective_iso_ts ts2 ts1.
      Proof.
        suffices imp h1 h2 : uniq h1 -> effective_iso_ts h1 h2 -> effective_iso_ts h2 h1. by apply imp.
        move=> uh1; case=> mu /and3P[pre_iso_mu uniq_relab perm_relab].
        move:(is_pre_iso_ts_inv pre_iso_mu); rewrite /pre_iso/is_pre_iso; move=> [nu [pre_iso_nu /map_comp_in_id_ts/can_bs_can_rtbs nuP]].
        exists nu.
        suffices /(perm_eq_relab_uniq_ts uh1) [peq urel] : perm_eq (relabeling_seq_triple nu h2) h1.
          by apply /and3P; split=> //.
        move: perm_relab; rewrite perm_sym=> /(perm_map (relabeling_triple nu))=> perm_relab.
        by apply: perm_trans perm_relab _; rewrite relabeling_triple_map_comp map_id_in //.
      Qed.

      Lemma effective_iso_outside_eq_inv G H (uG : uniq G):
          forall mu,
            is_pre_iso_ts G H mu ->
          forall (nu : B -> B), (is_pre_iso_ts H G nu /\ [seq (nu \o mu) i | i <- get_bts G] = get_bts G) ->
          exists rho, is_pre_iso_ts H G rho /\
                        (forall b : B, rho b \in get_bts G -> b \in get_bts H) /\
                        {in (get_bts H), nu =1 rho}.
      Proof.
        move=> mu pre_iso_mu.
        rewrite /iso_ts/is_iso/is_iso_ts=> nu [pre_iso_nu /map_comp_in_id_ts mu_inv].
        move: pre_iso_mu => /and3P[_ _ pre_iso_mu].
        case_eq (perm_eq (get_bts H) (get_bts G)).
        + set rho := (fun b => if (b \in (get_bts H)) then nu b else b).
          have eq1_nu_rho : {in (get_bts H), nu =1 rho} by rewrite /rho => b ->.
          move=> peq_bnodes; exists rho; split; last first.
          - split=> //; rewrite /rho=> b.
            case_eq (b \in get_bts H)=> //.
            by rewrite (perm_mem peq_bnodes)=> ->.
          - rewrite /is_pre_iso_ts/bnode_map_bij.
            by move/eq_in_map : eq1_nu_rho=> <-.
        + move=> not_peq.
          suffices  [b0 /andP[bin_H bnin_G]] : exists b, (b \in (get_bts H)) && (negb (b \in (get_bts G))).
            set rho := (fun b => if (b \in (get_bts H)) then nu b else b0).
            have eq1_nu_rho : {in (get_bts H), nu =1 rho} by rewrite /rho=> b ->.
            exists rho; split=> //; last first.
            - split=> //; rewrite /rho=> b.
              case_eq (b \in get_bts H)=> //.
              by move=> _; apply contraTT.
            - rewrite /is_pre_iso_ts/bnode_map_bij.
              by move/eq_in_map : eq1_nu_rho=> <-.
          apply: not_perm_eq=> //.
          + by move: pre_iso_mu=> /perm_size <-; rewrite size_map.
          + by rewrite not_peq.
      Qed.

      Lemma effective_iso_outside_domain G H (uG : uniq G) :
        effective_iso_ts G H ->
          exists rho : B -> B,
            is_effective_iso_ts H G rho /\
              forall b, rho b \in (get_bts G) -> b \in get_bts H.
      Proof.
        case=> mu /and3P[pre_iso_mu uniq_relab perm_relab].
        rewrite /iso_ts/is_iso/is_iso_ts.
        move:(is_pre_iso_ts_inv pre_iso_mu); rewrite /pre_iso/is_pre_iso; move=> [nu [pre_iso_nu eq]].
        rewrite /is_pre_iso_ts/bnode_map_bij in pre_iso_mu.
        suffices [rho [piso_rho [rho_part eq1_rho_nu]]]: exists rho, is_pre_iso_ts H G rho /\
                                  (forall b : B, rho b \in get_bts G -> b \in get_bts H) /\
                                 {in (get_bts H), nu =1 rho}.
          suffices /perm_eq_relab_uniq_ts step : perm_eq (relabeling_seq_triple rho H) G.
            move : step=> /(_ uG) [peq_rho urho].
            by exists rho; split=> //; apply/and3P; rewrite piso_rho peq_rho urho.
          move: perm_relab; rewrite perm_sym=> /(perm_map (relabeling_triple rho))=> perm_relab.
          apply: perm_trans perm_relab _; rewrite relabeling_triple_map_comp map_id_in //.
          move: eq=> /map_comp_in_id_ts mu_inv.
          suffices : {in (get_bts G), (rho \o mu) =1 (nu \o mu)}.
            move=> eq1_rhomu_numu /= t tin; apply triple_inj.
            + rewrite projs_rel; move: t tin; case=> [[]]s p o sib pii //=.
              suffices bin : Bnode s \in bnodes_triple  {| subject := Bnode s; predicate := p; object := o; subject_in_IB := sib; predicate_in_I := pii |}.
                move=> /mem_ts_mem_triple_bts /(_ bin) sin.
                congr Bnode.
                rewrite /comp in eq1_rhomu_numu mu_inv.
                by rewrite eq1_rhomu_numu // mu_inv.
              by rewrite /bnodes_triple/terms_triple filter_undup mem_undup in_cons eqxx.
            + by rewrite projp_rel; move: t tin; case=> [[]]s []p o sib pii.
            + rewrite projo_rel; move: t tin; case=> s p []o sib pii //=.
              suffices bin : Bnode o \in bnodes_triple {| subject := s; predicate := p; object := Bnode o; subject_in_IB := sib; predicate_in_I := pii |}.
                move=> /mem_ts_mem_triple_bts /(_ bin) sin.
                congr Bnode. rewrite /comp in eq1_rhomu_numu mu_inv.
                by rewrite eq1_rhomu_numu // mu_inv.
              by rewrite /bnodes_triple/terms_triple filter_undup mem_undup -mem_rev -filter_rev in_cons eqxx.
          move=> b bin.
          suffices mub_inH : mu b \in get_bts H.
            by rewrite /= -eq1_rho_nu // mu_inv.
          move: pre_iso_mu => /and3P[_ _ pre_iso_mu].
          by apply (map_f mu) in bin; rewrite (perm_mem pre_iso_mu) in bin.
        by apply (effective_iso_outside_eq_inv uG pre_iso_mu).
      Qed.

      Lemma effective_iso_ts_iso_inv ts1 ts2 (u1 : uniq ts1) : effective_iso_ts ts1 ts2 -> iso_ts ts2 ts1.
      Proof.
        (* suffices imp G H : uniq G -> iso_ts G H -> iso_ts H G by split; exact: imp. *)
        (* move=> /= uG; *)
        (* move{u2}. *)
               case=> mu /and3P[pre_iso_mu uniq_relab perm_relab].
        rewrite /iso_ts/is_iso/is_iso_ts.
        suffices [rho [/and3P[piso_rho urG peq_rho] mu_part]]: exists rho : B -> B,
                is_effective_iso_ts ts2 ts1 rho /\
                forall b, rho b \in (get_bts ts1) -> b \in get_bts ts2.
          exists rho; split.
          + by apply /and3P.
          + have rho_inj_in := is_pre_iso_ts_inj2 piso_rho.
            move=> t wfs wfp.
            suffices -> : {|
                            subject := relabeling_term rho (subject t);
                            predicate := predicate t;
                                                 object := relabeling_term rho (object t);
                                                           subject_in_IB := wfs;
                                                                            predicate_in_I := wfp
                       |} = relabeling_triple rho t.
              suffices /(_ I L) SH : forall s s', s' \in get_bts ts2 -> Bnode (rho s) = Bnode (rho s') -> s \in get_bts ts2.
                rewrite -(perm_mem peq_rho)=> /mapP/=[t' t'inh2 eqtt' ].
                have /and3P[] := triple_case eqtt'.
                rewrite !projo_rel !projs_rel !projp_rel=> /eqP eqs /eqP eqp /eqP eqo.
                case_eq ((is_bnode (subject t)) || (is_bnode (object t))).
                + move=> /orP[].
                  - case: t t' t'inh2 wfs wfp eqtt' eqo eqs eqp=> //= [[]]s p o sib pii; case=> //= [[]]s' p' o' sib' pii' //= t'inh2 wfs wfp eqtt' eqo eqs eqp.
                    suffices s'inh2 : s' \in (get_bts ts2).
                      have sinh2 := SH s s' s'inh2 eqs.
                      move: eqs=> []/(rho_inj_in _ _ sinh2 s'inh2) eqs.
                      suffices -> : {| subject := Bnode s; predicate := p; object := o; subject_in_IB := sib; predicate_in_I := pii |} = {| subject := Bnode s'; predicate := p'; object := o'; subject_in_IB := sib'; predicate_in_I := pii' |}.
                        by [].
                      apply triple_inj=> //; rewrite eqs //=.
                      + by move: p p' pii pii' eqp t'inh2 eqtt' wfp=> []p []p'.
                      + move: o o' eqo t'inh2 eqtt' wfp=> []o []o' //= eqo t'inh2.
                        suffices o'inh2 : o' \in (get_bts ts2).
                          have oinh2 := SH o o' o'inh2 eqo.
                          by move: eqo=> []/(rho_inj_in _ _ oinh2 o'inh2) eqo _ _; rewrite eqo.
                        suffices bnode_in :  Bnode o' \in bnodes_triple  {|
                                                       subject := Bnode s';
                                                         predicate := p';
                                                         object := Bnode o';
                                                         subject_in_IB := sib';
                                                         predicate_in_I := pii'
                                                       |}.
                          by apply (mem_ts_mem_triple_bts t'inh2 bnode_in).
                        by rewrite /bnodes_triple/terms_triple filter_undup mem_undup -mem_rev -filter_rev /= in_cons eqxx.
                    suffices bnode_in :  Bnode s' \in bnodes_triple  {|
                                                     subject := Bnode s';
                                                       predicate := p';
                                                       object := o';
                                                       subject_in_IB := sib';
                                                       predicate_in_I := pii'
                                                     |}.
                      by apply (mem_ts_mem_triple_bts t'inh2 bnode_in).
                    by rewrite /bnodes_triple/terms_triple filter_undup mem_undup /= in_cons eqxx.
                  - case: t t' t'inh2 wfs wfp eqtt' eqo eqs eqp=> //= s p []o sib pii; case=> //= s' p' []o' sib' pii' //= t'inh2 wfs wfp eqtt' eqo eqs eqp.
                    suffices o'inh2 : o' \in (get_bts ts2).
                      have oinh2 := SH o o' o'inh2 eqo.
                      move: eqo=> []/(rho_inj_in _ _ oinh2 o'inh2) eqo.
                      suffices -> : {| subject := s; predicate := p; object := Bnode o; subject_in_IB := sib; predicate_in_I := pii |} = {| subject := s'; predicate := p'; object := Bnode o'; subject_in_IB := sib'; predicate_in_I := pii' |}.
                        by [].
                      apply triple_inj=> //; rewrite eqo //=; first last.
                      + by move: p p' pii pii' eqp t'inh2 eqtt' wfp=> []p []p'.
                      + move: s s' eqs sib sib' eqtt' wfs t'inh2=> []s []s' //= eqs sib sib' eqtt' wfs t'inh2.
                        suffices s'inh2 : s' \in (get_bts ts2).
                          have sinh2 := SH s s' s'inh2 eqs.
                          by move: eqs=> []/(rho_inj_in _ _ sinh2 s'inh2) ->.
                        suffices bnode_in :  Bnode s' \in bnodes_triple  {|
                                                         subject := Bnode s';
                                                           predicate := p';
                                                           object := Bnode o';
                                                           subject_in_IB := sib';
                                                           predicate_in_I := pii'
                                                         |}.
                          by apply (mem_ts_mem_triple_bts t'inh2 bnode_in).
                        by rewrite /bnodes_triple/terms_triple filter_undup mem_undup in_cons eqxx.
                        suffices bnode_in :  Bnode o' \in bnodes_triple
                                                         {|
                                                                   subject := s';
                                                                   predicate := p';
                                                                   object := Bnode o';
                                                                   subject_in_IB := sib';
                                                                   predicate_in_I := pii'
                                                                 |}.
                          by apply (mem_ts_mem_triple_bts t'inh2 bnode_in).
                        by rewrite /bnodes_triple/terms_triple filter_undup mem_undup -mem_rev -filter_rev /= in_cons eqxx.
                +  rewrite Bool.orb_false_iff.
                   case: t t' t'inh2 wfs wfp eqtt' eqo eqs eqp=> //= [[]]s []p []o sib pii; case=> //= [[]]s' []p' []o' sib' pii' //= t'inh2 wfs wfp eqtt' eqo eqs eqp [] // _ _.
                   suffices -> : {|
                                      subject := Iri s;
                                      predicate := Iri p;
                                      object := Iri o;
                                      subject_in_IB := sib;
                                      predicate_in_I := pii
                               |} = {|
                                      subject := Iri s';
                                      predicate := Iri p';
                                      object := Iri o';
                                      subject_in_IB := sib';
                                      predicate_in_I := pii'
                                    |}.
                      by [].
                    by apply triple_inj.
                    suffices -> : {|
                                      subject := Iri s;
                                      predicate := Iri p;
                                      object := Lit o;
                                      subject_in_IB := sib;
                                      predicate_in_I := pii
                               |} = {|
                                      subject := Iri s';
                                      predicate := Iri p';
                                      object := Lit o';
                                      subject_in_IB := sib';
                                      predicate_in_I := pii'
                                    |}.
                      by [].
                    by apply triple_inj.
              move=> ? ? b b' /(map_f (rho)).
              move: piso_rho=> /and3P[_ _ /perm_mem ->] rho_b'in []eq_rho.
              by move: rho_b'in; rewrite -eq_rho=> /mu_part.
            + apply triple_inj=> //=.
                - by rewrite projs_rel.
                - by rewrite projp_rel; case: (predicate t) wfp.
                - by rewrite projo_rel.
        by apply effective_iso_outside_domain=> //; exists mu; apply /and3P; split=> //.
      Qed.

      Lemma iso_ts_sym ts1 ts2 (u1 : uniq ts1) (u2 : uniq ts2) : iso_ts ts1 ts2 <-> iso_ts ts2 ts1.
      Proof.
        suffices imp G H : uniq G -> iso_ts G H -> iso_ts H G by split; exact: imp.
        move=> uG [mu [eiso] _].
        by apply effective_iso_ts_iso_inv=> //; exists mu.
      Qed.

      Lemma effective_iso_iso ts1 ts2 (u1 : uniq ts1) (u2 : uniq ts2) : effective_iso_ts ts1 ts2 -> iso_ts ts1 ts2.
      Proof. by move=> /(effective_iso_ts_iso_inv u1) /(iso_ts_sym u1 u2). Qed.

      Lemma iso_sym g1 g2 : iso g1 g2 <-> iso g2 g1.
      Proof. by apply: iso_ts_sym (uniq_rdf_graph _) (uniq_rdf_graph _). Qed.

      Lemma eq_mem_in (T : eqType) (s : seq T) (a b : T) : a = b -> a \in s -> b \in s.
      Proof. by move => ->. Qed.


      Lemma effective_iso_ts_trans ts1 ts2 ts3 : effective_iso_ts ts1 ts2 -> effective_iso_ts ts2 ts3 -> effective_iso_ts ts1 ts3.
      Proof.
        rewrite /iso/is_iso; move=> [mu12 /and3P[pre_iso12 urel12 perm12]] [mu23 /and3P[pre_iso23 urel23 perm23]].
        exists (mu23 \o mu12).
        suffices ucomp: uniq (relabeling_seq_triple (mu23 \o mu12) ts1).
        apply /and3P; split=> //.
        + by apply: is_pre_iso_ts_trans pre_iso12 pre_iso23.
        + by apply : perm_eq_comp perm12 perm23.
        + rewrite -relabeling_seq_triple_comp /relabeling_seq_triple.
          have /eq_uniq -> //: size [seq relabeling_triple mu23 i | i <- [seq relabeling_triple mu12 i | i <- ts1]] =
                             size (relabeling_seq_triple mu23 ts2).
          by move: perm12=> /perm_size; rewrite !size_map.
          by apply eq_mem_map; apply perm_mem.
      Qed.

      Lemma iso_ts_trans ts1 ts2 ts3 : iso_ts ts1 ts2 -> iso_ts ts2 ts3 -> iso_ts ts1 ts3.
      Proof. rewrite /iso/is_iso; move=> [mu12 [/and3P[pre_iso12 urel12 perm12] mu12_part]] [mu23 [/and3P[pre_iso23 urel23 perm23] mu23_part]].
             exists (mu23 \o mu12).
             suffices ucomp: uniq (relabeling_seq_triple (mu23 \o mu12) ts1).
             split.
               apply /and3P; split=> //.
               + by apply: is_pre_iso_ts_trans pre_iso12 pre_iso23.
               + by apply : perm_eq_comp perm12 perm23.
               + move=> t wfs wfp tin.
                 move: mu23_part=> /(_ (relabeling_triple mu12 t)).
                 have wfs2 := wfs.
                 rewrite -projs_rel relabeling_triple_comp projs_rel in wfs2.
                 move=> /(_ wfs2).
                 have wfp2 := wfp.
                 have /(_ I L t) /iffLR /(_ wfp2) wfp3 := (relabeling_triple_preserves_is_in_i mu12).
                 move=> /(_ wfp3).
                 suffices -> : {|
     subject := relabeling_term mu23 (subject (relabeling_triple mu12 t));
     predicate := predicate (relabeling_triple mu12 t);
     object := relabeling_term mu23 (object (relabeling_triple mu12 t));
     subject_in_IB := wfs2;
     predicate_in_I := wfp3
   |} = {|
          subject := relabeling_term (mu23 \o mu12) (subject t);
          predicate := predicate t;
          object := relabeling_term (mu23 \o mu12) (object t);
          subject_in_IB := wfs;
          predicate_in_I := wfp
        |}.
                 move=> /(_ tin).
                 move=> tin2.
                 suffices ib : (is_in_ib (relabeling_term mu12 (subject t))).
                 apply (mu12_part _ ib wfp2).
                 suffices -> :  {|
                              subject := relabeling_term mu12 (subject t);
                                         predicate := predicate t;
                                                      object := relabeling_term mu12 (object t);
                                                                subject_in_IB := ib;
                                                                                 predicate_in_I := wfp2
                               |} = relabeling_triple mu12 t.
                 by apply tin2.
                 apply triple_inj=> /=.
               + by rewrite projs_rel.
               + by rewrite projp_rel; case : (predicate t) wfp2=> //.
               + by rewrite projo_rel.
             move: wfs {tin}.
             by rewrite relabeling_term_comp -relabeling_term_preserves_is_in_ib.
                 apply triple_inj=> /=.
               + by rewrite projs_rel relabeling_term_comp.
               + by rewrite projp_rel; case : (predicate t) wfp2=> //.
               + by rewrite projo_rel relabeling_term_comp.
               + rewrite -relabeling_seq_triple_comp /relabeling_seq_triple.
                 have /eq_uniq -> //: size [seq relabeling_triple mu23 i | i <- [seq relabeling_triple mu12 i | i <- ts1]] =
                               size (relabeling_seq_triple mu23 ts2).
                 by move: perm12=> /perm_size; rewrite !size_map.
                 by apply eq_mem_map; apply perm_mem.
      Qed.

      Lemma iso_trans g1 g2 g3 : iso g1 g2 -> iso g2 g3 -> iso g1 g3.
      Proof. by apply iso_ts_trans. Qed.

      (* TODO *)
      Lemma ts_pre_iso_effective_iso ts mu (urel: uniq (relabeling_seq_triple mu ts)) :
        is_pre_iso_ts ts (relabeling_seq_triple mu ts) mu ->
          is_effective_iso_ts ts (relabeling_seq_triple mu ts) mu.
      Proof. by move=> pre_iso; apply/and3P; rewrite pre_iso urel /=. Qed.

      Section Isocanonical.

        Definition effective_isocanonical_mapping (M : rdf_graph I B L -> rdf_graph I B L) :=
          (forall g, effective_iso_ts g (M g)) /\
            (forall g1 g2, eqb_rdf (M g1) (M g2) <-> effective_iso_ts g1 g2).

        Definition isocanonical_mapping (M : rdf_graph I B L -> rdf_graph I B L) :=
          (forall g, iso g (M g)) /\
            (forall g1 g2, eqb_rdf (M g1) (M g2) <-> iso g1 g2).

        Lemma effective_isocanonical_mapping_isocanonical (M : rdf_graph I B L -> rdf_graph I B L) :
          effective_isocanonical_mapping M -> isocanonical_mapping M.
        Proof. move=> [iso_out can].
               split.
               + move=> g.
                 have ug := uniq_rdf_graph g.
                 apply effective_iso_iso=> //.
                 - have [mu /and3P[piso urg peq]] := iso_out g.
                   by rewrite -(perm_uniq peq) urg.
               + move=> g h; split.
                 by move=> /can/(effective_iso_iso (uniq_rdf_graph _) (uniq_rdf_graph _)).
               + by move=> [mu [eiso _]]; apply can; exists mu.
       Qed.

        (* Definition isocanonical_mapping' M := *)
        (*   (forall g, iso g (M g)) /\ *)
        (*     (forall g1 g2, eqb_rdf (M g1) (M g2) <-> iso g1 g2). *)

        Definition mapping_is_effective_iso_mapping (M : rdf_graph I B L -> rdf_graph I B L) := forall g, effective_iso g (M g).
        Definition mapping_is_iso_mapping (M : rdf_graph I B L -> rdf_graph I B L) := forall g, iso g (M g).

        Definition dt_names_mapping (M : rdf_graph I B L -> rdf_graph I B L) := forall g1 g2,
            iso g1 g2 -> eqb_rdf (M g1) (M g2).

        Lemma same_res_impl_effective_iso_mapping M g1 g2 (iso_output : mapping_is_effective_iso_mapping M) :
          eqb_rdf (M g1) (M g2) -> effective_iso_ts g1 g2.
        Proof.
          have isog1k1 : effective_iso g1 (M g1). by apply iso_output.
          have isog2k2 : effective_iso (M g2) g2. apply effective_iso_ts_sym=> //; first by case g2. apply iso_output.
          have umg1 : uniq (M g1). move: isog1k1=> [mu /and3P[piso _ peq ]].
            rewrite -(perm_uniq peq). rewrite map_inj_in_uniq; first by case g1. apply inj_get_b_inj_g. apply (is_pre_iso_inj piso). 
          move=> /(eq_effective_iso_ts umg1) peqm.
          have {}peqm: effective_iso_ts (M g1) (M g2) by exists id.
          apply: (effective_iso_ts_trans (effective_iso_ts_trans isog1k1 peqm) isog2k2).
        Qed.

        Lemma same_res_impl_iso_mapping M g1 g2 (iso_output : mapping_is_iso_mapping M) :
          eqb_rdf (M g1) (M g2) -> iso g1 g2.
        Proof.
          have isog1k1 : iso g1 (M g1). by apply iso_output.
          have isog2k2 : iso (M g2) g2. by rewrite iso_sym; apply iso_output.
          by move=> /eqiso peqm; apply: iso_trans (iso_trans isog1k1 peqm) isog2k2.
        Qed.

        Lemma effective_iso_can_trans_ts (M : seq (triple I B L) -> seq (triple I B L)) ts1 ts2 (u1 : uniq ts1) (u2 : uniq ts2) (uniq_output : forall ts, uniq ts -> uniq (M ts)) (iso_output : forall ts, uniq ts -> effective_iso_ts ts (M ts)) :
          effective_iso_ts ts1 ts2 -> effective_iso_ts (M ts1) (M ts2).
        Proof.
          have isog1k1 : effective_iso_ts (M ts1) ts1. by apply effective_iso_ts_sym=> //; apply iso_output.
          have isog2k2 : effective_iso_ts ts2 (M ts2). by apply iso_output.
          by move=> peqm; apply: (effective_iso_ts_trans (effective_iso_ts_trans isog1k1 peqm) isog2k2).
        Qed.

        Lemma effective_iso_can_trans M g1 g2 (iso_output : mapping_is_effective_iso_mapping M) :
          effective_iso g1 g2 -> effective_iso (M g1) (M g2).
        Proof.
          have isog1k1 : effective_iso (M g1) g1. apply effective_iso_ts_sym; first by case g1. apply iso_output.
          have isog2k2 : effective_iso g2 (M g2). by apply iso_output.
          move=> peqm; apply: (effective_iso_ts_trans (effective_iso_ts_trans isog1k1 peqm) isog2k2).
        Qed.

        Lemma iso_can_trans_ts (M : seq (triple I B L) -> seq (triple I B L)) ts1 ts2 (u1 : uniq ts1) (u2 : uniq ts2) (uniq_output : forall ts, uniq ts -> uniq (M ts)) (iso_output : forall ts, uniq ts -> iso_ts ts (M ts)) :
          iso_ts ts1 ts2 -> iso_ts (M ts1) (M ts2).
        Proof.
          have isog1k1 : iso_ts (M ts1) ts1.
            rewrite iso_ts_sym //; last by apply (uniq_output _).
            by apply iso_output.
          have isog2k2 : iso_ts ts2 (M ts2). by apply iso_output.
          by move=> peqm; apply: (iso_ts_trans (iso_ts_trans isog1k1 peqm) isog2k2).
        Qed.

        Lemma iso_can_trans M g1 g2 (iso_output : mapping_is_iso_mapping M) :
          iso g1 g2 -> iso (M g1) (M g2).
        Proof.
          have isog1k1 : iso (M g1) g1. by rewrite iso_sym; apply iso_output.
          have isog2k2 : iso g2 (M g2). by apply iso_output.
          move=> peqm; apply: (iso_trans (iso_trans isog1k1 peqm) isog2k2).
        Qed.

        Lemma isocanonical_mapping_dt_out_mapping M (iso_out: mapping_is_iso_mapping M)
          (dt: dt_names_mapping M) : isocanonical_mapping M.
        Proof.
          split; first by apply iso_out.
          split; last by apply dt.
          + by apply: same_res_impl_iso_mapping iso_out.
        Qed.

      End Isocanonical.
    End Isomorphism.

  End EqRdf.

  Definition code_ts (I B L : eqType) ts : (seq (triple I B L))%type :=
    ts.

  Definition decode_ts (I B L : eqType) (s: seq (triple I B L)) : (seq (triple I B L)) :=
    s.

  Definition odecode_ts (I B L : eqType) (s: seq (triple I B L)) : option (seq (triple I B L)) :=
    Some (decode_ts s).

  Lemma pcancel_code_decode_ts (I B L : eqType): pcancel (@code_ts I B L) (@odecode_ts I B L).
  Proof. by case. Qed.

  Section ChoiceTs.
    Variable I B L: choiceType.

    HB.instance Definition _ :=
      Choice.copy (seq (triple I B L)) (pcan_type (@pcancel_code_decode_ts I B L)).

  End ChoiceTs.
  Section OrderTs.
  Variables d : unit.
  Variables I B L : orderType d.

  Notation le_triple := (@le_triple d I B L).

  Fixpoint le_st_fix (x y : seq (triple I B L)) :=
      match (x,y) with
      | (nil,nil)=> true
      | (x::xs,y::ys) => if x == y
                      then le_st_fix xs ys
                      else le_triple x y
      | (nil,_::_) => true
      | (_::_,nil) => false
      end.

  Definition le_st : rel (seq (triple I B L)) :=
    fun x y => le_st_fix x y.

  Definition lt_st : rel (seq (triple I B L)) :=
    fun x y => (negb (x == y)) && (le_st x y).

  (* Infimum *)
  Definition meet_st : (seq (triple I B L)) -> seq (triple I B L) -> seq (triple I B L) :=
    fun x y => (if lt_st x y then x else y).

  (* Supremum *)
  Definition join_st : seq (triple I B L) -> seq (triple I B L) -> seq (triple I B L) :=
    fun x y => (if lt_st x y then y else x).

  Lemma lt_st_def : forall x y, lt_st x y = (y != x) && (le_st x y).
  Proof. by move=> x y; rewrite eq_sym. Qed.

  Lemma meet_st_def : forall x y, meet_st x y = (if lt_st x y then x else y).
  Proof. by []. Qed.

  Lemma join_st_def : forall x y, join_st x y = (if lt_st x y then y else x).
  Proof. by []. Qed.

  Lemma le_st_total : total le_st.
  Proof. elim=> [|tx txs IHtx] [| ty txy]=> //=.
         case e: (tx == ty); rewrite (eq_sym ty tx) e; first by apply: IHtx.
         + exact: le_triple_total.
  Qed.

  Lemma lt_st_neq_total sx sy : sx != sy -> lt_st sx sy || lt_st sy sx.
  Proof. rewrite !lt_st_def /negb eq_sym=> -> /=; exact: le_st_total. Qed.

  Lemma le_st_antisym sx sy : le_st sx sy && le_st sy sx -> sx == sy.
    elim: sx sy=> [| x xs IHxs] [| y ys] //=.
    case e : (x == y); rewrite (eq_sym y x) e.
      + by rewrite (eqP e)=> /IHxs/eqP ->.
      + by move=> /le_triple_antisym; rewrite e.
  Qed.

  Lemma le_st_anti : antisymmetric le_st.
  Proof. by move=> sx sy /le_st_antisym/eqP ->. Qed.

  Lemma le_st_trans : transitive le_st.
  Proof. elim=> [| x sx IHsx] [| y sy] [| z sz] //=.
         repeat (case : ifP=> // /eqP ?; subst)=> //.
         + by apply IHsx.
         + move=> le1 le2.
           suffices /eqP contra : x == z.
           by subst.
           by apply le_triple_antisym; rewrite le1 le2.
         + apply le_triple_trans.
  Qed.

  Lemma join_stA : associative join_st.
  Proof.
  move=> x y z; rewrite /join_st !(fun_if, if_arg).
  repeat (try case : ifP); rewrite // !lt_st_def Bool.andb_false_iff /negb.
  + move=> /andP[_ leyz]; case: ifP=> [/eqP -> //|_ [//|]].
    * case: ifP=> [/eqP -> //|nyx nlexz /andP[_ lexy _]].
      suffices lezx : le_st z x.
        have lexz := (le_st_trans lexy leyz).
        by apply le_st_anti; apply /andP ; split=> //.
      by move: (le_st_total x z); rewrite nlexz.
  + move=> /andP[nzy leyz]; case: ifP=> [/eqP -> //|_ [//|]].
    * case: ifP=> [/eqP eqxy| nyx nlexz /= nlexy lexz]; first by move: leyz; rewrite eqxy=> ->.
      suffices lezx : le_st z x.
        by apply le_st_anti; apply /andP ; split=> //.
      by move: (le_st_total x z) (le_st_total x y); rewrite nlexz nlexy.
  + case: ifP=> [/eqP -> _ _ /= |nzy [//|]]; first by case: ifP=> [//|_ ->].
    * case: ifP=> [/eqP -> -> _ _| nyx nlexz /= _ nlexy]; first by rewrite andbF.
      case: ifP=> //= nzx lexz.
        suffices lezx : le_st z x.
          by apply le_st_anti; apply /andP ; split=> //.
        move: (le_st_total x y) (le_st_total y z); rewrite nlexz nlexy /==> yx zy.
        by apply (le_st_trans zy yx).
  + move=> /andP[nzy leyz]; case: ifP=> [/eqP -> //| contra /=].
    case: ifP=> [/eqP eqxy| /= nyx -> /=]; last by case.
    by move: leyz; rewrite eqxy=> ->.
  Qed.

  Lemma join_st_nil_idl : left_id [::] join_st. Proof. by move=> []. Qed.

  Lemma join_st_nil_idr : right_id [::] join_st. Proof. by move=> []. Qed.

  Lemma join_st_comm : commutative join_st.
  Proof.
    move=> x y; rewrite /join_st !lt_st_def.
    case: ifP; case: ifP=> //.
    + move=> /andP[neqxy leyx] /andP[neqyx lexy].
      by apply /eqP/le_st_antisym/andP;split.
    + rewrite !Bool.andb_false_iff /negb => [[|leyx]]; first by case: ifP=> // /eqP ->.
      by case: ifP=> [/eqP -> //|  _ [//|lexy]]; move: (le_st_total x y); rewrite lexy leyx.
  Qed.


  Lemma join_st_idem : idempotent join_st.
  Proof. by move=> ?; rewrite /join_st lt_st_def eqxx. Qed.

  Lemma nil_minimum (ts: seq (triple I B L)) : le_st [::] ts.
  Proof. by case ts. Qed.

  (* Folding the join of sequences of triples results either in the default value or
     an element of the folded sequence *)
  Lemma foldl_max_st (l : seq (seq (triple I B L))) (x0 : (seq (triple I B L))):
    foldl join_st x0 l = x0 \/ foldl join_st x0 l \in l.
  Proof.
  elim: l x0 => [//| t ts IHts] x0; first by left.
  + rewrite in_cons /=; case: (IHts (join_st x0 t))=> [ -> |intail] /=.
    - rewrite join_st_def; case: ifP=> _; first by right; rewrite eqxx.
      * by left.
    - by right; rewrite intail orbT.
  Qed.

  (* The join between the empty sequence
     and any non-empty sequence of triples is different from the empty sequence *)
  Lemma join_nil_size (h : seq (triple I B L)) :
    (size h != 0) -> join_st [::] h != [::].
  Proof. by case: h=> //. Qed.

  (* Given a sequence of sequence of triples: l,
     if there is a sequence of triples: x for which x is less than every other sequence of triples,
     then if folding join in l results in x, either l is the empty sequence or x is in l *)
  Lemma max_foldl_minimum_st (l : seq (seq (triple I B L))) (x : seq (triple I B L)) :
    (forall y : (seq (triple I B L)) , lt_st x y) -> foldl join_st x l = x -> (l == [::]) || (x \in l).
  Proof.
  move=> minimum; elim: l=> [//| hd t IHt]; rewrite /= join_st_def minimum.
  case: (foldl_max_st t hd).
  + by move=> -> ->; rewrite in_cons eqxx.
  + by move=> H <-; rewrite in_cons H orbT.
  Qed.

  (* Given a sequence of sequence of triples: l,
     if there is a sequence of triples: x for which
     x is less than every other sequence of triples in l,
     then if folding join in l results in x, either l is the empty sequence or x is in l *)
  Lemma max_foldl_minimum_in_st (l : seq (seq (triple I B L))) (x : seq (triple I B L)) :
    (forall y : (seq (triple I B L)) , y \in l -> lt_st x y) ->
    foldl join_st x l = x -> (l == [::]) || (x \in l).
  Proof.
  elim: l=> [//| hd t IHt] minimum.
  rewrite /= join_st_def minimum; last by rewrite in_cons eqxx.
  case: (foldl_max_st t hd).
  + by move=> -> ->; rewrite in_cons eqxx.
  + by move=> H <-; rewrite in_cons H orbT.
  Qed.


  End OrderTs.
  Fact ts_display : unit. exact tt. Qed.

  HB.instance Definition _ (d : unit) (I B L : orderType d):=
    Monoid.isComLaw.Build
      (seq (triple I B L)) [::]
      (@join_st d I B L) (@join_stA d I B L)
      (@join_st_comm d I B L)
      (@join_st_nil_idl d I B L).

HB.instance Definition _ (d : unit) (I B L: orderType d):=
  Order.isOrder.Build ts_display (seq (triple I B L))
    (@lt_st_def d I B L) (@meet_st_def d I B L) (@join_st_def d I B L)
    (@le_st_anti d I B L) (@le_st_trans d I B L) (@le_st_total d I B L).

  (* Section CountRdf. *)
  (*   Variables I B L : countType. *)
  (*   Implicit Type g : rdf_graph I B L. *)

  (*   Lemma empty_min g : Order.max g (@empty_rdf_graph I B L) = g. *)
  (*   Proof. by case: g=> g'; case: g'=> [//|h t] us; rewrite Order.POrderTheory.maxElt. Qed. *)

  (* End CountRdf. *)

Lemma minn_refl n : minn n n = n.
Proof. by rewrite /minn; case e: (_ < _)%N. Qed.

Section OrderRdf.
  Variables d : unit.
  Variables I B L : orderType d.

  Notation le_triple := (@le_triple d I B L).

  Definition le_rdf : rel (rdf_graph I B L) :=
    fun x y => le_st x y.

  Definition lt_rdf : rel (rdf_graph I B L) :=
    fun x y => (negb ((graph x) == (graph y))) && (le_st x y).

  (* Infimum *)
  Definition meet_rdf : (rdf_graph I B L) -> (rdf_graph I B L) -> (rdf_graph I B L) :=
    fun x y => (if lt_st x y then x else y).

  (* Supremum *)
  Definition join_rdf : (rdf_graph I B L) -> (rdf_graph I B L) -> (rdf_graph I B L) :=
    fun x y => (if lt_st x y then y else x).

  Lemma lt_rdf_def : forall x y, lt_rdf x y = ((graph y) != (graph x)) && (le_rdf x y).
  Proof. by move=> x y; apply lt_st_def. Qed.

  Lemma meet_rdf_def : forall x y, meet_rdf x y = (if lt_rdf x y then x else y).
  Proof. by []. Qed.

  Lemma join_rdf_def : forall x y, join_rdf x y = (if lt_rdf x y then y else x).
  Proof. by []. Qed.

  Lemma le_rdf_total : total le_rdf.
  Proof. by move=> x y; apply: le_st_total. Qed.

  Lemma lt_rdf_neq_total g h : (graph g) != (graph h) -> lt_rdf g h || lt_rdf h g.
  Proof. rewrite !lt_rdf_def /negb eq_sym=> -> /=; exact: le_rdf_total. Qed.

  Lemma le_rdf_antisym g h : le_rdf g h && le_rdf h g -> (graph g) == (graph h).
  Proof. by apply le_st_antisym. Qed.

  Lemma le_rdf_anti : antisymmetric le_rdf.
  Proof. by move=> x y /le_st_anti/rdf_inj ->. Qed.

  Lemma le_rdf_trans : transitive le_rdf.
  Proof. by move=> x y z; apply le_st_trans. Qed.

  Lemma rdf_leP ts1 ts2 : reflect (sort le_triple ts1 = sort le_triple ts2) (perm_eq ts1 ts2).
  Proof. exact: Order.TotalTheory.perm_sort_leP ts1 ts2. Qed.

  Lemma rdf_leP' ts1 ts2 : (sort le_triple ts1 = sort le_triple ts2) <-> (perm_eq ts1 ts2).
  Proof. exact: Bool.reflect_iff (Order.TotalTheory.perm_sort_leP ts1 ts2). Qed.

End OrderRdf.

Section RDF_Spec.

  Variable I B L : eqType.

  Definition node_triple (t : triple I B L) : seq (term I B L) :=
    [:: (subject t); (object t)].

  Fixpoint fix_node_terms (ts : seq (triple I B L)) : seq (term I B L) :=
    match ts with
    | [::] => [::]
    | t :: ts' => (node_triple t) ++ (fix_node_terms ts')
    end.

  Definition node_terms (ts : seq (triple I B L)) : seq (term I B L) :=
    undup (fix_node_terms ts).

  Lemma uniq_node_terms (ts : seq (triple I B L)) : uniq (node_terms ts).
  Proof. by apply undup_uniq. Qed.

  Definition bij_nodes (ts1 ts2 : seq (triple I B L)) mu : bool :=
    bnode_map_bij (node_terms ts1) (node_terms ts2) mu.

  Definition bnodes_to_bnodes (mu : term I B L -> term I B L) :=
    forall (trm : term I B L), is_bnode trm -> is_bnode (mu trm).

  Definition lit_to_lit (ts: seq (triple I B L)) (mu : term I B L -> term I B L) :=
    forall l: L,
      (Lit l) \in (node_terms ts) -> mu (Lit l) = (Lit l).

  Definition iri_to_iri (ts: seq (triple I B L)) (mu : term I B L -> term I B L) :=
    forall i: I,
      (Iri i) \in (node_terms ts) -> mu (Iri i) = (Iri i).

  Lemma rel_pres_ib (ts : seq (triple I B L)) (mu : term I B L -> term I B L) (trm : term I B L) :
    bnodes_to_bnodes mu ->
    iri_to_iri ts mu ->
    trm \in (node_terms ts) ->
            is_in_ib  trm ->
            is_in_ib (mu trm).
  Proof.
  case: trm=> [i|l|b] btb iti in_node // iib; rewrite /is_in_ib.
  by rewrite (iti i in_node).
  + have := btb (Bnode b). by rewrite Bool.orb_comm=> ->.
  Qed.

  Lemma rel_pres_i ts (mu : term I B L -> term I B L) (trm : term I B L) :
    iri_to_iri ts mu -> trm \in (node_terms ts) ->
                                is_in_i  trm -> is_in_i (mu trm).
  Proof. by case: trm=> [i|l|b] iti in_node //=; rewrite (iti i in_node). Qed.

  Definition spec_rel_triple_iso (t : triple I B L) (mu : term I B L -> term I B L)
    (pres_s: is_in_ib (mu (subject t)))
    (pres_p : is_in_i (predicate t)) : triple I B L :=
    mkTriple (mu (object t)) pres_s pres_p.

  Definition pres_wf (ts : seq (triple I B L)) (mu : term I B L -> term I B L) :=
    forall trm,
      trm \in (node_terms ts) ->
        ( (is_in_ib trm -> is_in_ib (mu trm)) /\ (is_in_i trm -> is_in_i (mu trm))).

  Definition rel_wf_triple (t : triple I B L) (mu : term I B L -> term I B L) (ts : seq (triple I B L))
    (mu_pres_wf : pres_wf ts mu) : (subject t) \in (node_terms ts) -> triple I B L :=
    (match t with
       mkTriple s p o sib pii =>
         fun sin => @mkTriple I B L (mu s) p (mu o) ((mu_pres_wf s sin).1 sib) pii
     end).

  Lemma in_nodes_cons (trm : term I B L) (ts : seq (triple I B L)) (t' : triple I B L):
    trm \in node_terms ts -> trm \in node_terms (t' :: ts).
  Proof.
    by rewrite /node_terms !mem_undup=> H; rewrite /= !in_cons H !orbT. 
  Qed.

  Lemma in_triple_s_in_node_terms (t: triple I B L) (ts : seq (triple I B L)) :
    t \in ts -> (subject t) \in (node_terms ts).
  Proof.
    elim: ts=> [|t' ts' IH]; first by rewrite in_nil.
    rewrite in_cons. move=> /orP[/eqP->|].
    by rewrite /node_terms undup_in // /fix_node_terms in_cons eqxx.
    by move=> /IH; apply in_nodes_cons.
  Qed.

  Lemma in_triple_o_in_node_terms (t: triple I B L) (ts : seq (triple I B L)) :
    t \in ts -> (object t) \in (node_terms ts).
  Proof.
    elim: ts=> [|t' ts' IH]; first by rewrite in_nil.
    rewrite in_cons. move=> /orP[/eqP->|].
    by rewrite /node_terms undup_in // /fix_node_terms !in_cons eqxx orbC.
    by move=> /IH; apply in_nodes_cons.
  Qed.

  Definition adj_pres (ts1 ts2: seq (triple I B L)) (mu : term I B L -> term I B L) :=
    pres_wf ts1 mu ->
    forall t, t \in ts1 <-> forall wf_s wf_p, @mkTriple I B L (mu (subject t)) (predicate t) (mu (object t)) wf_s wf_p \in ts2.

  Definition spec_is_iso (ts1 ts2 : seq (triple I B L)) mu :=
    bij_nodes ts1 ts2 mu /\
      bnodes_to_bnodes mu /\
        lit_to_lit ts1 mu /\
          iri_to_iri ts1 mu /\
            adj_pres ts1 ts2 mu.

  Definition spec_iso (ts1 ts2 : seq (triple I B L)) :=
    exists (mu : term I B L -> term I B L), spec_is_iso ts1 ts2 mu.

  Lemma nodes_terms_cons (trpl : triple I B L) (ts : seq (triple I B L)):
    node_terms (trpl :: ts) = undup (node_triple trpl ++ node_terms ts).
  Proof. by rewrite {1}/node_terms /fix_node_terms -undup_cat_r -undup_cat_l. Qed.

  Lemma bnodes_nodes (ts : seq (triple I B L)) : perm_eq (bnodes_ts ts) (filter (@is_bnode I B L) (node_terms ts)).
  Proof.
  suffices mem_eq : (bnodes_ts ts) =i (filter (@is_bnode I B L) (node_terms ts)).
    apply uniq_perm=> //.
    + by apply uniq_bnodes_ts.
    + by apply filter_uniq; apply uniq_node_terms.
  elim: ts=> [//| t tl IHl].
  move=> T; rewrite bnodes_ts_cons mem_undup.
  rewrite nodes_terms_cons filter_undup mem_undup filter_cat.
  rewrite !mem_cat.
  f_equal ; last by rewrite IHl.
  case: t=> s p o sib pii. rewrite /bnodes_triple.
  rewrite /terms_triple filter_undup mem_undup.
  suffices -> : [seq x <- [:: s; p; o] | is_bnode x] = [seq x <- [:: s; o] | is_bnode x].
    done.
  by case: p pii=> //.
  Qed.

  Lemma map_filter_nodes ts (mu : B -> B)  :
    [seq x <- [seq relabeling_term mu i | i <- node_terms ts] | is_bnode x] = [seq relabeling_term mu i | i <- [seq x <- node_terms ts | is_bnode x]].
  Proof. by elim: (node_terms ts) => [//| []h tl IHl]; rewrite /= IHl. Qed.

  Lemma in_nt_in_ts (trm: term I B L) (ts : seq (triple I B L)) :
    trm \in node_terms ts -> exists t, (t \in ts) && (((subject t) == trm) || ((object t) == trm)).
  Proof.
   elim: ts=> [//| hd tl IHl].
   rewrite nodes_terms_cons mem_undup mem_cat=> /orP[]eq.
   + exists hd.
     rewrite in_cons eqxx /=.
     move: eq; rewrite /node_triple !in_cons.
     by move=> /orP[ /eqP ->| /orP[/eqP ->|]] //; rewrite eqxx ?orbT.
   + have [t0 /andP[tin tP]]:= IHl eq.
     by exists t0; rewrite tP andbT; apply: inweak tin.
  Qed.

  Lemma in_ts_in_nt (t : triple I B L) (ts : seq (triple I B L)):
    t \in ts -> ((subject t) \in node_terms ts) && ((object t) \in node_terms ts).
  Proof.
    elim: ts=> [//| hd tl IHl] tin.
    rewrite !nodes_terms_cons !mem_undup.
    case_eq (t == hd).
      + by move=> /eqP <- /=; rewrite in_cons eqxx /=; apply inweak; rewrite in_cons eqxx.
      + move=> neq; rewrite in_cons neq /= in tin; rewrite !mem_cat.
        have /andP[-> ->]:= IHl tin.
        by rewrite !orbT.
  Qed.

  Lemma not_b_rel_inj (trm1 trm2 : term I B L) (mu : B -> B) : negb (is_bnode trm1) -> negb (is_bnode trm2)->
                                                              relabeling_term mu trm1 = relabeling_term mu trm2 ->
                                                              trm1 = trm2.
  Proof. by case: trm1; case: trm2=> //. Qed.

  Lemma the_function :
    forall (mu : term I B L -> term I B L), bnodes_to_bnodes mu ->
       exists (nu : B -> B),
           Bnode \o nu =1 mu \o Bnode.
  Proof.
    move=> mu btb.
    exists (fun b => let fb := mu (Bnode b) in
                     let fPb := btb (Bnode b) isT in
                     match fb as fb' return is_bnode fb' -> B with
                     | Iri i => fun bfb=> False_rect _ (notF bfb)
                     | Bnode b2 => fun _ => b2
                     | Lit l => fun bfb=> False_rect _ (notF bfb)
                     end fPb).
    move=> b /=; move : (btb (Bnode b) isT).
    by case: (mu (Bnode b)).
  Qed.

  Lemma relabeling_and_constructing : forall (mu : B -> B) (b : B),
      (Bnode (I := I) (L := L) \o mu) b = relabeling_term mu (Bnode b).
  Proof. by move=> mu b. Qed.

  Lemma relabeling_and_constructing1 : forall (mu : B -> B),
      (Bnode (I := I) (L := L) \o mu) =1 (relabeling_term mu) \o Bnode.
  Proof. by move=> mu. Qed.

  Theorem iso_equiv (ts1 ts2 : seq (triple I B L)) :
    (uniq ts1) -> (uniq ts2) ->
      effective_iso_ts ts1 ts2 <-> spec_iso ts1 ts2.
  Proof.
  move=> u1 u2; split.
  move=> /(effective_iso_iso u1 u2).
  move=> [mu [/and3P[piso wf_ret adj]] mu_part].
  exists (relabeling_term mu); split.
  have piso2 := piso.
  rewrite /is_pre_iso_ts/bnode_map_bij in piso.
  move : piso => /and3P[_ _ piso].
  rewrite /bij_nodes.
  rewrite /bnode_map_bij.
  rewrite !uniq_node_terms /=.
  apply uniq_perm.
  rewrite map_inj_in_uniq; first by rewrite uniq_node_terms.
  move=> /= nx ny /=.
  have /permEl /perm_mem eq := perm_filterC (@is_bnode I B L) (node_terms ts1).
  rewrite -!eq !mem_cat=> /orP[nxbnode |nxnotbnode] /orP[nybnode | nynotbnode].
  rewrite -!(perm_mem (bnodes_nodes ts1)) in nxbnode nybnode.
  have mu_inj_bnodes := is_pre_iso_ts_bnodes_inj piso2.
  by apply mu_inj_bnodes.
  by move: nxbnode nynotbnode; rewrite !mem_filter /=; case: nx=> //; case ny=> //.
  by move: nxnotbnode nybnode; rewrite !mem_filter /=; case: nx=> //; case ny=> //.
  by move: nxnotbnode nynotbnode; rewrite !mem_filter /=; case: nx=> //; case ny=> //.
  apply uniq_node_terms.
      move=> trm; apply /idP/idP=> /=.
      move=> /mapP[/= t' in_nt].
      have [triple /andP[tin tP]] := in_nt_in_ts in_nt.
      apply (map_f (relabeling_triple mu)) in tin.
      rewrite (perm_mem adj) in tin.
      have /andP[sin_nt oin_nt] := in_ts_in_nt tin.
      move=> eq.
      rewrite {}eq.
      case/orP: tP.
       + by move=> /eqP <-; rewrite -projs_rel.
       + by move=> /eqP <-; rewrite -projo_rel.
         (**)
      move=> trmin.
      apply /mapP=> /=.
      case_eq (is_bnode trm).
      - case: trm trmin=> trm //= trmin _.
        have /permEl /perm_mem eq := perm_filterC (@is_bnode I B L) (node_terms ts2).
        rewrite -eq mem_cat orbC mem_filter /= in trmin.
        rewrite -!(perm_mem (bnodes_nodes ts2)) in trmin.
        rewrite -perm_relabel_bts in piso.
        rewrite -(perm_mem piso) in trmin.
        move/mapP : trmin => /=[pre_trm pre_in preeq].
        exists pre_trm=> //.
        have /permEl /perm_mem eq_mem := perm_filterC (@is_bnode I B L) (node_terms ts1).
        rewrite -eq_mem mem_cat.
        rewrite !(perm_mem (bnodes_nodes ts1)) in pre_in.
        by rewrite pre_in.
      - move=> nbnode. exists trm.
        have /= [triple /andP[tin tP]] := in_nt_in_ts trmin.
      rewrite -(perm_mem adj) in tin.
      have /andP[sin_nt oin_nt] := in_ts_in_nt tin.
      suffices node_terms_rel : forall trm ts mu, negb (is_bnode trm) -> (trm \in node_terms ts) = (trm \in node_terms (relabeling_seq_triple mu ts)).
       move/eqP : nbnode; rewrite eqbF_neg=> nbnode.
       case/orP: tP.
       + move/eqP=> eq; by rewrite (node_terms_rel trm ts1 mu nbnode) -eq.
       + move/eqP=> eq; by rewrite (node_terms_rel trm ts1 mu nbnode) -eq.
       + move=> trm' ts' mu' nbnode'.
         apply /idP/idP.
         + move: nbnode'; case: trm'=> []b //= _; elim: ts'=> [//| t tl IHl] /=.
           rewrite !nodes_terms_cons !mem_undup !mem_cat=> /orP[].
           rewrite {1}/node_triple !in_cons in_nil=> /orP[/eqP| /orP[/eqP | //]].
           rewrite projs_rel=> <-; rewrite eqxx //.
           rewrite projo_rel => <-; rewrite eqxx //; by case (_ == _).
           + by move=> /IHl ->; rewrite orbT.
           rewrite !nodes_terms_cons !mem_undup !mem_cat=> /orP[].
           rewrite {1}/node_triple !in_cons in_nil=> /orP[/eqP| /orP[/eqP | //]].
           rewrite projs_rel=> <-; rewrite eqxx //.
           rewrite projo_rel => <-; rewrite eqxx //; by case (_ == _).
           + by move=> /IHl ->; rewrite orbT.
         + move: nbnode'; case: trm'=> []b //= _; elim: ts'=> [//| t tl IHl] /=.
           rewrite !nodes_terms_cons !mem_undup !mem_cat=> /orP[].
           rewrite {1}/node_triple !in_cons in_nil=> /orP[/eqP| /orP[/eqP | //]].
           by rewrite projs_rel; case: (subject t)=> //i ->; rewrite eqxx.
           by rewrite projo_rel; case: (object t)=> //i ->; rewrite eqxx; case (_ == _).
           + by move=> /IHl ->; rewrite orbT.
           rewrite !nodes_terms_cons !mem_undup !mem_cat=> /orP[].
           rewrite {1}/node_triple !in_cons in_nil=> /orP[/eqP| /orP[/eqP | //]].
           by rewrite projs_rel; case: (subject t)=> //i ->; rewrite eqxx.
           by rewrite projo_rel; case: (object t)=> //i ->; rewrite eqxx; case (_ == _).
           + by move=> /IHl ->; rewrite orbT.
    by case: trm nbnode trmin.
  (*  *)
  + split.
  + by move=> []//.
  + split.
    - move=> //.
    - split.
      * by move=> //.
        ++ rewrite /adj_pres/pres_wf /==> p_wf t; split=> tin.
          move=> wf_s wf_p.
          apply perm_mem in adj.
          rewrite -adj.
          suffices -> : {|
                       subject := relabeling_term mu (subject t);
                                  predicate := predicate t;
                                               object := relabeling_term mu (object t);
                                                         subject_in_IB := wf_s;
                                                                          predicate_in_I := wf_p
                     |} = relabeling_triple mu t.
            by apply map_f.
          apply triple_inj; case: t tin wf_s wf_p=> /= s p o sib pin tin wf_s wf_p //.
          by case: p pin tin wf_p.
        suffices [wfs wfp]: is_in_ib (relabeling_term mu (subject t)) /\ is_in_i (predicate t).
          by apply (mu_part _ wfs wfp); apply tin.
        split.
         + case t=> s /= _ _ sib _. by apply relabeling_term_preserves_is_in_ib.
         + by case t=> _ p /= _ _ pii.
+ move=> /= [mu_trm [bij_nodes [b_to_b [l_id [i_id /= adj_pres]]]]].
  (* rewrite /= mu_trm. *)
  have [mu muP] := (the_function b_to_b).
  exists mu.
   suffices piso_mu : is_pre_iso_ts ts1 ts2 mu.
    suffices /(perm_eq_relab_uniq_ts u2) [u peq] : perm_eq (relabeling_seq_triple mu ts1) ts2.
      by apply /and3P; split=> //.
      rewrite /adj_pres /= in adj_pres.
      suffices pwf : pres_wf ts1 mu_trm.
      move: adj_pres=> /(_ pwf) adj_pres.
      apply uniq_perm=> //.
      (**)
      rewrite map_inj_in_uniq //.
      apply inj_get_bts_inj_ts.
      by apply: (is_pre_iso_ts_inj2 piso_mu).
      (* admit. *)
      move=> t.
      apply /idP/idP.
      move=> /mapP[/= t' tin ->].
      have tin2 := tin.
      rewrite (adj_pres t') in tin.
      suffices /andP[wfs wfp]: is_in_ib (mu_trm (subject t')) && is_in_i (predicate t').
      have := tin wfs wfp.
      suffices -> : {|
                      subject := mu_trm (subject t');
                      predicate := predicate t';
                      object := mu_trm (object t');
                      subject_in_IB := wfs;
                      predicate_in_I := wfp
                    |} = relabeling_triple mu t'.
      done.
      (**)
      apply triple_inj=> //=.
      rewrite !projs_rel.
      apply in_triple_s_in_node_terms in tin2.
      case: (subject t') wfs tin2=> //= x _ irinx.
      by apply i_id.
      by apply l_id.
      rewrite /comp/= in muP.
      by rewrite muP.
      rewrite !projp_rel.
      by case: (predicate t') wfp.
      rewrite !projo_rel.
      apply in_triple_o_in_node_terms in tin2.
      case: (object t') tin2 => //= x.
      rewrite /comp/= in muP.
      by rewrite muP.
      (**)
      have [h1 _]:= pwf (subject t') (in_triple_s_in_node_terms tin2).
      apply /andP; split.
       by rewrite h1; case : t' tin2 tin h1.
       by case t'.
      rewrite /bij_nodes/bnode_map_bij in bij_nodes.
      move: bij_nodes=> /and3P[_ _ bij_nodes].
      move=> tin2.
      have /andP[sin_nodes oin_nodes] := in_ts_in_nt tin2.
      rewrite -!(perm_mem bij_nodes) in sin_nodes oin_nodes.
      move/mapP : sin_nodes => [/= s' s'in seq].
      move/mapP : oin_nodes => [/= o' o'in oeq].
      suffices [sib' pii'] : is_in_ib s' /\ is_in_i (predicate t).
      pose t' := mkTriple o' sib' pii'.
      suffices : t' \in ts1.
        move=> /(map_f (relabeling_triple mu)).
        suffices -> :  relabeling_triple mu t' = t.
          done.
        apply triple_inj.
        + rewrite projs_rel. rewrite seq.
          rewrite /=.
          move {t'}.
          case: s' sib' s'in {seq}=> //x.
          - by move=> _ /i_id ->.
          - by move=> _ _ /=; rewrite /comp in muP; rewrite muP.
            + by rewrite projp_rel /==> {t'}; case: (predicate t) pii'.
            + rewrite projo_rel oeq /=.
              case: o' o'in oeq {t'}=> //=x.
          - by move=> /i_id ->.
          - by move=> /l_id ->.
          - by move=> _ _ /=; rewrite /comp in muP; rewrite muP.
            (**)
            apply adj_pres.
            move=> wfs wfp.
            rewrite /=.
            suffices <- : t =
                         {| subject := mu_trm s'; predicate := predicate t; object := mu_trm o'; subject_in_IB := wfs; predicate_in_I := wfp |}.
              done.
            by apply triple_inj=> //=.
            split; last by (case t).
            case: t {tin2} seq {oeq}=> /= s _ _ sib _ eq.
            rewrite {}eq in sib.
            move: sib.
            case: s' s'in seq=> //x.
            move=> /l_id -> //.
            (* *)
      rewrite /pres_wf /==> trm tin; split.
      rewrite /is_in_ib=> /orP[].
      + by case: trm tin=> //=i tin _; rewrite i_id.
      + by case: trm tin=> //=i tin _; rewrite b_to_b // orbT.
      + by case: trm tin=> //=i tin _; rewrite i_id.
        (* piso *)
  apply /and3P; split; rewrite ?uniq_get_bts //.
  rewrite -perm_relabel_bts.
  apply uniq_perm; rewrite ?uniq_bnodes_ts //.
  rewrite /bij_nodes/bnode_map_bij in bij_nodes.
  move: bij_nodes=> /and3P[_ _ bij_nodes].
  have umap : uniq [seq mu_trm i | i <- node_terms ts1] by rewrite (perm_uniq bij_nodes) uniq_node_terms.
  have /(_ ts1) inj_mu := (in_map_injP (mu_trm ) (uniq_node_terms _)).
  move: umap=> /inj_mu {}inj_mu_trm.
  rewrite bnodes_map_get_bts -map_comp.

  have /eq_map <- := relabeling_and_constructing1 mu.
  rewrite (eq_map muP) map_comp -bnodes_map_get_bts.
  rewrite map_inj_in_uniq ?uniq_bnodes_ts //.
  move=> b1 b2 b1in b2in. apply inj_mu_trm.
  have /permEl /perm_mem <- := perm_filterC (@is_bnode I B L) (node_terms ts1).
  by rewrite mem_cat -(perm_mem (bnodes_nodes ts1)) b1in.
  have /permEl /perm_mem <- := perm_filterC (@is_bnode I B L) (node_terms ts1).
  by rewrite mem_cat -(perm_mem (bnodes_nodes ts1)) b2in.
  (**)
  move=> b.
  apply /idP/idP.
  have /(eq_mem_map (relabeling_term mu)) H := (perm_mem (bnodes_nodes ts1)).
  rewrite bnodes_map_get_bts -map_comp.
  have /eq_map <- := relabeling_and_constructing1 mu.
  rewrite (eq_map muP) map_comp -bnodes_map_get_bts.
  rewrite /bij_nodes/bnode_map_bij in bij_nodes.
  move: bij_nodes=> /and3P[_ _ bij_nodes].
  move=> bin.
  suffices : b \in [seq mu_trm i | i <- node_terms ts1].
    rewrite (perm_mem bij_nodes).
    have : is_bnode b. move/mapP : bin=> /= [t2 t2in ].
      have /allP := (all_bnodes_ts ts1).
      move=> /(_ t2 t2in).
      by case: t2 t2in=> //b2 bin /b_to_b H2 -> //.
    have /permEl /perm_mem <- := perm_filterC (@is_bnode I B L) (node_terms ts2).
    rewrite mem_cat. rewrite -(perm_mem (bnodes_nodes ts2)).
    by rewrite mem_filter /==> -> /=; rewrite orbF.
    have /permEl /perm_mem H2 := perm_filterC (@is_bnode I B L) (node_terms ts1).
    rewrite -(eq_mem_map mu_trm H2).
    rewrite map_cat mem_cat.
    have /(eq_mem_map mu_trm) H3 := (perm_mem (bnodes_nodes ts1)).
    rewrite H3 in bin.
    by rewrite bin.
    (**)
  rewrite /bij_nodes/bnode_map_bij in bij_nodes.
  move: bij_nodes=> /and3P[_ _ bij_nodes].
  rewrite (perm_mem (bnodes_nodes ts2)).
  apply (perm_filter (@is_bnode I B L)) in bij_nodes.
  rewrite -(perm_mem bij_nodes).
  rewrite mem_filter.
  rewrite bnodes_map_get_bts -map_comp.
  have /eq_map <- := relabeling_and_constructing1 mu.
  rewrite (eq_map muP) map_comp -bnodes_map_get_bts.
  move=> /andP[bb /mapP[/= t tin c]].
  suffices H: t \in bnodes_ts ts1.
  apply /mapP=> /=.
  exists t=> //.
    suffices bt : is_bnode t.
      rewrite (perm_mem (bnodes_nodes ts1)).
      by rewrite mem_filter bt tin.
      rewrite c in bb.
      move: bb.
        case: t tin {c}=> []//x tin.
      by rewrite (i_id x tin).
      by rewrite (l_id x tin).
      Qed.


  Definition spec_isocanonical_mapping (M : rdf_graph I B L -> rdf_graph I B L) :=
    (forall (g : rdf_graph I B L), spec_iso g (M g)) /\
      (forall (g1 g2 : rdf_graph I B L) , eqb_rdf (M g1) (M g2) <-> spec_iso g1 g2).

  Lemma effective_iso_can_spec_iso_can (M : rdf_graph I B L -> rdf_graph I B L) :
    effective_isocanonical_mapping M -> spec_isocanonical_mapping M.
  Proof.
    move=> [iso_out can].
    split.
    + move=> g. apply (iso_equiv (ugraph _) (ugraph _)). apply iso_out.
    + move=> g h; split.
      - by move=> /can /(iso_equiv (ugraph _) (ugraph _)).
      - by move=> siso; apply can; apply (iso_equiv (ugraph _) (ugraph _)).
  Qed.


End RDF_Spec.

End Rdf.

