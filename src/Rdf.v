From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Triple Term Util.

Section Rdf.

  Record rdf_graph (I B L : eqType) := mkRdfGraph {
                                           graph :> seq (triple I B L) ;
                                           ugraph : uniq graph
                                         }.

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

      Definition decode_rdf (s: seq (triple I B L)) : option (rdf_graph I B L) :=
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

    Canonical rdf_eqType (i b l : eqType):= EqType (rdf_graph i b l) (PcanEqMixin (@pcancel_code_decode i b l)).
    Canonical rdf_predType (i b l : eqType) := PredType (pred_of_seq \o (@graph i b l)).

    Remark eq_eqb_rdf g1 g2 : g1 == g2 -> eqb_rdf g1 g2.
    Proof. by move=> /eqP ->; rewrite eqb_rdf_refl. Qed.

    Implicit Type t : triple I B L.
    Implicit Type ts : seq (triple I B L).

    Definition empty_rdf_graph {i b l : eqType} := @mkRdfGraph i b l [::] (eqxx true) : rdf_graph i b l.

    Definition is_ground g : bool :=
      all (@is_ground_triple _ _ _) g.

    Definition relabeling_seq_triple
      (B' B'': Type) (μ : B' -> B'')
      (ts : seq (triple I B' L)) : seq (triple I B'' L) :=
      map (relabeling_triple μ) ts.

    Section Relabeling_seq_triple.
      Variable B' : Type.

      Lemma relabeling_seq_triple_id ts : relabeling_seq_triple id ts = ts.
      Proof. by elim ts => [//| t ts' ihts] /=; rewrite relabeling_triple_id ihts. Qed.

      Lemma relabeling_seq_triple_ext (μ1 μ2 : B -> B') ts :
        μ1 =1 μ2 -> relabeling_seq_triple μ1 ts = relabeling_seq_triple μ2 ts.
      Proof. move=> mu_eq; apply: eq_map; exact: relabeling_triple_ext. Qed.

      Lemma relabeling_seq_triple_comp (B'' : eqType) (μ2 : B -> B') (μ1 : B' -> B'') ts :
        relabeling_seq_triple μ1 (relabeling_seq_triple μ2 ts) =
          relabeling_seq_triple (μ1 \o μ2) ts.
      Proof.
        by rewrite /relabeling_seq_triple -map_comp; apply: eq_map=> x; rewrite relabeling_triple_comp.
      Qed.

      Lemma relabeling_seq_triple_nil (B1 B2: Type) (μ: B1 -> B2) :
        relabeling_seq_triple μ [::] = [::].
      Proof. by []. Qed.

    End Relabeling_seq_triple.

    Definition relabeling
      (B' B'' : eqType) (μ : B' -> B'')
      (g : rdf_graph I B' L)  (urel : uniq (relabeling_seq_triple μ (graph g))): rdf_graph I B'' L:=
      mkRdfGraph urel.

    Lemma relabeling_triple_map_comp (B' B'': eqType) (ts : seq (triple I B L)) (mu1: B -> B') (mu2 : B' -> B'') :
      [seq relabeling_triple mu2 i | i <- [seq relabeling_triple mu1 i | i <- ts]] =
        [seq relabeling_triple (mu2 \o mu1) i | i <- ts].
    Proof. have ->: [seq relabeling_triple (mu2 \o mu1) i | i <- ts] = relabeling_seq_triple (mu2 \o mu1) ts by [].
           by rewrite -relabeling_seq_triple_comp.
    Qed.

    Lemma rdf_perm_mem_eq {i b l : eqType} (g1 g2 :rdf_graph i b l) :
      (perm_eq g1 g2) <-> (g1 =i g2).
    Proof. split; first by move=> /perm_mem.
           by move: (ugraph g1) (ugraph g2); apply uniq_perm.
    Qed.

    Lemma rdf_mem_eq_graph g1 g2 :
      g1 =i g2 <-> (graph g1) =i (graph g2).
    Proof. by []. Qed.

    Lemma relabeling_comp (B' B'': eqType) g (μ1 : B -> B') (μ2: B' -> B'') :
      forall u1 u2 u12,
        perm_eq (@relabeling B' B'' μ2 (@relabeling B B' μ1 g u1) u2) (@relabeling B B'' (μ2 \o μ1) g u12).
    Proof. move=> u1 u2 u12; rewrite rdf_perm_mem_eq /relabeling/==> x /=.
           suffices ->: {| graph := relabeling_seq_triple μ2 (relabeling_seq_triple μ1 g); ugraph := u2 |} = {| graph := relabeling_seq_triple (μ2 \o μ1) g; ugraph := u12 |} by [].
           by apply rdf_inj; rewrite /= relabeling_seq_triple_comp.
    Qed.

    Section Relabeling_graph.

      Lemma relabeling_id g : forall us, (@relabeling B B id g us) = g.
      Proof. by case g => g' ug us ; apply rdf_inj=> /=; rewrite relabeling_seq_triple_id. Qed.

      Variable B' : eqType.

      Lemma relabeling_ext  (μ1 μ2 : B -> B') g (mu_ext: μ1 =1 μ2) :
        forall u1 u2, @relabeling B B' μ1 g u1 = @relabeling B B' μ2 g u2.
      Proof. by move=> u1 u2; apply /rdf_inj; rewrite /= (relabeling_seq_triple_ext _ mu_ext). Qed.

      Lemma relabeling_nil (B1 B2: eqType) (μ: B1 -> B2) :
        @relabeling B1 B2 μ empty_rdf_graph (eqxx true) = empty_rdf_graph.
      Proof. by apply rdf_inj. Qed.

      Lemma relabeling_cons (B1 B2 : eqType) (μ: B1 -> B2) (trpl : triple I B1 L) (ts : seq (triple I B1 L)) (ucons : uniq (trpl :: ts)) :
        forall us,
          @relabeling B1 B2 μ (mkRdfGraph ucons) us =
            mkRdfGraph (undup_uniq (relabeling_triple μ trpl :: (relabeling_seq_triple μ ts))).
      Proof. by move=> us; apply rdf_inj=> /=; move: us=> /andP[/negPf -> /undup_id ->]. Qed.

    End Relabeling_graph.

    Definition terms_ts (I' B' L': eqType) (ts : seq (triple I' B' L')) : seq (term I' B' L') :=
      undup (flatten (map (@terms_triple I' B' L') ts)).

    Lemma undup_terms_ts ts : undup (terms_ts ts) = (terms_ts ts).
    Proof. by rewrite undup_idem. Qed.

    Lemma uniq_terms_ts (i b l : eqType) (ts : seq (triple i b l)) : uniq (terms_ts ts).
    Proof. by apply undup_uniq. Qed.
    Hint Resolve uniq_terms_ts.

    Remark uniq_tail (T: eqType) a (t : seq T) : (uniq (a :: t)) -> uniq t.
    Proof. by move=> /andP[_ //]. Qed.

    Lemma terms_ts_cons (I' B' L': eqType) (trpl : triple I' B' L') (ts : seq (triple I' B' L')) :
      terms_ts (trpl :: ts) = undup (terms_triple trpl ++ (terms_ts ts)).
    Proof. by case: ts =>  [ // | ? ? /= ]; rewrite undup_cat_r. Qed.

    Definition terms (I' B' L': eqType) (g : rdf_graph I' B' L') : seq (term I' B' L') :=
      undup (flatten (map (@terms_triple I' B' L') (graph g))).

    Lemma terms_graph (I' B' L': eqType) (g : rdf_graph I' B' L') :
      terms g = terms_ts (graph g).
    Proof. by case g. Qed.

    Lemma undup_terms g : undup (terms g) = (terms g).
    Proof. by rewrite terms_graph undup_terms_ts. Qed.

    Lemma uniq_terms (i b l : eqType) (g : rdf_graph i b l) : uniq (terms g).
    Proof. by apply undup_uniq. Qed.
    Hint Resolve uniq_terms.

    Lemma terms_cons (I' B' L': eqType) (trpl : triple I' B' L') (ts : seq (triple I' B' L')) (us : uniq (trpl :: ts)):
      terms (mkRdfGraph us) = undup (terms_triple trpl ++ (terms (mkRdfGraph (uniq_tail us)))).
    Proof. by rewrite !terms_graph terms_ts_cons. Qed.

    Section TermRelabeling.
      Variable B1 B2: eqType.

      Lemma terms_triple_map_rt (t : triple I B1 L) (mu : B1 -> B2) :
        terms_triple (relabeling_triple mu t) =i [seq relabeling_term mu i | i <- terms_triple t].
      Proof. by case t=> s p o ? ? x; rewrite -mem_map_undup mem_undup. Qed.

      Lemma terms_ts_relabeled_mem (ts : seq (triple I B1 L)) (mu: B1 -> B2) :
        (terms_ts (relabeling_seq_triple mu ts)) =i (map (relabeling_term mu) (terms_ts ts)).
      Proof. elim: ts=> [//| h t IHt] /= x.
             by rewrite !terms_ts_cons !mem_undup -mem_map_undup map_cat !mem_cat IHt terms_triple_map_rt.
      Qed.

      Lemma terms_relabeled_mem (g : rdf_graph I B1 L) (mu: B1 -> B2) :
        forall us,
        (@terms I B2 L (@relabeling B1 B2 mu g us)) =i (map (relabeling_term mu) (terms g)).
      Proof. by move=> ? x; rewrite !terms_graph terms_ts_relabeled_mem. Qed.

      Lemma relabeling_triple_inj (i l B' B'' : Type) (mu : B' -> B'') (mu_inj :injective mu) : injective (@relabeling_triple i l B' B'' mu).
      Proof.
        have /(_ i l) rtmu_inj := (relabeling_term_inj mu_inj).
        by move=> [? ? ? ? ?] [? ? ? ? ?] // [] /rtmu_inj eq1 /rtmu_inj eq2 /rtmu_inj eq3; apply triple_inj.
      Qed.

      Lemma terms_ts_relabeled (ts : seq (triple I B1 L)) (mu : B1 -> B2) (mu_inj: injective mu):
        terms_ts (relabeling_seq_triple mu ts) = [seq relabeling_term mu i | i <- terms_ts ts].
      Proof.
        have rts_inj := (@relabeling_triple_inj I L B1 B2 mu mu_inj).
        have rt_inj := (@relabeling_term_inj I B1 B2 L mu mu_inj).
        elim: ts=> [//| h tl IHtl].
        have step: undup ([seq relabeling_term mu i | i <- terms_triple h] ++
                          [seq relabeling_term mu i | i <- flatten [seq terms_triple i | i <- tl]]) =
               undup
                 ([seq relabeling_term mu i | i <- terms_triple h] ++
                    undup [seq relabeling_term mu i | i <- flatten [seq terms_triple i | i <- tl]]) by rewrite undup_cat_r.
        rewrite -undup_map_inj // !terms_ts_cons /= map_cat step.
        by apply f_equal; rewrite IHtl terms_relabeled_triple // undup_map_inj.
      Qed.

      Lemma terms_relabeled (g : rdf_graph I B1 L) (mu: B1 -> B2) (inj_mu : injective mu):
        forall us,
          (@terms I B2 L (@relabeling B1 B2 mu g us)) = map (relabeling_term mu) (terms g).
      Proof. by move=> /= us; rewrite !terms_graph terms_ts_relabeled. Qed.

    End TermRelabeling.

    Definition bnodes_ts (i b l : eqType) (ts : seq (triple i b l)): seq (term i b l) :=
      undup (filter (@is_bnode i b l) (terms_ts ts)).

    Definition bnodes (i b l : eqType) (g : rdf_graph i b l) : seq (term i b l) :=
      bnodes_ts (graph g).

    Section BnodeRelabeling.
      Variable B1 B2: eqType.

      (* Lemma mem_filter_map ts1 ts2 : *)
      (*   filter *)
      Lemma rt_pres_b (t : term I B1 L) (mu : B1 -> B2) : is_bnode t -> is_bnode (relabeling_term mu t).
      Proof. by case t. Qed.

      Lemma mem_filter_map (T: eqType) f p a (s : seq T) : (forall b, p b = p (f b)) -> (a \in (map f (filter p s))) = (a \in filter p (map f s)).
      Proof. elim: s=> [//|h t IHts] pres.
             case e: (p h).
             by rewrite /= e; rewrite pres in e; rewrite e /= !in_cons IHts //.
             by rewrite /= e; rewrite pres in e; rewrite e /= IHts //.
      Qed.

      Lemma filter_map_rt (trms: seq (term I B1 L)) (us: uniq trms) (mu: B1 -> B2) :
        [seq x <- [seq relabeling_term mu i | i <- trms ] | is_bnode x] =i
                                                                         [seq relabeling_term mu i | i <- trms & is_bnode i].
      Proof. elim: trms us=> [//| hd tl IHtl] [/andP[nin utl]] x /=.
             case e: (is_bnode hd) nin.
             by rewrite rt_pres_b //= in_cons IHtl.
             have -> : is_bnode (relabeling_term mu hd) = false by move : e; case hd=> //.
             by rewrite IHtl.
      Qed.

      Lemma bnodes_ts_relabel_mem (ts : seq (triple I B1 L)) (mu: B1 -> B2) :
        bnodes_ts (relabeling_seq_triple mu ts) =i (map (relabeling_term mu) (bnodes_ts ts)).
      Proof. move=> x; rewrite mem_undup -mem_map_undup.
             by rewrite mem_filter terms_ts_relabeled_mem -mem_filter filter_map_rt.
      Qed.

      Lemma bnodes_relabel_mem (g: rdf_graph I B1 L) (mu: B1 -> B2) :
        forall us,
        bnodes (@relabeling B1 B2 mu g us) =i (map (relabeling_term mu) (bnodes g)).
      Proof. by move=> ? x; rewrite bnodes_ts_relabel_mem. Qed.

      Lemma bnodes_ts_relabel_inj (ts: seq (triple I B1 L)) (mu: B1 -> B2) (mu_inj : injective mu):
        bnodes_ts (relabeling_seq_triple mu ts) = (map (relabeling_term mu) (bnodes_ts ts)).
      Proof.
        have /(_ I L) rtmu_inj := relabeling_term_inj mu_inj.
        rewrite /bnodes_ts terms_ts_relabeled // -filter_undup undup_map_inj // -filter_undup.
        elim: (undup (terms_ts ts)) => [// | hd tl IHtl] /=.
             case e: (is_bnode hd).
             by rewrite rt_pres_b // IHtl.
             have -> : is_bnode (relabeling_term mu hd) = false by move : e; case hd=> //.
             by rewrite IHtl.
      Qed.

      (* Lemma undup_map_inj_in (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1) : *)
      (*   {in s&, injective f} -> *)
      (*   undup [seq f i | i <- s] =i [seq f i | i <- undup s]. *)
      (* Proof. *)
      (*   move=> inj_f. *)
      (*   move=> x; rewrite -mem_map_undup mem_undup. *)

      (*   elim: s => //= h t IHt injF. *)
      (*   case e: (h \in t). *)
      (*   by rewrite map_f // IHt // => x y /(inweak h) xin /(inweak h) yin; apply injF. *)
      (*   case e2: (f h \in [seq f i | i <- t]). *)
      (*   rewrite (map_f f).  in e. rewrite e. *)


      (*   /=. *)
      Lemma bnodes_relabel (g: rdf_graph I B1 L) (mu: B1 -> B2) (inj_mu : injective mu):
        forall us,
          bnodes (@relabeling B1 B2 mu g us) = (map (relabeling_term mu) (bnodes g)).
      Proof. by rewrite /bnodes /= bnodes_ts_relabel_inj. Qed.

    End BnodeRelabeling.

    Lemma bnodes_ts_cons (trpl : triple I B L) (ts : seq (triple I B L)) :
      bnodes_ts (trpl :: ts) = undup ((bnodes_triple trpl) ++ (bnodes_ts ts)).
    Proof. by rewrite /bnodes_ts terms_ts_cons filter_undup undup_idem undup_cat_r filter_cat. Qed.

    Lemma bnodes_cons (trpl : triple I B L) (ts : seq (triple I B L)) :
      forall us : uniq (trpl :: ts),
        bnodes {| graph := trpl :: ts; ugraph := us |} = undup ((bnodes_triple trpl) ++ (bnodes {| graph := ts; ugraph := uniq_tail us |})).
    Proof. by rewrite /bnodes/= bnodes_ts_cons. Qed.

    Remark undup_bnodes g : undup (bnodes g) = bnodes g.
    Proof. exact: undup_idem. Qed.

    Lemma all_bnodes_ts ts : all (@is_bnode I B L) (bnodes_ts ts).
    Proof. elim: ts=> [// | t ts IHts].
           by rewrite bnodes_ts_cons all_undup all_cat IHts Bool.andb_true_r all_bnodes_triple_is_bnode.
    Qed.

    Lemma all_bnodes g : all (@is_bnode I B L) (bnodes g).
    Proof. by rewrite all_bnodes_ts. Qed.

    Lemma in_bnodes b g: b \in bnodes g -> is_bnode b.
    Proof. apply /allP. apply all_bnodes. Qed.

    Lemma b_in_bnode_is_bnode b g : bnodes g = [:: b] -> is_bnode b.
    Proof.
      move=> H; have : b \in bnodes g by rewrite H in_cons in_nil eq_refl.
      by apply in_bnodes.
    Qed.

    Lemma uniq_bnodes_ts ts : uniq (bnodes_ts ts).
    Proof. exact: undup_uniq. Qed.
    Hint Resolve uniq_bnodes_ts.

    Lemma uniq_bnodes g : uniq (bnodes g).
    Proof. exact: undup_uniq. Qed.
    Hint Resolve uniq_bnodes.

    Lemma i_in_bnodes_ts id ts: Iri id \in bnodes_ts ts = false.
    Proof. by rewrite /bnodes_ts -filter_undup mem_filter. Qed.

    Lemma l_in_bnodes_ts l ts: Lit l \in bnodes_ts ts = false.
    Proof. by rewrite /bnodes_ts -filter_undup mem_filter. Qed.

    Lemma i_in_bnodes id g: Iri id \in bnodes g = false.
    Proof. by rewrite /bnodes i_in_bnodes_ts. Qed.

    Lemma l_in_bnodes l g: Lit l \in bnodes g = false.
    Proof. by rewrite /bnodes l_in_bnodes_ts. Qed.

    Definition get_bts {i b l : eqType} (ts : seq (triple i b l)) : seq b :=
      get_bs (bnodes_ts ts).

    Definition get_b g : seq B :=
      get_bts g.

    Lemma bnode_memP (i b' l: eqType) (b : b') trms : Bnode b \in trms = (b \in @get_bs i b' l trms).
    Proof. elim: trms=> [//| h t' IHt].
           by case: h=> // ?; rewrite !in_cons IHt eqb_eq.
    Qed.

    Lemma bnode_memPn (i b' l: eqType) (b : b') trms : Bnode b \notin trms = (b \notin @get_bs i b' l trms).
    Proof. by rewrite /negb bnode_memP. Qed.

    Lemma get_bs_of_uniq (s : seq (term I B L)) : uniq s -> get_bs (undup s) = get_bs s.
    Proof. rewrite /get_bs. elim: s=> [//| h t IHl]; rewrite cons_uniq=> /andP[/eqP nin unt] /=.
           by case: (h \in t) nin => //; case: h=> x /= _; rewrite IHl.
      Qed.

    Lemma undup_get_bsC (s : seq (term I B L)) : uniq s -> (undup (get_bs s)) = get_bs s.
    Proof. elim: s=> [//| h t IHt].
           move=> /andP[nin unt] /=; case: h nin=> //= b; rewrite ?IHt //.
           by rewrite bnode_memPn /negb; case: (b \in get_bs t)=> //; by rewrite IHt.
    Qed.

    Lemma uniq_get_bs ts : uniq (get_bs (bnodes_ts ts)).
    Proof. by rewrite -(undup_get_bsC (uniq_bnodes_ts ts)) undup_uniq. Qed.
    Hint Resolve uniq_get_bs.

    Lemma uniq_get_bts ts : uniq (get_bts ts).
    Proof. by rewrite /get_b uniq_get_bs. Qed.
    Hint Resolve uniq_get_bts.

    Lemma uniq_get_b g : uniq (get_b g).
    Proof. by rewrite /get_b uniq_get_bs. Qed.
    Hint Resolve uniq_get_b.

    Lemma relabeling_triple_of_comp (B1 B2 B3: eqType)(mu : B2 -> B3) (nu : B1 -> B2):
      ((@relabeling_triple I L _ _ mu) \o (@relabeling_triple I L _ _ nu)) =1 (relabeling_triple (mu \o nu)).
    Proof. by move=> t; rewrite relabeling_triple_comp. Qed.

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

    Lemma bijective_eqb_rdf mu nu g1 g2 :
      forall us1 us2,
        cancel mu nu -> eqb_rdf (@relabeling _ _ mu g2 us1) g1 -> eqb_rdf g2 (@relabeling _ _ nu g1 us2).
    Proof.
      by move=> us1 us2 can_munu; rewrite /eqb_rdf/relabeling/=; apply bijective_perm_eq_relabeling_st.
    Qed.

    Remark id_bij T: bijective (@id T). Proof. by exists id. Qed.
    Hint Resolve id_bij.

    Section Isomorphism.

      Section PreIsomorphism.

        Definition is_pre_iso_ts ts1 ts2 (μ : B -> B) :=
          perm_eq (map μ (get_bts ts1)) (get_bts ts2).

        Definition is_pre_iso g1 g2 (μ : B -> B) :=
          is_pre_iso_ts g1 g2 μ.

        Lemma is_pre_iso_ts_trans ts1 ts2 ts3 m12 m23 :
          is_pre_iso_ts ts1 ts2 m12 -> is_pre_iso_ts ts2 ts3 m23 -> is_pre_iso_ts ts1 ts3 (m23 \o m12).
        Proof. rewrite /is_pre_iso=> /(perm_map m23); rewrite -map_comp=> pe12 pe23.
               by apply: perm_trans pe12 pe23.
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

        Definition pre_iso_ts ts1 ts2 := exists (μ : B -> B), is_pre_iso_ts ts1 ts2 μ.
        Definition pre_iso g1 g2 := exists (μ : B -> B), is_pre_iso_ts g1 g2 μ.

        Lemma pre_iso_ts_refl ts : pre_iso_ts ts ts.
        Proof. by rewrite /pre_iso_ts /is_pre_iso_ts; exists id; rewrite map_id perm_refl. Qed.

        Lemma pre_iso_refl g : pre_iso g g.
        Proof. by apply pre_iso_ts_refl; rewrite /pre_iso_ts /is_pre_iso_ts; exists id; rewrite map_id perm_refl. Qed.

        Lemma is_pre_iso_ts_inv ts1 ts2 mu : is_pre_iso_ts ts1 ts2 mu ->
                              exists nu, is_pre_iso_ts ts2 ts1 nu /\
                               map (nu \o mu) (get_bts ts1) = get_bts ts1.
        Proof.
        wlog dflt :/ B.
          move=> hwlog; rewrite /is_pre_iso_ts/get_b.
          case_eq (get_bts ts2) => [e |dflt l <-]; last by apply: hwlog.
          by move/perm_nilP/eqP; rewrite -size_eq0 size_map size_eq0; move/eqP->; exists id.
        rewrite /is_pre_iso_ts => mu_pre_iso.
        wlog map_mu:  mu {mu_pre_iso} / [seq mu i | i <- get_bts ts1] = get_bts ts2.
          move=> hwlog.
          have [rho rhoP] := map_of_seq [seq mu i | i <- get_bts ts1] (get_bts ts2) dflt.
          have {rhoP} rhoP : [seq (rho \o mu) i | i <- get_bts ts1] = get_bts ts2.
          rewrite -map_comp in rhoP; apply: rhoP; first by rewrite (perm_uniq mu_pre_iso).
            by rewrite (perm_size mu_pre_iso).
          have {hwlog} [tau [tauP1 tauP2]] := hwlog _ rhoP.
          exists (tau \o rho); split=> //.
          rewrite -tauP2 perm_sym.
          have:=  (perm_map (tau \o rho) mu_pre_iso).
          by rewrite -map_comp.
        have [nu nuP] := map_of_seq (get_bts ts2) (get_bts ts1) dflt.
        have  {nuP} nuP : [seq nu i | i <- get_bts ts2] = get_bts ts1.
          by apply: nuP=> //; rewrite -map_mu size_map.
        exists nu; split=> //.
        - rewrite nuP; exact: perm_refl.
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

        Lemma pre_iso_ts_trans ts1 ts2 ts3 : pre_iso_ts ts1 ts2 -> pre_iso_ts ts2 ts3 -> pre_iso_ts ts1 ts3.
        Proof. rewrite /pre_iso=> [[mu12 iso12] [mu23 iso23]].
               by exists (mu23 \o mu12); apply (is_pre_iso_ts_trans iso12 iso23).
        Qed.

        Lemma pre_iso_trans g1 g2 g3 : pre_iso g1 g2 -> pre_iso g2 g3 -> pre_iso g1 g3.
        Proof. by apply pre_iso_ts_trans. Qed.

      End PreIsomorphism.

      Definition is_iso_ts ts1 ts2 mu :=
        [&& is_pre_iso_ts ts1 ts2 mu,
          uniq (relabeling_seq_triple mu ts1) &
            perm_eq (relabeling_seq_triple mu ts1) ts2].

      Definition is_iso g1 g2 mu :=
        [&& is_pre_iso g1 g2 mu,
          uniq (relabeling_seq_triple mu g1) &
            perm_eq (relabeling_seq_triple mu g1) g2].

      Definition iso_ts ts1 ts2 := exists mu, @is_iso_ts ts1 ts2 mu.
      Definition iso g1 g2 := iso_ts g1 g2.
      (* exists mu, @is_iso g1 g2 mu. *)

      Remark is_iso_is_pre_iso g1 g2 mu: @is_iso g1 g2 mu -> is_pre_iso g1 g2 mu.
      Proof. by case/and3P. Qed.

      Definition iso_refl g : iso g g.
      Proof. exists id; rewrite /is_iso.
             case g=> g' ug /=.
             by rewrite /is_iso_ts relabeling_seq_triple_id ug  /= /is_pre_iso/is_pre_iso_ts map_id !perm_refl.
      Qed.

      Lemma eqb_rdf_terms g1 g2 : eqb_rdf g1 g2 -> perm_eq (terms g1) (terms g2).
      Proof. rewrite /eqb_rdf/terms=> peq.
             by rewrite perm_undup //; apply perm_mem; rewrite perm_flatten //; apply: perm_map peq.
      Qed.

      Lemma eqb_rdf_bnodes g1 g2 : eqb_rdf g1 g2 -> perm_eq (bnodes g1) (bnodes g2).
      Proof. move=> /eqb_rdf_terms eqb.
             by rewrite /bnodes perm_undup //; apply: perm_mem; apply: perm_filter.
      Qed.

      Lemma eqb_rdf_get_b g1 g2 : eqb_rdf g1 g2 -> perm_eq (get_b g1) (get_b g2).
      Proof. by move=> /eqb_rdf_bnodes eqb ; rewrite /get_b/get_bs; apply: perm_pmap eqb. Qed.

      Lemma terms_uniq g : uniq (terms g).
      Proof. by apply undup_uniq. Qed.

      Lemma bnodes_map_get_bs ts : bnodes_ts ts = map (fun b=> Bnode b) (get_bs (bnodes_ts ts)).
      Proof.
        (* have taut := (undup_uniq [seq x <- flatten [seq terms_triple i | i <- ts] | is_bnode x]). *)
        move: (all_bnodes_ts ts).
        rewrite /get_b/bnodes/bnodes_ts filter_undup // undup_idem -filter_undup.
        elim: [seq x <- undup (flatten [seq terms_triple i | i <- ts]) | is_bnode x]=> [//| []//=b t IHt] al.
        by rewrite -IHt.
      Qed.

      Lemma bnodes_map_get_b g : bnodes g = map (fun b=> Bnode b) (get_b g).
      Proof. by rewrite /bnodes -bnodes_map_get_bs. Qed.

      Lemma count_mem_bnodes b l: all (@is_bnode I B L) l -> count_mem b (get_bs l) = count_mem (Bnode b) l.
      Proof. elim: l=> [//|[]//b' t IHt] albn.
             by rewrite /= eqb_eq /eqb_term /= IHt.
      Qed.

      Lemma perm_eq_1s (b1 b2: B) : perm_eq [:: b1] [:: b2] = perm_eq [:: (@Bnode I B L b1)] [:: Bnode b2].
      Proof. by rewrite /perm_eq /= !eqb_eq /=. Qed.

      Lemma get_bs_map s mu: all (@is_bnode I B L) s -> (@get_bs I B L (map (relabeling_term mu) s)) = map mu (get_bs s).
      Proof. by elim: s=> [//| []//b t IHtl] /==> ? ; rewrite IHtl. Qed.

      Lemma map_rel_bnode s mu: all (@is_bnode I B L) s -> all (@is_bnode I B L) (map (relabeling_term mu) s).
      Proof. by elim: s=> [//| []//b t IHt]. Qed.

      Lemma all_bnodes_uniq_bs (i b l : eqType) s: all (@is_bnode i b l) s -> uniq (get_bs s) = uniq s.
      Proof. by elim: s=> [//| []//ab t IHt] alb; rewrite /= IHt // bnode_memPn. Qed.

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

      Lemma perm_relabel_bnodes g1 g2 mu :
        perm_eq (map (relabeling_term mu) (bnodes g1)) (bnodes g2) =
          perm_eq (map mu (get_b g1)) (get_b g2).
      Proof. by rewrite perm_relabel_bnodes_ts. Qed.

      Remark eqiso g1 g2 : eqb_rdf g1 g2 -> iso g1 g2.
      Proof.
        exists id.
        have usid: uniq (relabeling_seq_triple id g1) by rewrite relabeling_seq_triple_id; case g1.
        rewrite /is_iso/is_iso_ts usid /is_pre_iso/is_pre_iso_ts map_id relabeling_seq_triple_id /=; apply/andP; split=> //.
        - exact: eqb_rdf_get_b.
      Qed.

      Lemma map_of_triples t1 ft (f : B -> B): relabeling_term f (subject t1) = (subject ft) ->
                                                relabeling_term f (predicate t1) = predicate ft ->
                                                relabeling_term f (object t1) = object ft
                                                -> relabeling_triple f t1 = ft.
      Proof. by move=> rts rtp rto; apply triple_inj; rewrite -?rts -?rtp -?rto; case t1. Qed.

      Lemma is_pre_iso_ts_inj ts1 ts2 mu : is_pre_iso_ts ts1 ts2 mu -> {in get_bts ts1 &, injective mu}.
      Proof.
      move=> hmu b b' hb1 hb'.
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
        by move/permP: hmu<-.
      by rewrite count_uniq_mem //; case: (mu b \in get_bts ts2).
      Qed.

      Lemma is_pre_iso_inj g1 g2 mu : is_pre_iso g1 g2 mu -> {in get_b g1 &, injective mu}.
      Proof. by apply is_pre_iso_ts_inj. Qed.

      Lemma bnode_inj (i b l : eqType) : injective (fun bn=> @Bnode i b l bn).
      Proof. by move=> x y; case. Qed.
      Hint Resolve bnode_inj.

      Lemma is_pre_iso_ts_bnodes_inj ts1 ts2 mu : is_pre_iso_ts ts1 ts2 mu -> {in bnodes_ts ts1 &, injective (relabeling_term mu)}.
      Proof. move=> /is_pre_iso_ts_inj hmu []b // []b' //=;
             rewrite bnodes_map_get_bs !mem_map // => hb1 hb' []=> eq; rewrite ?eq //.
             by congr Bnode; apply hmu.
      Qed.

      Lemma is_pre_iso_bnodes_inj g1 g2 mu : is_pre_iso g1 g2 mu -> {in bnodes g1 &, injective (relabeling_term mu)}.
      Proof. by apply is_pre_iso_ts_bnodes_inj. Qed.

      Lemma undup_get_bs (s : seq (term I B L)) : (undup (get_bs s)) = (get_bs (undup s)).
      Proof. elim: s=> [//|h t IHts] /=.
             case e: (h \in t); first by move: e; case h=> //b; rewrite /= -IHts bnode_memP=> ->.
             by move: e; case h=> //b; rewrite /= -IHts bnode_memP=> ->.
      Qed.

      Lemma get_bs_cat (s1 s2: seq (term I B L)): get_bs s1 ++ get_bs s2 = get_bs (s1 ++ s2).
      Proof. by elim: s1 s2=> [//| []//=b t IHts] s2; rewrite IHts. Qed.

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

      Lemma perm_eq_bnodes_relabel_inj_in ts1 ts2 mu :
        {in (get_bs (bnodes_ts ts1))&, injective mu} ->
        perm_eq (get_bs (bnodes_ts (relabeling_seq_triple mu ts1))) (get_bs (bnodes_ts ts2)) ->
        perm_eq [seq mu i | i <- get_bs (bnodes_ts ts1)] (get_bs (bnodes_ts ts2)).
      Proof. by move=> inj /perm_eq_bnodes_relabel/perm_undup_map_inj ->. Qed.

      Lemma eqb_rdf_get_b_hom g1 g2 mu us :
        eqb_rdf (@relabeling _ _ mu g1 us) g2 -> perm_eq (undup (map mu (get_b g1))) (get_b g2).
      Proof.
        by move=> /eqb_rdf_get_b eqb ; rewrite /get_b/bnodes/relabeling (perm_eq_bnodes_relabel eqb).
      Qed.

      Lemma mem_get_bs_undup (s: seq (term I B L)) : get_bs (undup s) =i get_bs s.
      Proof. elim: s=> [//| h t IHts] x /=.
             case e: (h \in t).
             case: h e=> //= b.
             by rewrite IHts -(mem_undup (b :: get_bs t)) bnode_memP /==> ->; rewrite mem_undup.
             case: h e=> //= b.
             by rewrite -(mem_undup (b :: get_bs t)) bnode_memP /==> ->; rewrite !in_cons IHts mem_undup.
      Qed.

      Lemma uniq_rdf_graph g : uniq g. Proof. exact: ugraph. Qed.
      Hint Resolve uniq_rdf_graph.

      Lemma mem_triple_terms_ts t ts: t \in ts -> [&& (subject t) \in (terms_ts ts),
              ((predicate t) \in (terms_ts ts)) & ((object t) \in terms_ts ts)].
      Proof. case t=> s p o ? ? /=; elim: ts=> [//|hd tl IHts] /= t_mem.
             apply /and3P; rewrite !terms_ts_cons !mem_undup; move: t_mem; rewrite !in_cons /terms_triple !mem_cat; case/orP.
             + by move=> /eqP <-; rewrite !mem_undup !in_cons !eqxx /= !orbT.
             + by move=> /IHts /and3P[-> -> ->]; rewrite !orbT.
      Qed.

      Lemma mem_triple_terms t g: t \in g -> [&& (subject t) \in (terms g),
              ((predicate t) \in (terms g)) & ((object t) \in terms g)].
      Proof. by rewrite terms_graph; apply mem_triple_terms_ts. Qed.

      Lemma bterms_ts b ts : Bnode b \in (terms_ts ts) -> Bnode b \in (bnodes_ts ts).
      Proof. by move=> mem_term; rewrite mem_undup mem_filter. Qed.

      Lemma bterms b g: Bnode b \in (terms g) -> Bnode b \in (bnodes g).
      Proof. by rewrite terms_graph; apply bterms_ts. Qed.

      Lemma triple_case t1 t2: t1 = t2 -> [&& (subject t1) == (subject t2),
            (predicate t1) == (predicate t2) &
              (object t1) == (object t2)].
      Proof. by case t1; case t2=> /= ? ? ? ? ? ? ? ? ? ? [] -> -> ->; rewrite !eqxx. Qed.

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

      Lemma relabeling_term_inj_terms {B2 : eqType} (mu : B -> B2) g sx sy :
        {in get_b g &, injective mu} ->
        sx \in terms g -> sy \in terms g ->
                                relabeling_term mu sx = relabeling_term mu sy ->
                                sx = sy.
        Proof. apply relabeling_term_inj_terms_ts. Qed.

      Lemma is_pre_iso_inj_ts {B2: eqType} ts (mu : B -> B2) : ({in get_bts ts &, injective mu}) -> {in ts &, injective (relabeling_triple mu)}.
      Proof.
        move=> mu_inj; case=> sx ps ox ? ?; case=> sy py oy ? ? /= /mem_triple_terms_ts /= /and3P[memsx mempx memox] /mem_triple_terms_ts /= /and3P[memsy mempy memoy] [] eqs eqp eqo.
          by apply triple_inj=> /=; apply (relabeling_term_inj_terms_ts mu_inj)=> //.
      Qed.

      Lemma is_pre_iso_inj_g {B2: eqType} g (mu : B -> B2) : ({in get_b g &, injective mu}) -> {in g &, injective (relabeling_triple mu)}.
      Proof.
        move=> mu_inj; case=> sx ps ox ? ?; case=> sy py oy ? ? /= /mem_triple_terms /= /and3P[memsx mempx memox] /mem_triple_terms /= /and3P[memsy mempy memoy] [] eqs eqp eqo.
          by apply triple_inj=> /=; apply (relabeling_term_inj_terms mu_inj)=> //.
      Qed.

      Lemma eq_relabeling_triple (i l B1 B2 : eqType) (mu nu : B1 -> B2) : mu =1 nu -> (@relabeling_triple i l _ _ mu) =1 (relabeling_triple nu).
      Proof. by move=> feq [[]? []? []? ? ?]; apply /triple_inj=> //=; rewrite feq. Qed.

      Lemma eq_relabeling_seq_triple (B1 B2 : eqType) (mu nu : B1 -> B2) : mu =1 nu -> (relabeling_seq_triple mu) =1 (relabeling_seq_triple nu).
      Proof. by move=> feq; elim=> [//| h t IHtl]; rewrite /= (eq_relabeling_triple feq) IHtl. Qed.

      Lemma perm_eq_relab_uniq g1 g2 mu : perm_eq (relabeling_seq_triple mu g1) g2 -> perm_eq (relabeling_seq_triple mu g1) g2 /\ uniq (relabeling_seq_triple mu g1).
      Proof. by move=> peq; rewrite (perm_uniq peq) peq. Qed.

      Lemma map_comp_in_id g (mu nu: B -> B) : [seq (nu \o mu) i | i <- get_b g] = get_b g ->
                                              {in (get_b g), nu \o mu =1 id}.
      Proof. elim: (get_b g)=> [| h t IHtl]; first by move=> _ x; rewrite in_nil //.
             move=> [heq teq] x; rewrite in_cons; case e: (x == h)=> /=.
             + by move: e=> /eqP ->; rewrite heq.
             + apply IHtl; apply teq.
      Qed.

      Lemma bterm_eq_mem_get_bs (b: B) ts :
        (@Bnode I B L b) \in terms_ts ts ->
                             b \in get_bs (bnodes_ts ts).
      Proof. by move=> /bterms_ts; rewrite {1}bnodes_map_get_bs (mem_map  (@bnode_inj I B L)). Qed.

      Lemma bterm_eq_mem_get_b (b: B) g :
        (@Bnode I B L b) \in terms g ->
                             b \in get_b g.
      Proof. by rewrite terms_graph/get_b; apply bterm_eq_mem_get_bs. Qed.

      Lemma mem_ts_mem_triple_bs t ts b : t \in ts -> Bnode b \in bnodes_triple t -> b \in get_bs (bnodes_ts ts).
      Proof. move=> /mem_triple_terms_ts; case t=> [[]]s []p []o ? ? //= /and3P[sint pint oint];
                                              rewrite /bnodes_triple filter_undup mem_undup ?in_cons in_nil // Bool.orb_false_r=> /eqP[eq]; move: sint oint; rewrite ?eq=> sint oint; rewrite bterm_eq_mem_get_bs //.
             by move: eq=> /eqP; case/orP=> /eqP[->].
      Qed.

      Lemma mem_g_mem_triple_b t g b : t \in g -> Bnode b \in bnodes_triple t -> b \in get_b g.
      Proof. by apply mem_ts_mem_triple_bs. Qed.

      Lemma can_b_can_rtbs ts (mu nu: B -> B) : {in get_bs (bnodes_ts ts), nu \o mu =1 id} ->
                                             {in ts, [eta relabeling_triple (nu \o mu)] =1 id}.
      Proof. move=> /= in_getb [s p o sib pii] /mem_ts_mem_triple_bs ing /=; apply triple_inj=> /=.
             + case: s sib ing  => // b sib ing.
               by rewrite /= in_getb // ing // /bnodes_triple filter_undup mem_undup in_cons eqxx.
             + by case: p pii ing  => // b sib /mem_g_mem_triple_b inb /=.
             + case: o ing  => // b ing /=.
               by rewrite /= in_getb // ing // /bnodes_triple filter_undup mem_undup mem_filter -mem_rev in_cons eqxx.
      Qed.

      Lemma can_b_can_rtb g (mu nu: B -> B) : {in get_b g, nu \o mu =1 id} ->
                            {in g, [eta relabeling_triple (nu \o mu)] =1 id}.
      Proof. by apply can_b_can_rtbs. Qed.

      Definition iso_sym g1 g2 : iso g1 g2 <-> iso g2 g1.
      Proof.
        suffices imp h1 h2 : iso h1 h2 -> iso h2 h1 by split; exact: imp.
        case=> mu /and3P[pre_iso_mu uniq_relab perm_relab].
        move:(is_pre_iso_inv pre_iso_mu); rewrite /pre_iso/is_pre_iso; move=> [nu [pre_iso_nu /map_comp_in_id/can_b_can_rtb nuP]].
        exists nu.
        rewrite /is_iso/is_iso_ts pre_iso_nu.
        have /perm_eq_relab_uniq [-> ->] //: perm_eq (relabeling_seq_triple nu h2) h1.
        move: perm_relab; rewrite perm_sym=> /(perm_map (relabeling_triple nu))=> perm_relab.
        apply: perm_trans perm_relab _; rewrite relabeling_triple_map_comp map_id_in //.
      Qed.

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

      Lemma eqb_relabeling_comp g1 g2 g3 mu12 mu23:
        forall u1 u2 u3,
          eqb_rdf (@relabeling _ _ mu12 g1 u1) g2 ->
          eqb_rdf (@relabeling _ _ mu23 g2 u2) g3 ->
          eqb_rdf (@relabeling _ _ (mu23 \o mu12) g1 u3) g3.
      Proof. by move=> u1 u2 u3; apply perm_eq_comp. Qed.

      Definition iso_trans g1 g2 g3 : iso g1 g2 -> iso g2 g3 -> iso g1 g3.
      Proof. rewrite /iso/is_iso; move=> [mu12 /and3P[pre_iso12 urel12 perm12]] [mu23 /and3P[pre_iso23 urel23 perm23]].
             exists (mu23 \o mu12).
             suffices ucomp: uniq (relabeling_seq_triple (mu23 \o mu12) g1).
             apply /and3P; split=> //.
             + by apply: is_pre_iso_trans pre_iso12 pre_iso23.
             + by apply : eqb_relabeling_comp perm12 perm23.
             + rewrite -relabeling_seq_triple_comp /relabeling_seq_triple.
               have /eq_uniq -> //: size [seq relabeling_triple mu23 i | i <- [seq relabeling_triple mu12 i | i <- g1]] =
                             size (relabeling_seq_triple mu23 g2).
               by move: perm12=> /perm_size; rewrite !size_map.
               by apply eq_mem_map; apply perm_mem.
      Qed.

      Lemma uniq_relabeling_pre_iso mu (ts : seq (triple I B L)):
        uniq ts -> is_pre_iso_ts ts (relabeling_seq_triple mu ts) mu -> uniq (relabeling_seq_triple mu ts).
      Proof. by rewrite /is_pre_iso_ts=> uts /is_pre_iso_ts_inj/is_pre_iso_inj_ts ?; rewrite map_inj_in_uniq //. Qed.

      Lemma ts_pre_iso_iso ts mu (urel: uniq (relabeling_seq_triple mu ts)) :
        is_pre_iso_ts ts (relabeling_seq_triple mu ts) mu -> is_iso_ts ts (relabeling_seq_triple mu ts) mu.
      Proof. move=> pre_iso; rewrite /is_iso/is_iso_ts pre_iso urel /=; apply perm_refl. Qed.

      Definition isocanonical_mapping (M : rdf_graph I B L -> rdf_graph I B L) :=
        forall g, iso (M g) g /\
               (forall g1 g2, eqb_rdf (M g1) (M g2) <-> iso g1 g2).

      Definition mapping_is_iso_mapping (M : rdf_graph I B L -> rdf_graph I B L) := forall g, iso (M g) g.

      Definition dt_names_mapping (M : rdf_graph I B L -> rdf_graph I B L) := forall g1 g2,
          iso g1 g2 -> eqb_rdf (M g1) (M g2).

      (* forall g μ, {in (get_b g), bijective μ} -> M g == M (relabeling μ g). *)

      (* Definition dont_manipulate_names_mapping_idem (M : rdf_graph I B L -> rdf_graph I B L) (dnmn : dont_manipulate_names_mapping M) : forall g (μ : B -> B), (bijective μ) -> M (M g) = M g. *)

      (* Lemma iso_leads_canonical_mapping M (nmn : dt_names_mapping M) g1 g2 : *)
      (*   iso_mapping g1 g2 -> eqb_rdf (M g1) (M g2). *)
      (* Proof. rewrite /iso_mapping/is_iso_mapping; move=> [μ /andP [peq eqb]]. *)
      (*        suffices -> : M g2 = M (relabeling μ g2). by []. *)
      (*        apply /eqP; apply (nmn g2 μ bijmu). *)
      (* Qed. *)

      Lemma same_res_impl_iso_mapping M g1 g2 (iso_output : mapping_is_iso_mapping M) : eqb_rdf (M g1) (M g2) -> iso g1 g2.
      Proof.
        have isog1k1 : iso g1 (M g1). by rewrite iso_sym; apply iso_output.
        have isog2k2 : iso (M g2) g2. by apply iso_output.
        by move=> /eqiso peqm; apply: iso_trans (iso_trans isog1k1 peqm) isog2k2.
      Qed.

      Lemma isocanonical_mapping_dt_out_mapping M (iso_out: mapping_is_iso_mapping M) (dt: dt_names_mapping M) : isocanonical_mapping M.
      Proof.
        split; first by apply iso_out.
        split; last by apply dt.
        + by apply: same_res_impl_iso_mapping iso_out.
      Qed.



    End Isomorphism.

  End EqRdf.
  Section Relabeling_alt.
    Variables I B L : choiceType.
    Implicit Type g : rdf_graph I B L.
    Definition relabeling_alt {g} (mu : {ffun (seq_sub (bnodes g)) -> B}) g1 : rdf_graph I B L. Admitted.

  End Relabeling_alt.


  Definition code_ts (I B L : eqType) ts : (seq (triple I B L))%type :=
    ts.

  Definition decode_ts (I B L : eqType) (s: seq (triple I B L)) : option (seq (triple I B L)) :=
    Some s.

  Lemma pcancel_code_decode_ts (I B L : eqType): pcancel (@code_ts I B L) (@decode_ts I B L).
  Proof. by case. Qed.

  Definition ts_canChoiceMixin' (I B L : choiceType) := PcanChoiceMixin (@pcancel_code_decode_ts I B L).
  Definition ts_canCountMixin' (I B L : countType):= PcanCountMixin (@pcancel_code_decode_ts I B L).

  Canonical ts_choiceType (I B L: choiceType):= Eval hnf in ChoiceType (seq (triple I B L)) (@ts_canChoiceMixin' I B L).
  Canonical ts_countType (I B L: countType):= Eval hnf in CountType (seq (triple I B L)) (@ts_canCountMixin' I B L).

  Definition ts_canPOrderMixin (I B L: countType):= PcanPOrderMixin (@pickleK (ts_countType I B L)).
  Canonical ts_POrderType (I B L: countType):= Eval hnf in POrderType tt (seq (triple I B L)) (@ts_canPOrderMixin I B L).

  Definition rdf_canChoiceMixin' (I B L : choiceType) := PcanChoiceMixin (@pcancel_code_decode I B L).
  Definition rdf_canCountMixin' (I B L : countType):= PcanCountMixin (@pcancel_code_decode I B L).

  Canonical rdf_choiceType (I B L: choiceType):= Eval hnf in ChoiceType (rdf_graph I B L) (@rdf_canChoiceMixin' I B L).
  Canonical rdf_countType (I B L: countType):= Eval hnf in CountType (rdf_graph I B L) (@rdf_canCountMixin' I B L).

  Definition rdf_canPOrderMixin (I B L: countType):= PcanPOrderMixin (@pickleK (rdf_countType I B L)).
  Canonical rdf_POrderType (I B L: countType):= Eval hnf in POrderType tt (rdf_graph I B L) (@rdf_canPOrderMixin I B L).

  Section CountRdf.
    Variables I B L : countType.
    Implicit Type g : rdf_graph I B L.

    Lemma empty_min g : Order.max g (@empty_rdf_graph I B L) = g.
    Proof. by case: g=> g'; case: g'=> [//|h t] us; rewrite Order.POrderTheory.maxElt. Qed.

    (* assia : this requires rewriting relabeling function(. cf error message
The term "g1" has type "rdf_graph I B L" while it is expected to have type
 "rdf_graph I (seq_sub_finType (bnodes g1)) ?L" *)

    Fail Definition is_iso_alt g1 g2  (μ :  {ffun (seq_sub (bnodes g1)) -> B}) :=
      {in {set (seq_sub (bnodes g1))} , bijective μ} /\ g2 == (relabeling_alt μ g1).
    (* The term "μ" has type "{ffun seq_sub (bnodes g1) -> B}" while it is expected to have type *)
    (*   "{set seq_sub (bnodes g1)} -> ?rT". *)

    Fail Definition iso_alt g1 g2:= exists mu, @is_iso_alt g1 g2 mu.

    Section FinTypeRdf.
      Local Notation fbnode g := (seq_sub (bnodes g)).

      Variables (g' : rdf_graph I B L).

      Variables (bns : {set (seq_sub (bnodes g'))}) (b : term I B L).

      Search _ seq_sub.

      Definition p1 (A : {set (seq_sub (bnodes g'))}) : option (term I B L) :=
        if (enum A) is h :: tl then Some (ssval h) else None.

      Definition p2 (A : {set (seq_sub (bnodes g'))}) : option (term I B L) :=
        if (pickP (mem A)) is Pick x Ax then Some (ssval x) else None.

      Definition p3 (A : {set (seq_sub (bnodes g'))}) : option (seq_sub (bnodes g')) :=
        if (pickP (mem A)) is Pick x Ax then Some x else None.


      Lemma p3_mem A z : p3 A = Some z -> z \in A.
      Proof. by rewrite /p3; case: (pickP (mem A)) => // x Ax; case=> <-. Qed.

      Variable z : fbnode g'.
      Check ssval z : term I B L.

      (* Other option *)
      Check bnodes g'.
      (* membership function of list (bnodes g') has type (term I B L) -> bool. but
         (term I B L) is NOT a finite type so this fails: *)
      Fail Check [set x in (bnodes g')].
      (* but once we have a finite type, we can use this notation *)
      Variable l : seq (fbnode g').
      Check [set x in l].





      Check b \in (bnodes g').
      Check enum bns.
      Check partition.
      Fail Check b \in bns.
      Print rel.


      (* Definition term_of_bnode {g} (b : fbnodes g) : term I B L :=  *)


      (* Coercion {g} fbnodes g *)
      (* Maybe μ has type (subType (term I B L) (fun t => t \in g)) -> term I B L *)
      Definition mapping g (μ : fbnode g -> term I B L) := [ffun b : (fbnode g) => (μ b)]. 


      Variables (p : pred (term I B L))  (q : pred (fbnode g')).

      Definition A := [set x | q x]. (* seq_sub (bnodes g) is a fintype! *)
      Fail Check [set x in A | p x]. (* need to compose p with the coercion from 
(seq_sub (bnodes g)) to term I B L *)
      Check A : {set (fbnode g')}.


    End FinTypeRdf.

  End CountRdf.
End Rdf.

