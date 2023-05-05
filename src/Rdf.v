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
    Proof. by rewrite /eqb_rdf. Qed.

    Lemma eqb_rdf_sym g1 g2 : eqb_rdf g1 g2 = eqb_rdf g2 g1.
    Proof. by rewrite /eqb_rdf perm_sym. Qed.

    Lemma eqb_rdf_trans g1 g2 g3: eqb_rdf g1 g2 -> eqb_rdf g2 g3 -> eqb_rdf g1 g3.
    Proof. by rewrite /eqb_rdf; apply perm_trans. Qed.

    Canonical rdf_eqType (i b l : eqType):= EqType (rdf_graph i b l) (PcanEqMixin (@pcancel_code_decode i b l)).
    Canonical rdf_predType (i b l : eqType) := PredType (pred_of_seq \o (@graph i b l)).

    Remark eq_eqb_rdf g1 g2 : g1 == g2 -> eqb_rdf g1 g2.
    Proof. by move=> /eqP ->; rewrite eqb_rdf_refl. Qed.

    (* Variable g : rdf_graph I B L. *)
    (* Variable trm : term I B L. *)
    (* Variable t : triple I B L. *)
    (* Check trm \in t. *)
    (* Check t \in g. *)
    (* Print SetDef.finset. *)
    (* (* requieres trm to be finType *) *)
    (* Fail Check finset (trm \in g). *)

    Implicit Type t : triple I B L.
    Implicit Type ts : seq (triple I B L).

    Definition empty_rdf_graph {i b l : eqType} := @mkRdfGraph i b l [::] (eqxx true) : rdf_graph i b l.

    Definition is_ground g : bool :=
      all (@is_ground_triple _ _ _) g.

    Definition relabeling_seq_triple
      (B' B'': Type) (μ : B' -> B'')
      (ts : seq (triple I B' L)) : seq (triple _ B'' _) :=
      map (relabeling_triple μ) ts.

    Section Relabeling_seq_triple.
      Variable B' : Type.

      Lemma relabeling_seq_triple_ext (μ1 μ2 : B -> B') ts :
        μ1 =1 μ2 -> relabeling_seq_triple μ1 ts = relabeling_seq_triple μ2 ts.
      Proof. move=> mu_eq; apply: eq_map; exact: relabeling_triple_ext. Qed.

      Lemma relabeling_seq_triple_comp (B'' : eqType) (μ2 : B -> B') (μ1 : B' -> B'') ts :
        relabeling_seq_triple μ1 (relabeling_seq_triple μ2 ts) =
          relabeling_seq_triple (μ1 \o μ2) ts.
      Proof.
        rewrite /relabeling_seq_triple -map_comp -/relabeling_seq_triple; apply: eq_map=> x.
        by rewrite relabeling_triple_comp.
      Qed.

    End Relabeling_seq_triple.

    Lemma relabeling_seq_triple_id ts : relabeling_seq_triple id ts = ts.
    Proof. by elim ts => [//| t ts' ihts] /= ; rewrite relabeling_triple_id ihts.
    Qed.

    Definition relabeling
      (B' B'' : eqType) (μ : B' -> B'')
      (g : rdf_graph I B' L)  (urel : uniq (relabeling_seq_triple μ (graph g))): rdf_graph I B'' L:=
      mkRdfGraph urel.

    Lemma relabeling_triple_map_comp (B' B'': eqType) (g : seq (triple I B L)) (mu1: B -> B') (mu2 : B' -> B'') :
      [seq relabeling_triple mu2 i | i <- [seq relabeling_triple mu1 i | i <- g]] =
        [seq relabeling_triple (mu2 \o mu1) i | i <- g].
    Proof. by rewrite -map_comp; apply eq_map=> t /=; rewrite -relabeling_triple_comp. Qed.

    Lemma rdf_perm_mem_eq {i b l : eqType} (g1 g2 :rdf_graph i b l) :
      (perm_eq g1 g2) <-> (g1 =i g2).
    Proof. split; first by move=> /perm_mem.
           by move: (ugraph g1) (ugraph g2); apply uniq_perm=> //.
    Qed.

    Lemma rdf_mem_eq_graph g1 g2 :
      g1 =i g2 <-> (graph g1) =i (graph g2).
    Proof. by []. Qed.


    Lemma relabeling_comp (B' B'': eqType) g (μ1 : B -> B') (μ2: B' -> B'') :
      forall u1 u2 u12,
        perm_eq (@relabeling B' B'' μ2 (@relabeling B B' μ1 g u1) u2) (@relabeling B B'' (μ2 \o μ1) g u12).
    Proof. case g => g' ug' u1 u2 u12; rewrite rdf_perm_mem_eq /relabeling/relabeling_seq_triple=> x.
           suffices ->: [seq relabeling_triple μ2 i | i <- [seq relabeling_triple μ1 i | i <- g']] =i [seq relabeling_triple (μ2 \o μ1) i | i <- g'].
           by [].
           by move=> ? /=; rewrite relabeling_triple_map_comp.
    Qed.

    Section Relabeling_graph.

      Lemma relabeling_id g : forall us, (@relabeling B B id g us) = g.
      Proof. by case g => g' ug us ; apply rdf_inj=> /=; rewrite relabeling_seq_triple_id. Qed.

      Variable B' : eqType.

      Lemma relabeling_ext  (μ1 μ2 : B -> B') g :  μ1 =1 μ2 ->
                                                  forall u1 u2, @relabeling B B' μ1 g u1 = @relabeling B B' μ2 g u2.
      Proof. by move=> μpweq u1 u2; apply /rdf_inj; rewrite /= (relabeling_seq_triple_ext _ μpweq). Qed.

      Lemma relabeling_nil (B1 B2: eqType) (μ: B1 -> B2) :
        (* forall u1 u2, *)
        @relabeling B1 B2 μ empty_rdf_graph (eqxx true) = empty_rdf_graph.
      Proof. by apply rdf_inj. Qed.

      Lemma relabeling_cons (B1 B2 : eqType) (μ: B1 -> B2) (trpl : triple I B1 L) (ts : seq (triple I B1 L)) (ucons : uniq (trpl :: ts)) :
        forall us,
          @relabeling B1 B2 μ (mkRdfGraph ucons) us =
            mkRdfGraph (undup_uniq (relabeling_triple μ trpl :: (relabeling_seq_triple μ ts))).
      Proof. by move=> us; apply rdf_inj=> /=; move: us=> /andP[/negPf -> /undup_id ->]. Qed.

    End Relabeling_graph.
    (* Section Relabeling_graph_eq. *)

    (*   (* Lemma relabeling_mu_inv (g : rdf_graph I B L) (fs : seq (B -> B)) *) *)
    (*   (*   (mapping : rdf_graph I B L -> rdf_graph I B L) : *) *)
    (*   (*   (mapping g) \in (map (fun mu => relabeling mu g) fs) -> *) *)
    (*   (*                   exists (mu : B -> B), relabeling mu g == mapping g. *) *)
    (*   (* Proof. *) *)
    (*   (*   elim : fs => [| f fs' IHfs]; first by rewrite in_nil. *) *)
    (*   (*   rewrite in_cons; case/orP. *) *)
    (*   (*   + by rewrite eq_sym; exists f. *) *)
    (*   (*   + by move=> /IHfs //. *) *)
    (*   (* Qed. *) *)

    (* End Relabeling_graph_eq. *)

    Definition terms (I' B' L': eqType) (g : rdf_graph I' B' L') : seq (term I' B' L') :=
      undup (flatten (map (@terms_triple I' B' L') (graph g))).

    Lemma terms_graph (I' B' L': eqType) (g : rdf_graph I' B' L') :
      terms g = undup (flatten (map (@terms_triple I' B' L') (graph g))).
    Proof. by case g. Qed.

    Lemma undup_terms g : undup (terms g) = (terms g).
    Proof. by rewrite /terms undup_idem. Qed.

    Definition uniq_tail (T: eqType) a (t : seq T) : (uniq (a :: t)) -> uniq t.
    Proof. by move=> /andP[_ //]. Qed.

    Definition terms_cons (I' B' L': eqType) (trpl : triple I' B' L') (ts : seq (triple I' B' L')) (us : uniq (trpl :: ts)):
      terms (mkRdfGraph us) = undup (terms_triple trpl ++ (terms (mkRdfGraph (uniq_tail us)))).
    Proof. by rewrite /terms; case: ts us=>  [ // | ? ? ]; rewrite /= undup_cat_r. Qed.

    Section TermRelabeling.
      Variable B1 B2: eqType.

      (* Lemma terms_relabeled_mem (g : rdf_graph I B1 L) (mu: B1 -> B2) : *)
      (*   (@terms I B2 L (relabeling mu g)) =i undup (map (relabeling_term mu) (terms g)). *)
      (* Proof. Admitted. *)


      Lemma map_undup_idem (T1 T2: eqType) (f : T1 -> T2) (s : seq T1):
        map f (undup (undup s)) = map f (undup s).
      Proof. elim: s=> [//|h t IHts] /=.
             case e: (h \in t); first by rewrite IHts.
             by move: e; rewrite -mem_undup /= -IHts=> ->.
      Qed.

      Lemma relabeling_triple_inj (i l B' B'' : Type) (mu : B' -> B'') (inj_mu :injective mu) : injective (@relabeling_triple i l B' B'' mu).
      Proof.
        have inj_rtmu : injective (relabeling_term mu). by move=> ? ?; apply relabeling_term_inj.
        move=> x y; rewrite /relabeling_triple; case x; case y=> // ? ? ? ? ? ? ? ? ? ?.
        by move=> [] /inj_rtmu eq1 /inj_rtmu eq2 /inj_rtmu eq3; apply triple_inj.
      Qed.

      Lemma terms_relabeled (g : rdf_graph I B1 L) (mu: B1 -> B2) (inj_mu : injective mu):
        forall us,
          (@terms I B2 L (@relabeling B1 B2 mu g us)) = map (relabeling_term mu) (terms g).
      Proof.
        move: (@relabeling_triple_inj I L B1 B2 mu inj_mu) (@relabeling_term_inj I B1 B2 L mu inj_mu) => rts_inj rt_inj.
        elim g=> g'; elim g'=> [//|t ts IHts] us /= x.
        + have /andP[/negPf nin urt]: uniq (relabeling_triple mu t :: relabeling_seq_triple mu ts).
          by rewrite -map_cons map_inj_uniq //.
          rewrite relabeling_cons terms_graph /= nin terms_cons -(undup_map_inj rt_inj) -undup_cat_r.
          f_equal; rewrite map_cat=> /=. f_equal; first by apply terms_relabeled_triple.
          have ->: undup (flatten [seq terms_triple i | i <- undup (relabeling_seq_triple mu ts)]) = (terms (@relabeling B1 B2 mu {| graph := ts; ugraph := (uniq_tail us) |} urt)).
          by rewrite terms_graph /= (undup_id urt).
          by rewrite IHts.
      Qed.

    End TermRelabeling.

    Definition bnodes g : seq (term I B L) :=
      undup (filter (@is_bnode _ _ _) (terms g)).

    Section BnodeRelabeling.
      Variable B1 B2: eqType.

      (* Lemma bnodes_relabel_mem (g: rdf_graph I B L) (mu: B -> B) : *)
      (*   bnodes (relabeling mu g) =i (map (relabeling_term mu) (bnodes g)). *)
      (* Proof. Admitted. *)
      Lemma terms_relabeled_mem (B' B'' : eqType) (g : rdf_graph I B' L) (mu : B' -> B''):
          forall us,
            terms (@relabeling _ _ mu g us) =i [seq relabeling_term mu i | i <- terms g].
      Proof. move=> us x. rewrite /terms mem_undup -mem_map_undup; move: us.
             case g; elim=> [//| [s p o ? ?] tl IHtl] us0 usrel.
             move: (uniq_tail us0) (uniq_tail usrel)=> utl usreltl.
             rewrite map_cat mem_cat -mem_map_undup -IHtl // mem_cat /terms_triple.
             have ->: (x \in [seq relabeling_term mu i | i <- [:: s; p; o]]) =
                    (x \in undup [:: relabeling_term mu s; relabeling_term mu p; relabeling_term mu o]). by rewrite mem_undup.
             done.
      Qed.

      (* Lemma iri_not_bnode i mu ts : (Iri i \in [seq relabeling_term mu i | i <- ts & is_bnode i]) = false. *)

      Lemma mem_filter_map (T: eqType) f p a (s : seq T) : (forall b, p b = p (f b)) -> (a \in (map f (filter p s))) = (a \in filter p (map f s)).
      Proof. elim: s=> [//|h t IHts] pres.
             case e: (p h).
             by rewrite /= e; rewrite pres in e; rewrite e /= !in_cons IHts //.
             by rewrite /= e; rewrite pres in e; rewrite e /= IHts //.
      Qed.

      Lemma bnodes_relabel_mem (g: rdf_graph I B L) (mu: B -> B) :
        forall us,
          bnodes (@relabeling B B mu g us) =i (map (relabeling_term mu) (bnodes g)).
      Proof. move=> us. rewrite /relabeling/bnodes=> x /=. rewrite terms_graph /=.
             rewrite mem_undup. rewrite -mem_map_undup.
             have ->:
               forall (us : uniq (relabeling_seq_triple mu g)), undup (flatten [seq terms_triple i | i <- relabeling_seq_triple mu g]) = (terms (relabeling us)).
             by [].
             rewrite mem_filter terms_relabeled_mem.
             elim: (terms g)=> [|h t IHts]; first by rewrite /= in_nil Bool.andb_false_r.
             rewrite /= in_cons. case e: (is_bnode h).
             rewrite /= in_cons. case e2: (x == relabeling_term mu h).
             move: e2=> /eqP; move: e. by case h=> // b e ->.
             by rewrite -IHts.
             case e2: (x == relabeling_term mu h).
             move: e2=> /eqP; move: e. case h=> // b e ->. rewrite /=.
             rewrite mem_filter_map. by rewrite mem_filter.
             by case.
             rewrite mem_filter_map. by rewrite mem_filter.
             by case.
             done.
      Qed.

      Lemma bnodes_relabel (g: rdf_graph I B L) (mu: B -> B) (inj_mu : injective mu):
        forall us,
          bnodes (@relabeling B B mu g us) = (map (relabeling_term mu) (bnodes g)).
      Proof. move: (@relabeling_term_inj I B B L mu inj_mu) => inj_rtmu us.
             rewrite /bnodes terms_relabeled // -filter_undup undup_map_inj; last by apply inj_rtmu.
             rewrite -filter_undup.
             elim: (undup (terms g))=> [//| a l IHl] /=.
             have b_pres: forall (t : term I B L) b , (is_bnode t == b) = (is_bnode (relabeling_term mu t) == b).
             by case.
             by case e: (is_bnode a); move: e=> /eqP; rewrite b_pres=> /eqP ->; rewrite IHl.
      Qed.

    End BnodeRelabeling.

    Lemma bnodes_cons (trpl : triple I B L) (ts : seq (triple I B L)) :
      forall us : uniq (trpl :: ts),
        bnodes {| graph := trpl :: ts; ugraph := us |} = undup ((bnodes_triple trpl) ++ (bnodes {| graph := ts; ugraph := uniq_tail us |})).
    Proof.
      elim: ts trpl => [| h ts' IHts]=> trpl; rewrite /bnodes/bnodes_triple.
      + by rewrite /terms /= !cats0 filter_undup undup_idem.
      + by move=> ?; rewrite terms_cons filter_undup undup_idem undup_cat_r filter_cat.
    Qed.

    Remark undup_bnodes g : undup (bnodes g) = bnodes g.
    Proof. by rewrite /bnodes undup_idem. Qed.

    Lemma all_bnodes g : all (@is_bnode I B L) (bnodes g).
      case: g=> g'; elim: g' => [//| t ts IHts] us.
      rewrite bnodes_cons all_undup all_cat IHts Bool.andb_true_r.
      exact: all_bnodes_triple_is_bnode.
    Qed.

    Lemma b_in_bnode_is_bnode b g : bnodes g = [:: b] -> is_bnode b.
    Proof.
      move=> H; have binb : b \in bnodes g. by rewrite H in_cons in_nil eq_refl.
      rewrite /bnodes -filter_undup mem_filter in binb.
      by case: (is_bnode b) binb.
    Qed.

    Lemma uniq_bnodes g : uniq (bnodes g).
    Proof. exact: undup_uniq. Qed.

    Lemma in_bnodes b g: b \in bnodes g -> is_bnode b.
    Proof. apply /allP. apply all_bnodes. Qed.


    Lemma i_in_bnodes id g: Iri id \in bnodes g = false.
    Proof. by rewrite /bnodes -filter_undup mem_filter. Qed.

    Lemma l_in_bnodes l g: Lit l \in bnodes g = false.
    Proof. by rewrite /bnodes -filter_undup mem_filter. Qed.

    Definition get_b g : seq B :=
      undup (get_bs (bnodes g)).

    Lemma relabeling_triple_of_comp (B1 B2 B3: eqType)(mu : B2 -> B3) (nu : B1 -> B2):
      ((@relabeling_triple I L _ _ mu) \o (@relabeling_triple I L _ _ nu)) =1 (relabeling_triple (mu \o nu)).
    Proof. by move=> t; rewrite relabeling_triple_comp. Qed.

  (*   Lemma relabeling_seq_triple_of_comp (B1 B2 B3: eqType) (mu : B2 -> B3) (nu : B1 -> B2) : *)
  (*     (relabeling_triple mu23) \o (relabeling_triple mu12) i | i <- g'] = *)
  (* relabeling_seq_triple (mu23 \o mu12) g' *)
    Lemma bijective_eqb_rdf mu nu g1 g2 :
      forall us1 us2,
        cancel mu nu -> eqb_rdf g1 (@relabeling _ _ mu g2 us1) -> eqb_rdf g2 (@relabeling _ _ nu g1 us2).
    Proof.
      move=> us1 us2.
      rewrite /eqb_rdf=> cancel_mu_nu /perm_map=> /(_ (triple_eqType I B L) (relabeling_triple nu)).
      suffices : undup [seq relabeling_triple nu i | i <- (@relabeling _ _ mu g2 us1)] = g2.
      rewrite perm_sym=> <- /perm_mem peq.
      apply uniq_perm=> //.
      + apply undup_uniq.
      + by move=> x; rewrite mem_undup.
        (* + move=> x; rewrite mem_undup peq /= mem_undup. *)
        (* move=> urmu. *)
        have-> : [seq relabeling_triple nu i | i <- (@relabeling _ _ mu g2 us1)] = relabeling_seq_triple (nu \o mu) g2.
      - rewrite /relabeling_seq_triple. case: g2 us1=> g2'. elim : g2' => [//| a t IHtl] us.
        move : (can_inj cancel_mu_nu) => /relabeling_triple_inj=> /(_ I L) mu_inj us1.
        have : (relabeling_triple mu a \in relabeling_seq_triple mu t) = false.
        rewrite mem_map //. move: us us1=> /andP[/negPf nin //] //.
        (* //; last by apply mu_inj. *)
        rewrite /= relabeling_triple_comp=> e /=. rewrite -IHtl.
        apply (uniq_tail us).
        move=> ?. apply (uniq_tail us1).
        done.
        have /relabeling_seq_triple_ext numu_id : nu \o mu =1 id by [].
        rewrite numu_id undup_id.
        by rewrite relabeling_seq_triple_id.
        by rewrite relabeling_seq_triple_id; case g2=> ? u //.
    Qed.

    Remark id_bij T: bijective (@id T). Proof. by exists id. Qed.
    Hint Resolve id_bij.

    Section IsoMapping.

      Section PreIso.

        Definition is_pre_iso g1 g2 (μ : B -> B) := perm_eq (map μ (get_b g1)) (get_b g2).

        Lemma is_pre_iso_trans g1 g2 g3 m12 m23 :
          is_pre_iso g1 g2 m12 -> is_pre_iso g2 g3 m23 -> is_pre_iso g1 g3 (m23 \o m12).
        Proof. rewrite /is_pre_iso=> /(perm_map m23); rewrite -map_comp=> pe12 pe23.
               by apply: perm_trans pe12 pe23.
        Qed.

        Definition pre_iso g1 g2 := exists (μ : B -> B), is_pre_iso g1 g2 μ.

        Lemma pre_iso_refl g : pre_iso g g.
        Proof. by rewrite /pre_iso /is_pre_iso; exists id; rewrite map_id perm_refl. Qed.

        Lemma pre_iso_sym gg1 gg2 : pre_iso gg1 gg2 <-> pre_iso gg2 gg1.
        Proof. Admitted.

        Lemma pre_iso_trans g1 g2 g3 : pre_iso g1 g2 -> pre_iso g2 g3 -> pre_iso g1 g3.
        Proof. rewrite /pre_iso=> [[mu12 iso12] [mu23 iso23]].
               by exists (mu23 \o mu12); apply (is_pre_iso_trans iso12 iso23).
        Qed.

      End PreIso.

      Definition is_iso_mapping_old g1 g2 mu us :=
        is_pre_iso g1 g2 mu &&
          eqb_rdf (@relabeling _ _ mu g1 us) g2.

      Definition is_iso_mapping g1 g2 mu :=
        [&& is_pre_iso g1 g2 mu,
          uniq (relabeling_seq_triple mu g1) & 
          perm_eq (relabeling_seq_triple mu g1) g2].

      
      Definition iso_mapping g1 g2 := exists mu, @is_iso_mapping g1 g2 mu.

      Remark is_iso_is_pre_iso g1 g2 mu: @is_iso_mapping g1 g2 mu -> is_pre_iso g1 g2 mu.
      Proof. by case/and3P. Qed.

      Definition iso_mapping_refl g : iso_mapping g g.
      Proof.
      exists id; rewrite /is_iso_mapping.
      case g=> g' ug /=.
      by rewrite relabeling_seq_triple_id ug  /= /is_pre_iso  map_id !perm_refl.
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
      Proof. move=> /eqb_rdf_bnodes eqb ; rewrite /get_b/get_bs.
             by apply perm_undup; apply perm_mem; apply : perm_pmap eqb.
      Qed.

      Lemma get_bs_of_uniq (s : seq (term I B L)) : uniq s -> get_bs (undup s) = get_bs s.
      Proof. rewrite /get_bs. elim: s=> [//| h t IHl]; rewrite cons_uniq=> /andP[/eqP nin unt] /=.
             by case: (h \in t) nin => //; case: h=> x /= _; rewrite IHl.
      Qed.

      Lemma terms_uniq g : uniq (terms g).
      Proof. by apply undup_uniq. Qed.

      Lemma bnode_mem_filter b trms : Bnode b \notin trms -> (b \notin @get_bs I B L [seq x <- trms | is_bnode x]).
      Proof. elim: trms=> [//| h t' IHt].
             case: h=> // b'.
             rewrite in_cons negb_or=> /andP [/negP ].
             have hd : ~ Bnode b == Bnode b' -> negb (b == b').
             by move=> ? ?; apply contraPneq=> -> //.
             rewrite in_cons negb_or => neqb nint. apply /andP; split; last by apply IHt.
             apply (hd _ _ neqb).
      Qed.

      Definition eqb_term (t1 t2: term I B L) : bool :=
        match t1, t2 with
        | Lit l1,Lit l2 => l1 == l2
        | Bnode b1, Bnode b2=> b1 == b2
        | Iri i1, Iri i2 => i1 == i2
        | _,_ => false
        end.

      Lemma eqb_eq trm1 trm2 : eqb_term trm1 trm2 = (trm1 == trm2).
      Proof. Admitted.

      Lemma bnode_memP b trms : Bnode b \in trms = (b \in @get_bs I B L trms).
      Proof. elim: trms=> [//| h t' IHt].
             by case: h=> // b'; rewrite !in_cons IHt -eqb_eq.
      Qed.

      Lemma bnode_memPn b trms : Bnode b \notin trms = (b \notin @get_bs I B L trms).
      Proof. by rewrite /negb bnode_memP. Qed.

      Lemma get_bs_uniq g : uniq (get_bs (bnodes g)).
      Proof. rewrite /bnodes. move: (terms_uniq g).
             elim: (terms g)=> [//| h t IHl] /==> /andP [nin unt].
             rewrite /=. case e: (is_bnode h); last by apply IHl.
             rewrite -cat1s undup_cat /=.
             rewrite mem_filter negb_and nin Bool.orb_true_r.
             case: h e nin=> // x /= _.
             rewrite IHl // get_bs_of_uniq.
             move=> H; rewrite Bool.andb_true_r.
             by apply: bnode_mem_filter H.
             by apply filter_uniq.
      Qed.

      Lemma undup_get_bsC (s : seq (term I B L)) : uniq s -> (undup (get_bs s)) = get_bs s.
      Proof. elim: s=> [//| h t IHt].
             move=> /andP[nin unt].
             rewrite /=. case: h nin=> // b /=.
             + by rewrite IHt.
             + by rewrite IHt.
               rewrite bnode_memPn /negb.
               case: (b \in get_bs t)=> //; by rewrite IHt.
      Qed.

      Lemma bnodes_map_get_b g : bnodes g = map (fun b=> Bnode b) (get_b g).
      Proof. rewrite /get_b. move: (all_bnodes g); rewrite undup_get_bsC. elim: (bnodes g)=> [//| h t IHl].
             case: h=> // b /= H. by rewrite {1}IHl.
             apply uniq_bnodes.
      Qed.

      Lemma count_mem_bnodes b l: all (@is_bnode I B L) l -> count_mem b (get_bs l) = count_mem (Bnode b) l.
      Proof. elim: l=> [//|[//|//|//]b' t IHt] albn.
             by rewrite /= -eqb_eq /eqb_term /= IHt.
      Qed.

      Lemma perm_eq_1s (b1 b2: B) : perm_eq [:: b1] [:: b2] = perm_eq [:: (@Bnode I B L b1)] [:: Bnode b2].
      Proof. by rewrite /perm_eq /= -!eqb_eq /=. Qed.

      Lemma get_bs_map s mu: all (@is_bnode I B L) s -> (@get_bs I B L (map (relabeling_term mu) s)) = map mu (get_bs s).
      Proof. by elim: s=> [//| [//|//|//]b t IHtl] /==> ? ; rewrite IHtl. Qed.

      Lemma map_rel_bnode s mu: all (@is_bnode I B L) s -> all (@is_bnode I B L) (map (relabeling_term mu) s).
      Proof. by elim: s=> [//| [//|//|//] b t IHt]. Qed.

      Lemma perm_relabel_bnodes g1 g2 mu :
        perm_eq (map (relabeling_term mu) (bnodes g1)) (bnodes g2) =
          perm_eq (map mu (get_b g1)) (get_b g2).
      Proof. rewrite /get_b. move: (uniq_bnodes g1) (uniq_bnodes g2) (all_bnodes g1) (all_bnodes g2)=> unb1 unb2 alb1 alb2.
             rewrite !undup_get_bsC // -get_bs_map //.
             case e : (perm_eq [seq relabeling_term mu i | i <- bnodes g1] (bnodes g2)).
             have H: uniq [seq relabeling_term mu i | i <- bnodes g1] = uniq (bnodes g2).
             by apply perm_uniq; rewrite e.
             rewrite !uniq_perm //.
             rewrite -undup_get_bsC. rewrite undup_uniq //.
             by rewrite H.
             apply get_bs_uniq.
             move=> x.
             rewrite -!bnode_memP.
             by apply perm_mem.
             apply /eqP; rewrite eq_sym; apply /eqP.
             eapply contra_notF.
             have P :  perm_eq (get_bs [seq relabeling_term mu i | i <- bnodes g1]) (get_bs (bnodes g2)) ->perm_eq [seq relabeling_term mu i | i <- bnodes g1] (bnodes g2).
             move=> contr.
             have H: uniq (get_bs [seq relabeling_term mu i | i <- bnodes g1]) = uniq (get_bs (bnodes g2)).
             by apply perm_uniq.
             apply uniq_perm=> //.
             have H2 : forall s, all (@is_bnode I B L) s -> uniq (get_bs s) = uniq s.
             elim => [//| [//|//|//]b t IHt] alb; by rewrite /= IHt // bnode_memPn.
             rewrite -H2 //. by rewrite H get_bs_uniq.
             by apply map_rel_bnode.
             move=> x. case x=> // b /=.
             rewrite i_in_bnodes.
             apply (map_rel_bnode mu) in alb1.
             have F: Iri b \in [seq relabeling_term mu i | i <- bnodes g1] -> negb (all (is_bnode (L:=L)) [seq relabeling_term mu i | i <- bnodes g1]).
             move=> contra2.
             apply /allPn; exists (Iri b)=> //.
             apply (contra_notF F). rewrite alb1 //.
             rewrite l_in_bnodes.
             apply (map_rel_bnode mu) in alb1.
             have F: Lit b \in [seq relabeling_term mu i | i <- bnodes g1] -> negb (all (is_bnode (L:=L)) [seq relabeling_term mu i | i <- bnodes g1]).
             move=> contra2.
             apply /allPn; exists (Lit b)=> //.
             apply (contra_notF F). rewrite alb1 //.
             rewrite !bnode_memP.
             by apply perm_mem in contr.
             apply P.
             by rewrite e.
      Qed.

      Remark eqiso_mapping g1 g2 : eqb_rdf g1 g2 -> iso_mapping g1 g2.
      Proof.
        exists id.
        have usid: uniq (relabeling_seq_triple id g1) by rewrite relabeling_seq_triple_id; case g1.
        rewrite /is_iso_mapping usid /is_pre_iso map_id relabeling_seq_triple_id /=; apply/andP; split.
        - exact: eqb_rdf_get_b.
        - exact: H.
      Qed.

      Lemma eqb_rdf_relabeling_inv g1 g2 mu :
        forall us,
          eqb_rdf (@relabeling _ _ mu g1 us) g2 -> {in (get_b g1) &, injective mu} -> exists nu us2, eqb_rdf (@relabeling _ _ nu g2 us2) g1.
      Proof.
      Admitted.

      Lemma is_pre_iso_inj g1 g2 mu : is_pre_iso g1 g2 mu -> {in get_b g1 &, injective mu}.
      Proof. Admitted.

      Lemma bnode_inj (i b l : eqType) : injective (fun bn=> @Bnode i b l bn).
        Proof. by move=> x y; case. Qed.

      Lemma is_pre_iso_bnodes_inj g1 g2 mu : is_pre_iso g1 g2 mu -> {in bnodes g1 &, injective (relabeling_term mu)}.
      Proof. move=> /is_pre_iso_inj hmu []b // []b' // /=; move: (@bnode_inj I B L)=> binj.
             rewrite bnodes_map_get_b !mem_map // => {binj} hb1 hb' [].
             by move=> eq; congr Bnode;  apply hmu.
      Qed.

      Lemma perm_map_cancel (T1 T2: eqType) (s : seq T1) (f: T1 -> T2) (g: T2 -> T1) :
        cancel f g -> perm_eq (map (g \o f) s) s.
      Proof. move=> can. elim: s=>[//| h t IHts] /=. by rewrite can perm_cons IHts. Qed.

      Lemma perm_map_in_cancel (T: eqType) (s : seq T) (f g: T -> T) :
        {in s, cancel f g} -> perm_eq (map (g \o f) s) s.
      Proof. elim: s=>[//| h t IHts] /=.
             move=> can. rewrite can. rewrite perm_cons IHts //.
             move=> x y. rewrite can //. by rewrite in_cons y orbT. by rewrite in_cons eqxx.
      Qed.

      Lemma perm_undup_map_inj (T1 T2: eqType) (f : T1 -> T2) s1 s2 :
        {in s1 &,injective f} ->  uniq s1 -> perm_eq (undup (map f s1)) s2 -> perm_eq (map f s1) s2.
      Proof. move=> injf us1 peq.
             have equ: uniq (undup (map f s1)) = uniq (map f s1).
             by rewrite map_inj_in_uniq // undup_uniq.
             have eq: perm_eq (map f s1) (undup (map f s1)).
             apply uniq_perm.
             + by rewrite -equ undup_uniq.
             + by rewrite undup_uniq.
             + by move=> x; rewrite mem_undup.
             by apply: perm_trans eq peq.
      Qed.

      Lemma undup_get_bs (s : seq (term I B L)) : (undup (get_bs s)) = (get_bs (undup s)).
      Proof. elim: s=> [//|h t IHts] /=.
             case e: (h \in t); first by move: e; case h=> //b; rewrite /= -IHts bnode_memP=> ->.
             by move: e; case h=> //b; rewrite /= -IHts bnode_memP=> ->.
      Qed.

      Lemma get_bs_cat (s1 s2: seq (term I B L)): get_bs s1 ++ get_bs s2 = get_bs (s1 ++ s2).
      Proof. elim: s1 s2=> [//| h t IHts] s2.
             by case h=> //b /=; rewrite IHts.
      Qed.

      Lemma eqb_rdf_get_b_hom g1 g2 mu us :
        eqb_rdf (@relabeling _ _ mu g1 us) g2 -> perm_eq (undup (map mu (get_b g1))) (get_b g2).
      Proof. move=> /eqb_rdf_get_b; rewrite /relabeling/=/relabeling_seq_triple/get_b/==> peq_b.
             apply uniq_perm. by apply undup_uniq. apply undup_uniq.
             move: peq_b=> /perm_mem peqb.
             move=> x. rewrite mem_undup -peqb mem_undup -mem_map_undup.
             move {peqb g2}.
             case: g1 us; elim=> [//| h t IHts].
             move=> ug urg; rewrite /= !bnodes_cons.
             rewrite -!undup_get_bs mem_undup -mem_map_undup -!get_bs_cat map_cat !mem_cat /= IHts.
             by apply uniq_tail in urg.
             move=> tmp; f_equal; move {tmp ug urg}.
             case: h; case=> // a; case=> // b; case=> // c ? ?;
                                                      rewrite /bnodes_triple/terms_triple ?filter_undup //.
             have ->:  [seq x <- [:: relabeling_term mu (Bnode a); relabeling_term mu (Iri b);
                            relabeling_term mu (Bnode c)]
                       | is_bnode x] = [:: (Bnode (mu a)); (Bnode (mu c))].
             by [].
             rewrite /= in_cons in_nil.
             case e: (a == c).
             have ->: (Bnode a) = (Bnode c).
             by move=> ? ?; congr Bnode; apply /eqP.
             rewrite /= !in_cons !in_nil.
             have ->: (Bnode (mu a)) = (Bnode (mu c)).
             by move=> ? ?; congr Bnode; congr mu; apply /eqP.
             by rewrite !eqxx.

             rewrite in_cons in_nil /=.
             case e2: ((mu a) == (mu c)).
             have eq: (mu a) = (mu c). by apply /eqP.
             have ->: Bnode a == Bnode c = false.
             by move=> ? ?; rewrite /eq_op /= /eq_op /= /eq_op /= /eq_op /= /eq_op /= /eq_op /= e.
             rewrite eq !eqxx /= eq !in_cons !in_nil.
             by case: (x == mu c).
             have ->: Bnode a == Bnode c = false.
             by move=> ? ?; rewrite /eq_op /= /eq_op /= /eq_op /= /eq_op /= /eq_op /= /eq_op /= e.
             have ->: Bnode (mu a) == Bnode (mu c) = false.
             by move=> ? ?; rewrite /eq_op /= /eq_op /= /eq_op /= /eq_op /= /eq_op /= /eq_op /= e2.
             by rewrite !in_cons in_nil.
      Qed.

      Lemma mem_get_bs_undup (s: seq (term I B L)) : get_bs (undup s) =i get_bs s.
      Proof. elim: s=> [//| h t IHts] x.
             rewrite /=.
             case e: (h \in t).
             case: h e=> // b /=.
             by rewrite IHts -(mem_undup (b :: get_bs t)) bnode_memP /==> ->; rewrite mem_undup.
             case: h e=> // b /=.
             by rewrite -(mem_undup (b :: get_bs t)) bnode_memP /==> ->; rewrite !in_cons IHts mem_undup.
      Qed.

      Lemma is_pre_iso_inv g1 g2 mu : is_pre_iso g1 g2 mu -> exists nu, is_pre_iso g2 g1 nu.
      Proof. move=> ipiso.
             have /pre_iso_sym [nu nuP]: pre_iso g1 g2. by exists mu.
                                                             by exists nu.
      Qed.

      Lemma uniq_rdf_graph g : uniq g. Proof. exact: ugraph. Qed.
      Hint Resolve uniq_rdf_graph.

      Definition iso_mapping_sym g1 g2 : iso_mapping g1 g2 <-> iso_mapping g2 g1.
      Proof.
        suffices imp h1 h2 : iso_mapping h1 h2 -> iso_mapping h2 h1 by split; exact: imp.
        case=> mu /and3P[] pre_iso_mu uniq_relab perm_relab. 
        have [nu nuP]: pre_iso h2 h1 by apply: (is_pre_iso_inv pre_iso_mu).
        exists nu.
        have inj_nu : {in h2 &, injective (relabeling_triple nu)}.
          rewrite /is_pre_iso in nuP. move=> x y h2x h2y heq. 
          (* f : A -> B and suppose: *)
          (*     - A = A1 |_| A2 *)
          (*     - f (A1) is disjoint from f (A2) *)
          (*     - f is inj on A1 and f is injective on A2                  *)
          (*     => f is injective on A *)
          have eqs : relabeling_term nu (subject x) = relabeling_term nu (subject y). by admit.
          have eqo : relabeling_term nu (object x) = relabeling_term nu (object y). by admit.
          have eqp : relabeling_term nu (predicate x) = relabeling_term nu (predicate y). by admit.
          case: x h2x heq eqs eqo eqp => sx px ox /= ? ? h2x heq eqs eqo eqp.
          case: y h2y heq eqs eqo eqp => sy py oy /= ? ? h2y heq eqs eqo eqp.
          apply: triple_inj => /=; admit.
        apply/and3P; split=> //.
        - by rewrite map_inj_in_uniq. 
        - rewrite /is_pre_iso in nuP.
          have aux : perm_eq (relabeling_seq_triple nu h2) (relabeling_seq_triple nu (relabeling_seq_triple mu h1)).
            by apply: perm_map; rewrite perm_sym.
          apply: perm_trans aux _.
          rewrite relabeling_seq_triple_comp.
          apply uniq_perm=> //.
Search perm_eq uniq.
          
          Search _ perm_eq map.
        case=> us; rewrite /iso_mapping/is_iso_mapping=> /andP[peqb eqb].
        have [nu nuP]: pre_iso h2 h1.
        by apply (is_pre_iso_inv peqb).
        have can_munu: {in (get_b h1), cancel mu nu}.
        admit.
        move: (is_pre_iso_inj nuP)=> nu_inj.
        have /(_ B _ _ nu_inj) inj_b_inj_relt : forall g mu, {in (get_b g)&, injective mu} -> {in g&, injective (relabeling_triple mu)}.
        move=> ?.
        case; elim=> [//| h t IHts] us' mu'.
        admit.
        have unu: uniq (relabeling_seq_triple nu h2).
        by rewrite map_inj_in_uniq // ugraph.
        exists nu. exists unu.
        rewrite nuP /=.
        move: eqb; rewrite /relabeling/eqb_rdf perm_sym /==> eqb.
        apply (perm_map (relabeling_triple nu)) in eqb.
        apply (perm_trans eqb).
        rewrite -map_comp; move {us peqb nuP eqb}.
        case: h1 can_munu; elim=> [//| h t IHts] us can_munu.
        rewrite /= -relabeling_triple_comp.
        have ->: relabeling_triple (nu \o mu) h = h.
        by case: h us can_munu; case=> //a; case=> //b; case=> //c /= ? ? us can_munu; apply /triple_inj=> // /=; rewrite can_munu // /get_b mem_undup bnodes_cons mem_get_bs_undup -get_bs_cat /bnodes_triple filter_undup mem_cat mem_get_bs_undup /= ?in_cons ?eqxx ?orbT.
        move: (uniq_tail us)=> ust.
        rewrite perm_cons IHts //.
        move=> x xin ; rewrite can_munu //; move: xin.
        by rewrite /get_b bnodes_cons !mem_undup mem_get_bs_undup -get_bs_cat mem_cat=> ->; rewrite orbT.
      Admitted.

      Lemma relabeling_triple_comp_map (B1 B2 B3 : eqType) (g : rdf_graph I B1 L) (mu12 : B1 -> B2) (mu23 : B2 -> B3) :
        [seq relabeling_triple mu23 i | i <- relabeling_seq_triple mu12 g] =
          relabeling_seq_triple (mu23 \o mu12) g.
        Proof. case g=> g' us=> /=; rewrite -map_comp /= /relabeling_seq_triple.
               by elim g'=> [//| h t IHts] /=; last by rewrite relabeling_triple_comp -IHts.
        Qed.

      Lemma eqb_relabeling_comp g1 g2 g3 mu12 mu23:
        forall u1 u2 u3,
        eqb_rdf (@relabeling _ _ mu12 g1 u1) g2 ->
        eqb_rdf (@relabeling _ _ mu23 g2 u2) g3 ->

        eqb_rdf (@relabeling _ _ (mu23 \o mu12) g1 u3) g3.
      Proof. move=> u1 u2 u3; rewrite /eqb_rdf/relabeling=> /(perm_map (relabeling_triple mu23)) p12 p23.
             suffices : [seq relabeling_triple mu23 i | i <- {| graph := relabeling_seq_triple mu12 g1 |}] =
                          {| graph := relabeling_seq_triple (mu23 \o mu12) g1 |}.

             move=> a. eapply (perm_trans _ p23). Unshelve. move=> i1 i2 /=.
             apply relabeling_triple_comp_map.
             rewrite /=. rewrite /= in p12.
             apply uniq_perm=> //.
             apply perm_mem in p12.
             by rewrite -relabeling_triple_comp_map.
      Qed.

      Definition iso_mapping_trans g1 g2 g3 : iso_mapping g1 g2 -> iso_mapping g2 g3 -> iso_mapping g1 g3.
      Proof. rewrite /iso_mapping/is_iso_mapping; move=> [mu12 [us1 /andP[peq12 eqb12]]] [mu23 [us2 /andP[peq23 eqb23]]].
             exists (mu23 \o mu12).
             suffices ucomp: uniq (relabeling_seq_triple (mu23 \o mu12) g1).
             exists ucomp; apply /andP; split; first by apply: is_pre_iso_trans peq12 peq23.
             by apply : eqb_relabeling_comp eqb12 eqb23.
             rewrite -relabeling_seq_triple_comp /relabeling_seq_triple.
             have eqsize : size [seq relabeling_triple mu23 i | i <- [seq relabeling_triple mu12 i | i <- g1]] =
                             size (relabeling_seq_triple mu23 g2).
             by move: eqb12=> /perm_size; rewrite /relabeling /= /relabeling_seq_triple !size_map.
             rewrite (eq_uniq eqsize) //; last by apply eq_mem_map; move: eqb12=> /perm_mem.
      Qed.

      Definition isocanonical_mapping_map (M : rdf_graph I B L -> rdf_graph I B L) :=
        forall g, iso_mapping (M g) g /\
               (forall g1 g2, eqb_rdf (M g1) (M g2) <-> iso_mapping g1 g2).

      Definition mapping_is_iso_mapping (M : rdf_graph I B L -> rdf_graph I B L) := forall g, iso_mapping (M g) g.


      Definition dt_names_mapping (M : rdf_graph I B L -> rdf_graph I B L) := forall g1 g2,
          iso_mapping g1 g2 -> eqb_rdf (M g1) (M g2).

      (* forall g μ, {in (get_b g), bijective μ} -> M g == M (relabeling μ g). *)

      (* Definition dont_manipulate_names_mapping_idem (M : rdf_graph I B L -> rdf_graph I B L) (dnmn : dont_manipulate_names_mapping M) : forall g (μ : B -> B), (bijective μ) -> M (M g) = M g. *)

      (* Lemma iso_leads_canonical_mapping M (nmn : dt_names_mapping M) g1 g2 : *)
      (*   iso_mapping g1 g2 -> eqb_rdf (M g1) (M g2). *)
      (* Proof. rewrite /iso_mapping/is_iso_mapping; move=> [μ /andP [peq eqb]]. *)
      (*        suffices -> : M g2 = M (relabeling μ g2). by []. *)
      (*        apply /eqP; apply (nmn g2 μ bijmu). *)
      (* Qed. *)

      Lemma same_res_impl_iso_mapping M g1 g2 (iso_output : mapping_is_iso_mapping M) : eqb_rdf (M g1) (M g2) -> iso_mapping g1 g2.
      Proof.
        have isog1k1 : iso_mapping g1 (M g1). by rewrite iso_mapping_sym; apply iso_output.
        have isog2k2 : iso_mapping (M g2) g2. by apply iso_output.
        by move=> /eqiso_mapping peqm; apply: iso_mapping_trans (iso_mapping_trans isog1k1 peqm) isog2k2.
      Qed.

      Lemma isocanonical_mapping_dt_out_mapping M (iso_out: mapping_is_iso_mapping M) (dt: dt_names_mapping M) : isocanonical_mapping_map M.
      Proof.
        split; first by apply iso_out.
        split; last by apply dt.
        + by apply: same_res_impl_iso_mapping iso_out.
      Qed.


    End IsoMapping.

  End EqRdf.
  Section Relabeling_alt.
    Variables I B L : choiceType.
    Implicit Type g : rdf_graph I B L.
    Definition relabeling_alt {g} (mu : {ffun (seq_sub (bnodes g)) -> B}) g1 : rdf_graph I B L. Admitted.

  End Relabeling_alt.


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

