From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Triple Term Util.

Section Rdf.

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
    Definition merge_rdf_graph g1 g2 : rdf_graph I B L:=
      mkRdfGraph (g1 ++ g2).

    Notation "g1 +-+ g2" := (merge_rdf_graph g1 g2) (at level 0, only parsing).

    Lemma merge_cons t ts :
      {| graph := t::ts |} = (mkRdfGraph [:: t]) +-+ (mkRdfGraph ts).
    Proof. by []. Qed.

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

      Lemma relabeling_seq_triple_ext (μ1 μ2 : B -> B') ts :
        μ1 =1 μ2 -> relabeling_seq_triple μ1 ts = relabeling_seq_triple μ2 ts.
      Proof. move=> mu_eq; apply: eq_map; exact: relabeling_triple_ext. Qed.

      Lemma relabeling_seq_triple_comp (B'' : Type) (μ2 : B -> B') (μ1 : B' -> B'') ts :
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

      Lemma relabeling_ext  (μ1 μ2 : B -> B') g :  μ1 =1 μ2 -> relabeling μ1 g = relabeling μ2 g.
      Proof. by move=> μpweq; rewrite /relabeling (relabeling_seq_triple_ext _ μpweq). Qed.

      Lemma relabeling_nil B1 B2 (μ: B1 -> B2) :
        relabeling μ {| graph := [::] |} = {| graph := [::] |}.
      Proof. by []. Qed.

      Lemma relabeling_cons B1 B2 (μ: B1 -> B2) (trpl : triple I B1 L) (ts : seq (triple I B1 L)) :
        relabeling μ {| graph := trpl :: ts |} =
          {| graph := relabeling_triple μ trpl :: (relabeling_seq_triple μ ts) |}.
      Proof. by []. Qed.


    End Relabeling_graph.
    Section CodeRdf.

      (* Variables (I B L : Type). *)

      (* Implicit Type g : rdf_graph I B L. *)

      Definition code_rdf g : (seq (triple I B L))%type :=
        graph g.

      Definition decode_rdf (s: seq (triple I B L)) : (rdf_graph I B L) :=
        (mkRdfGraph s).

      Lemma pcancel_code_decode : cancel code_rdf decode_rdf.
      Proof. by case. Qed.

    End CodeRdf.
  End PolyRdf.

  Section EqRdf.
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

    (* lost eqType *)
    (* Definition rdf_eqP : Equality.axiom eqb_rdf. *)
    (* Proof. rewrite /Equality.axiom => x y. *)
    (*        apply: (iffP idP) => //= [| ->]; case: x y=> [g1] [g2]. *)
    (*        by rewrite /eqb_rdf; => /eqP /= ->. *)
    (*        by apply eqb_rdf_refl. *)
    (* Qed. *)

    (* Canonical rdf_eqType := EqType (rdf_graph I B L) (EqMixin rdf_eqP). *)
    Canonical rdf_eqType := EqType (rdf_graph I B L) (CanEqMixin (@pcancel_code_decode I B L)).
    Canonical rdf_predType := PredType (pred_of_seq \o (@graph I B L)).

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

    Section Relabeling_graph_eq.

      Lemma relabeling_mu_inv (g : rdf_graph I B L) (fs : seq (B -> B))
        (mapping : rdf_graph I B L -> rdf_graph I B L) :
        (mapping g) \in (map (fun mu => relabeling mu g) fs) ->
                        exists (mu : B -> B), relabeling mu g == mapping g.
      Proof.
        elim : fs => [| f fs' IHfs]; first by rewrite in_nil.
        rewrite in_cons; case/orP.
        + by rewrite eq_sym; exists f.
        + by move=> /IHfs //.
      Qed.

    End Relabeling_graph_eq.

    Definition terms (I' B' L': eqType) (g : rdf_graph I' B' L') : seq (term I' B' L') :=
      undup (flatten (map (@terms_triple I' B' L') g)).

    Lemma undup_terms g : undup (terms g) = (terms g).
    Proof. by rewrite /terms undup_idem. Qed.

    Definition terms_cons (I' B' L': eqType) (trpl : triple I' B' L') (ts : seq (triple I' B' L')) :
      terms (mkRdfGraph (trpl :: ts)) = undup (terms_triple trpl ++ (terms (mkRdfGraph ts))).
    Proof. by rewrite /terms; case: ts=>  [ // | ? ? ] ; rewrite undup_cat_r. Qed.

    Section TermRelabeling.
      Variable B1 B2: eqType.

      Lemma terms_relabeled (g : rdf_graph I B1 L) (mu: B1 -> B2) (inj_mu : injective mu):
        (@terms I B2 L (relabeling mu g)) = map (relabeling_term mu) (terms g).
      Proof. elim g=> g'; elim g'=> [//|t ts IHts].
             + rewrite relabeling_cons !terms_cons -undup_map_inj; last exact: relabeling_term_inj.
               by rewrite IHts map_cat terms_relabeled_triple //; apply inj_mu.
      Qed.
    End TermRelabeling.

    Definition bnodes g : seq (term I B L) :=
      undup (filter (@is_bnode _ _ _) (terms g)).

    (* Lemma bnodesP g: Finite.axiom (bnodes g). *)
    (*   Proof. rewrite /Finite.axiom=> t. rewrite /bnodes. *)

    Section BnodeRelabeling.
      Variable B1 B2: eqType.
      Lemma bnodes_relabel (g: rdf_graph I B L) (mu: B -> B): bnodes (relabeling mu g) = (map (relabeling_term mu) (bnodes g)).
      Proof. Admitted.

    End BnodeRelabeling.
    Lemma bnodes_cons (trpl : triple I B L) (ts : seq (triple I B L)) :
      bnodes {| graph := trpl :: ts |} = undup ((bnodes_triple trpl) ++ (bnodes {| graph := ts |})).
    Proof.
      elim: ts trpl => [| h ts' IHts]=> trpl; rewrite /bnodes/bnodes_triple.
      + by rewrite /terms /= !cats0 filter_undup undup_idem.
      + by rewrite terms_cons filter_undup undup_idem undup_cat_r filter_cat.
    Qed.

    Remark undup_bnodes g : undup (bnodes g) = bnodes g.
    Proof. by rewrite /bnodes undup_idem. Qed.

    Lemma all_bnodes g : all (@is_bnode I B L) (bnodes g).
      case: g=> g'; elim: g' => [//| t ts IHts].
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

    Lemma ground_no_bnodes g : bnodes g = [::] <-> is_ground g.
    Proof. split=> [|].
           + rewrite /is_ground /bnodes. elim g=> g'; elim: g' => [| a t IHts]; first by rewrite all_nil.
             rewrite -filter_undup.
             case a=> s p o; case: s; case: p; case o
                  => // x y z sib pii; rewrite terms_cons undup_cat_l undup_idem  filter_undup /=.
           - exact: IHts.
           - exact: IHts.
           - case e: (Bnode x \in [seq x <- terms {| graph := t |} | is_bnode x]) => contr //.
             by apply undup_nil in contr; rewrite contr in_nil in e.
           - case e: (Bnode z \in [seq x <- terms {| graph := t |} | is_bnode x]) => contr //.
             apply undup_nil in contr. rewrite contr in_nil in e. done.
           - case e: (Bnode z \in [seq x <- terms {| graph := t |} | is_bnode x]) => contr //.
             apply undup_nil in contr. rewrite contr in_nil in e. done.
           - case e: (Bnode x \in [seq x <- terms {| graph := t |} | is_bnode x]);
               case e2: (Bnode z \in Bnode x :: [seq x <- terms {| graph := t |} | is_bnode x])
                  => contr //; first by apply undup_nil in contr; rewrite contr in_nil in e.
             + rewrite /is_ground/bnodes/terms. elim g=> g'; elim g'=> [//| h t IHts].
               move=> /= /andP [groundT /IHts/undup_nil allT].
               rewrite undup_cat filter_cat allT cats0 -!filter_undup undup_idem !filter_undup -filter_predI.
               by case: h groundT=> s p o; case: s; case: p; case: o
               => // ? ? ? ? ?; rewrite /terms_triple filter_undup.
    Qed.

    Definition get_b g : seq B :=
      get_bs (bnodes g).

    (* Lemma get_bs_cons (trpl : triple I B L) (ts : seq (triple I B L)) : *)
      (*   get_b {| graph := (trpl :: ts) |} = undup (get_bs (bnodes_triple trpl) ++ get_b {| graph := ts |}). *)
      (* Proof. rewrite /get_b bnodes_cons. Admitted. *)


      (* Lemma get_bs_bnodes (b : B) g: (Bnode b) \in (bnodes g) -> b \in (get_b g). *)
      (* Proof. elim g=> g'; elim: g'=> [//| h t IHtl]. *)
      (*        rewrite bnodes_cons get_bs_cons undup_cat mem_cat. *)
      (*        Admitted. *)

      (* Lemma get_bs_notin (b : B) (s: seq (term I B L)): (Bnode b) \notin s -> b \notin (get_bs s). *)
      (*   Proof. Admitted. *)


      (* Lemma get_bs_uniq (s : seq (term I B L)) : uniq s -> uniq (get_bs s). *)
      (* Proof. rewrite /get_b. elim: s=> [//| h t IHtl]. *)
      (*        rewrite /=; case: h=> x /andP [nin unt]. *)
      (*         apply: IHtl unt. *)
      (*         apply: IHtl unt. *)
      (*         by rewrite cons_uniq (IHtl unt) (get_bs_notin nin). *)
      (* Qed. *)

      (* Lemma mapping_permutation_injective g1 g2 mu: *)
      (*     perm_eq (map mu (get_b g1)) (get_b g2) -> *)
      (*     uniq (map mu (get_b g1)). *)
      (* Proof. by move=> /perm_uniq ->; apply get_bs_uniq; rewrite undup_uniq. Qed. *)

    Lemma relabeling_triple_of_comp (B1 B2 B3: eqType)(mu : B2 -> B3) (nu : B1 -> B2): ((@relabeling_triple I L _ _ mu) \o (@relabeling_triple I L _ _ nu)) =1 (relabeling_triple (mu \o nu)).
    Proof. by move=> t; rewrite relabeling_triple_comp. Qed.

    Lemma bijective_eqb_rdf mu nu g1 g2 :
      cancel mu nu -> eqb_rdf g1 (relabeling mu g2) -> eqb_rdf g2 (relabeling nu g1).
    Proof.
      rewrite /eqb_rdf=> cancel_mu_nu /perm_map=> /(_ (triple_eqType I B L) (relabeling_triple nu)).
      suffices : [seq relabeling_triple nu i | i <- relabeling mu g2] = g2. by rewrite perm_sym; move ->.
      have-> : [seq relabeling_triple nu i | i <- relabeling mu g2] = relabeling_seq_triple (nu \o mu) g2.
      rewrite /relabeling_seq_triple. case:  g2=> g2'; elim : g2' => [//| a t IHtl /=].
      f_equal; first by rewrite relabeling_triple_comp.
      by apply IHtl.
      have /relabeling_seq_triple_ext-> : nu \o mu =1 id by [].
      by rewrite relabeling_seq_triple_id.
    Qed.

    Definition is_iso g1 g2 (μ : B -> B) :=
      (*   (* ({in (get_b g2), bijective μ}) *) *)
      (bijective μ)

      /\ eqb_rdf g1 (relabeling μ g2).

    Definition iso g1 g2 := exists (μ : B -> B),
        is_iso g1 g2 μ.

    Remark id_bij T: bijective (@id T). Proof. by exists id. Qed.
    Hint Resolve id_bij.

    Lemma iso_refl g : iso g g.
    Proof. rewrite /iso /is_iso; exists id; split; first exact: id_bij.
           by rewrite relabeling_id eqb_rdf_refl.
    Qed.

    Remark eqiso g1 g2 : perm_eq g1 g2 -> iso g1 g2.
    Proof. exists id. rewrite /is_iso; split; first exact (id_bij _).
           by rewrite relabeling_id.
    Qed.

    Lemma iso_symm g1 g2 : iso g1 g2 <-> iso g2 g1.
    Proof.
      rewrite /iso /is_iso.
      split; case=> mu [mu_bij heqb_rdf]; case: (mu_bij)
           => [nu h1 h2]; (exists nu; split; [exact: bij_can_bij h1 | exact: bijective_eqb_rdf heqb_rdf]).
    Qed.

    (* Lemma perm_inj (T1 T2: eqType) (f: seq T1 -> seq T2) (x y : seq T1): injective f -> perm_eq x y -> perm_eq (f x) (f y). *)
    (* Proof. move=> injF. *)



    Lemma iso_trans g1 g2 g3 : iso g1 g2 -> iso g2 g3 -> iso g1 g3.
    Proof. rewrite /iso/is_iso/eqb_rdf => [[μ1 [bij1 eqb1]] [μ2 [bij2 eqb2]]].
           exists (μ1 \o μ2). split; first by apply bij_comp.
           eapply perm_trans. apply eqb1. rewrite /relabeling. move: eqb2=> /perm_map => /(_ (triple_eqType I B L) (relabeling_triple μ1)).
           suffices -> : [seq relabeling_triple μ1 i | i <- relabeling μ2 g3] = relabeling_seq_triple (μ1 \o μ2) g3. by [].
           rewrite map_comp /relabeling/relabeling_seq_triple. case : g3=> g'; elim g'=> // t tl IHtl /=.
           by rewrite IHtl; f_equal; rewrite relabeling_triple_comp.
    Qed.

    Definition mapping_is_iso (M : rdf_graph I B L -> rdf_graph I B L) := forall g, iso (M g) g.

    Definition isocanonical_mapping (M : rdf_graph I B L -> rdf_graph I B L) :=
      forall g, mapping_is_iso M /\
             (forall g1 g2, perm_eq (M g1) (M g2) <-> iso g1 g2).

    Definition dt_names (M : rdf_graph I B L -> rdf_graph I B L) := forall g μ, (bijective μ) -> (eqb_rdf  (M (relabeling μ g)) (M g)).

    (* Definition dont_manipulate_names_mapping_idem (M : rdf_graph I B L -> rdf_graph I B L) (dnmn : dont_manipulate_names_mapping M) : forall g (μ : B -> B), (bijective μ) -> M (M g) = M g. *)

    Definition order_agnostic (M : rdf_graph I B L -> rdf_graph I B L) := forall g1 g2, eqb_rdf g1 g2 -> eqb_rdf (M g1) (M g2).

    Lemma iso_leads_canonical M (nmn : dt_names M) (oa : order_agnostic M) g1 g2 (iso_g1_g2: iso g1 g2) :
      eqb_rdf (M g1) (M g2).
    Proof. case iso_g1_g2=> μ [bijmu eqb].
           suffices canon: eqb_rdf (M g1) (M (relabeling μ g2)).
           have mg22: eqb_rdf (M (relabeling μ g2)) (M g2).
           apply : nmn bijmu.
           apply (eqb_rdf_trans canon mg22).
           apply: oa eqb.
    Qed.

    Lemma same_res_impl_iso M g1 g2 (iso_output : mapping_is_iso M) : perm_eq (M g1) (M g2) -> iso g1 g2.
    Proof.
      have isog1k1 : iso g1 (M g1). by rewrite iso_symm; apply iso_output.
      have isog2k2 : iso (M g2) g2. by apply iso_output.
      move=> /eqiso k1_eq_k2.
      apply (iso_trans isog1k1 (iso_trans k1_eq_k2 isog2k2)).
    Qed.

    Lemma isocanonical_mapping_dt_out M (iso_out: mapping_is_iso M) (dt: dt_names M) (oa :order_agnostic M) : isocanonical_mapping M.
    Proof. rewrite /isocanonical_mapping. split; first by apply iso_out.
           split.
           + by apply: same_res_impl_iso iso_out.
           + by apply: (iso_leads_canonical dt oa).
    Qed.

  End EqRdf.
  Section Relabeling_alt.
    Variables I B L : choiceType.
    Implicit Type g : rdf_graph I B L.
    Definition relabeling_alt {g} (mu : {ffun (seq_sub (bnodes g)) -> B}) g1 : rdf_graph I B L. Admitted.

  End Relabeling_alt.


  Definition rdf_canChoiceMixin' (I B L : choiceType) := CanChoiceMixin (@pcancel_code_decode I B L).
  Definition rdf_canCountMixin' (I B L : countType):= CanCountMixin (@pcancel_code_decode I B L).

  Canonical rdf_choiceType (I B L: choiceType):= Eval hnf in ChoiceType (rdf_graph I B L) (@rdf_canChoiceMixin' I B L).
  Canonical rdf_countType (I B L: countType):= Eval hnf in CountType (rdf_graph I B L) (@rdf_canCountMixin' I B L).

  Definition rdf_canPOrderMixin (I B L: countType):= PcanPOrderMixin (@pickleK (rdf_countType I B L)).
  Canonical rdf_POrderType (I B L: countType):= Eval hnf in POrderType tt (rdf_graph I B L) (@rdf_canPOrderMixin I B L).

  Section CountRdf.
    Variables I B L : countType.
    Implicit Type g : rdf_graph I B L.

    Lemma empty_min g : Order.max g (mkRdfGraph [::]) = g.
    Proof. by case: g=> g'; case: g'=> [//|h t]; rewrite Order.POrderTheory.maxElt. Qed.

    (* assia : this requires rewriting relabeling function(. cf error message
The term "g1" has type "rdf_graph I B L" while it is expected to have type
 "rdf_graph I (seq_sub_finType (bnodes g1)) ?L" *)

    Fail Definition is_iso_alt g1 g2  (μ :  {ffun (seq_sub (bnodes g1)) -> B}) :=
      {in {set (seq_sub (bnodes g1))} , bijective μ} /\ g2 == (relabeling_alt μ g1).
    (* The term "μ" has type "{ffun seq_sub (bnodes g1) -> B}" while it is expected to have type *)
    (*   "{set seq_sub (bnodes g1)} -> ?rT". *)

    Fail Definition iso_alt g1 g2:= exists mu, @is_iso_alt g1 g2 mu.

    Section IsoBij_in_dom.

      Definition bijin (mu : B -> B) (D : seq B) := {in D, bijective mu}.

      (* Definition bijin_inv mu D (mu_bijin: bijin mu D) : exists nu, bijin nu (map mu D). *)
      (* Proof. case mu_bijin=> nu canin canon. exists nu. rewrite /bijin. exists mu=> x xin. *)
      (*        + *)
      (*          (* have inj_mu: injective mu. eapply can_inj. admit. *) *)
      (*          rewrite canon //.  *)
      (*          admit. *)
      (*        + rewrite canin //. *)
      (*          (* have : injective mu. *) *)
      (*          (* needs to apply mem_image to the fintype of the list D *) *)
      (*          rewrite mem_map //) in xin. *)
      (*          admit. *)
      (* Admitted. *)

      Definition list_intersection (D1 : list B) (D2 : list B) : list B :=
        let fix help xs :=
          match xs with
          | nil => nil
          | x :: xs => if (mem_seq xs x) then x :: (help xs) else help xs end in
        help ((undup D1) ++ (undup D2)).

      Section intersection_example.

        Variables b1 b2 b3 : B.
        Hypothesis b12_neq : b1 == b2 = false.
        Hypothesis b23_neq : b2 == b3 = false.
        Hypothesis b31_neq : b1 == b3 = false.
        Example li : list_intersection [:: b1; b2] [:: b2; b3] == [:: b2].
        Proof. rewrite /list_intersection.
               by rewrite /= !in_cons !in_nil /= !b12_neq b23_neq /= b12_neq b31_neq b23_neq eqxx.
        Qed.

      End intersection_example.

      Fixpoint find_preim (mu : B -> B) (D CD: list B) : list B :=
        match D with
        | nil => nil
        | b :: bs => if mem_seq CD (mu b)
                   then b :: find_preim mu bs CD else
                     find_preim mu bs CD end.

      Lemma in_preim1 mu D CD x : x \in find_preim mu D CD -> (x \in D).
      Admitted.

      Lemma in_preim2 mu D CD x : x \in find_preim mu D CD -> (mu x) \in CD.
      Admitted.

      Lemma in_li2 D1 D2 x : x \in list_intersection D1 D2 -> x \in D2.
      Admitted.

      Definition bijin_comp (mu1 : B -> B) D1 (mu2 : B -> B) D2 (bijin_mu1 : bijin mu1 D1) (bijin_mu2 : bijin mu2 D2) : bijin (mu2 \o mu1) (find_preim mu1 D1 (list_intersection (map mu1 D1) D2)).
      Proof. rewrite /bijin. case bijin_mu1=> nu1 canin1 canon1; case bijin_mu2=> nu2 canin2 canon2.
             exists (nu1 \o nu2)=> x xin.
             rewrite /= canin2. rewrite canin1 //.
             by move: xin=> /in_preim1.
             by move: xin=> /in_preim2/in_li2.
             have nunuin : nu1 (nu2 x) \in D1. by apply in_preim1 in xin.
             rewrite /= canon1; last by apply nunuin. rewrite canon2 //.
             by move: xin=> /in_preim2/in_li2; rewrite canon1.
      Qed.

      Definition iso_bijin g1 g2 := exists (mu : B -> B),
          bijin mu (get_b g1) /\
            perm_eq (relabeling mu g1) g2.

      (* Lemma get_b_map mu g : (@get_b I B L (relabeling mu g)) = [seq mu i | i <- get_b g]. *)
      (* Proof. elim g=> g'; elim: g'=> [//| t ts IHts]. *)
      (*        rewrite relabeling_cons /= /get_b !bnodes_cons. rewrite !undup_cat. Abort. *)

      (* Lemma one_to_one mu g1 g2 : bijin mu (get_b g1) -> relabeling mu g1 == g2 -> *)
      (*                             perm_eq (get_b g2) (map mu (get_b g1)). *)
      (* Proof. elim g1=> g1'; elim: g1'=> [| t ts IHts]. *)
      (*        move=> _ /eqP <- /=. rewrite relabeling_nil //.  *)
      (*        move=> h /eqP H /=. rewrite -H. Abort. *)
      (* relabeling_cons. /get_b/bnodes. apply perm_undup. //. *)
      (* rewrite . *)


      Definition iso_bijin_refl g: iso_bijin g g.
      Proof. exists id; split; first by exists id.
                                     by rewrite relabeling_id.
      Qed.

      Lemma relabeling_codom mu g1 g2 : relabeling mu g1 = g2 -> forall b, b \in (get_b g1) -> mu b \in (get_b g2).
      Proof. Admitted.

      Lemma mem_in_map (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1) : {in s, injective f} -> forall (x : T1), (f x \in [seq f i | i <- s]) = (x \in s).
      Proof. move=> H x. apply /mapP/idP; last by exists x.
                                                   by move=> [y yin] /eqP; rewrite eq_sym=> /eqP/H <-.
      Qed.

      Lemma can_in_pcan_in (T1 T2 : eqType) (f : T1 -> T2) (g : T2 -> T1) (s : seq T2): {in s, cancel g f} -> {in s, pcancel g (fun y => Some (f y))}.
      Proof. by move=> can y yin; congr (Some _); apply can. Qed.
      (* from coq ssr ssrfun *)

      (* Lemma pcan_in_inj1 (T1 T2 : eqType) (f : T1 -> T2) (g : T2 -> option T1) (s : seq T1) : *)
      (*   {in s, pcancel f g} -> {in s, injective f}. *)
      (* Proof. move=> fK x xin y=> /(congr1 g); rewrite fK //. => [[//] |]. Qed. *)

      Lemma pcan_in_inj (T1 T2 : eqType) (f : T1 -> T2) (g : T2 -> option T1) (s : seq T1) :
        {in s, pcancel f g} -> {in s &, injective f}.
      Proof. by move=> fK x y xin yin=> /(congr1 g); rewrite !fK // => [[]]. Qed.
      (* from coq ssr ssrfun *)

      Lemma inj_in_inamp (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1): {in s, injective f} -> {in s &, injective f}.
      Proof. by move=> injf x y xin /injf H /eqP; rewrite eq_sym=> /eqP/H ->. Qed.

      Lemma can_in_inj (T1 T2 : eqType) (f : T1 -> T2) (g : T2 -> T1) (s : seq T1) : {in s, cancel f g} -> {in s &, injective f}.
      Proof. move/can_in_pcan_in. move=> pcan. eapply pcan_in_inj. exact: pcan. Qed.
      (* from coq ssr ssrfun *)

      Lemma local_inj_can_sym (A C : eqType) (f : C -> A) (f' : A -> C) (cs : list C): {in cs, cancel f f'} -> {in (map f cs) &, injective f'} -> {in (map f cs), cancel f' f}.
      Proof.
        move=> h1 h2. move=> a ain.
        have [c ceq]: exists t : C, a = f t.
        by apply map_inv in ain.
        rewrite ceq. rewrite h1 //. rewrite ceq in ain. erewrite <- mem_in_map. apply ain.
        have : {in cs&, injective f}. apply (can_in_inj h1). 
        (* here I need {in cs, injective f}, but have {in cs&, injective f} instead*)
      Abort.


      (* Lemma relabeling_dom mu g1 g2 : relabeling mu g1 = g2 -> forall b, mu b \in (get_b g2) -> b \in (get_b g1). *)
      (* Proof. Admitted. *)

      (* Lemma bijective_in_eqb_rdf (I B L : eqType) (mu nu : B -> B) (g1 g2 : rdf_graph I B L) : *)
      (*     {in (get_b g1), (cancel mu nu /\ (g1 == relabeling mu g2))} -> {in (get_b g2), g2 == relabeling nu g1}. *)

      Lemma iso_bijin_trans g1 g2 g3 : iso_bijin g1 g2 -> iso_bijin g2 g3 -> iso_bijin g1 g3.
      Proof. rewrite /iso_bijin/bijin=> [[mu12 [bijin12 rel12]]] [mu23 [bijin23 rel23]].
             exists (mu23 \o mu12). split.
             (* last by rewrite -relabeling_comp rel12 rel23. *)
             (* rewrite /bijin. move: bijin12 bijin23=> [nu21 canin12 canon12] [nu32 canin23 canon23]. *)
             (* exists (nu21 \o nu32)=> x xin /=. *)
             (* rewrite canin23 ?canin12 //; apply (relabeling_codom rel12 xin). *)
             (* (* have can21: {in get_b g2, cancel nu21 mu12}. apply inj_can_sym. apply canin12. *) *)
             (* rewrite canon12; last exact xin. rewrite canon23 //. *)

             (* inj_can_sym: forall [A B : Type] [f : B -> A] [f' : A -> B], cancel f f' -> injective f' -> cancel f' f *)
             (* erewrite relabeling_dom=> //.  *)
             (* no hypothesis about nu's composition *)

      (* need something to build the other direction using the cancel,
              something like the commented lemma above. *)
      Abort.

      (* one of these may also work *)

      (*              in_onS_can: *)
      (*   forall {aT rT : predArgType} (aD : {pred aT}) {f : aT -> rT} {g : rT -> aT}, *)
      (*   (forall x : rT, g x \in aD) -> {in rT, {on aD, cancel g & f}} -> cancel g f *)
      (* onW_can_in: *)
      (*   forall {aT rT : predArgType} (aD : {pred aT}) {rD : {pred rT}} {f : aT -> rT} {g : rT -> aT}, *)
      (*   {in rD, cancel g f} -> {in rD, {on aD, cancel g & f}} *)
      (* inj_can_sym_on: *)
      (*   forall {aT rT : predArgType} {aD : {pred aT}} {f : aT -> rT} {g : rT -> aT}, *)
      (*   {in aD, cancel f g} -> {on aD &, injective g} -> {on aD, cancel g & f} *)
      (* on_can_inj: *)
      (*   forall [T1 T2 : predArgType] [D2 : {pred T2}] [f : T1 -> T2] [g : T2 -> T1], *)
      (*   {on D2, cancel f & g} -> {on D2 &, injective f} *)
      (* in_onW_can: *)
      (*   forall {aT rT : predArgType} (aD : {pred aT}) (rD : {pred rT}) {f : aT -> rT} {g : rT -> aT}, *)
      (*   cancel g f -> {in rD, {on aD, cancel g & f}} *)
      (* can_in_eq: *)
      (*   forall [aT rT : eqType] [D : pred aT] [f : aT -> rT] [g : rT -> aT], *)
      (*   {in D, cancel f g} -> {in D &, forall x y : aT, (f x == f y) = (x == y)} *)
      (* canRL_on: *)
      (*   forall [T1 T2 : predArgType] [D2 : {pred T2}] [f : T1 -> T2] [g : T2 -> T1] [x : T1] [y : T2], *)
      (*   {on D2, cancel f & g} -> f x \in D2 -> f x = y -> x = g y *)
      (* canLR_on: *)
      (*   forall [T1 T2 : predArgType] [D2 : {pred T2}] [f : T1 -> T2] [g : T2 -> T1] [x : T2] [y : T1], *)
      (*   {on D2, cancel f & g} -> f y \in D2 -> x = f y -> g x = y *)

      (* bijective_eqb_rdf: *)
      (*   forall [I B L : eqType] [mu nu : B -> B] [g1 g2 : rdf_graph I B L], *)
      (*   cancel mu nu -> g1 == relabeling mu g2 -> g2 == relabeling nu g1 *)
      (*         canLR_in: *)
      (*   forall [T1 T2 : predArgType] [D1 : {pred T1}] [f : T1 -> T2] [g : T2 -> T1] [x : T2] [y : T1], *)
      (*   {in D1, cancel f g} -> y \in D1 -> x = f y -> g x = y *)
      (* canRL_in: *)
      (*   forall [T1 T2 : predArgType] [D1 : {pred T1}] [f : T1 -> T2] [g : T2 -> T1] [x : T1] [y : T2], *)
      (*   {in D1, cancel f g} -> x \in D1 -> f x = y -> x = g y *)
      (* can_in_inj: *)
      (*   forall [T1 T2 : predArgType] [D1 : {pred T1}] [f : T1 -> T2] [g : T2 -> T1], *)
      (*   {in D1, cancel f g} -> {in D1 &, injective f} *)


      Definition iso_bijin_symm g1 g2 : iso_bijin g1 g2 <-> iso_bijin g2 g1.
      Proof.
        (* Abort. *)
        (* split; rewrite /iso_bijin=> [] [mu [[nu canin] canon]] /eq_eqb_rdf relab. *)
        (* exists nu; split. rewrite /bijin. admit. *)
        (* rewrite eq_sym in relab *. rewrite eq_sym. eapply bijective_eqb_rdf; last by apply relab. *)
        (* Fail apply canin. *)
      Abort.
      (* solving the problem of trans would also solve symmetry *)


    End IsoBij_in_dom.

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
        Proof. Admitted.

      End PreIso.

      Definition is_iso_mapping g1 g2 mu :=
        is_pre_iso g1 g2 mu &&
          eqb_rdf (relabeling mu g1) g2.

      Definition iso_mapping g1 g2 := exists mu, is_iso_mapping g1 g2 mu.

      Definition iso_mapping_refl g : iso_mapping g g.
      Proof. exists id; rewrite /is_iso_mapping; apply /andP; split; last by rewrite relabeling_id eqb_rdf_refl.
             + by rewrite /is_pre_iso map_id.
      Qed.

      Definition map_nil_is_nil (A C: eqType) (f : A -> C) (s : seq A) : (map f s == [::]) = (s == [::]).
      Proof. by case s. Qed.

      Lemma mem_eq_is_nil (A : eqType) (s : seq A) : s =i [::] -> s = [::].
      Proof. case: s=> [// | h t] H.
             + have: h \in [::]. rewrite -H in_cons eqxx //.
               by rewrite in_nil.
      Qed.

      (* Definition iso_mapping_inv g1 g2 (mu : B -> B) : B -> B := *)
      (* fun b => if (b \in (get_b g2)) then *)
      (*           (nth b (get_b g1) (index b (map mu (get_b g1)))) *) (*         else b. *)
      (* Lemma mapping_inv_cancel g1 g2 (mu : B -> B) : *)
      (*   perm_eq (map mu (get_b g1)) (get_b g2) -> *)
      (*   eqb_rdf (relabeling mu g1) g2 ->:w *)
      (*   eqb_rdf (relabeling (iso_mapping_inv g1 g2 mu) (relabeling mu g1)) g1. *)
      (* Proof. Admitted. *)

      Lemma relabeling_get_b g1 g2 (mu : B -> B) :
        eqb_rdf (relabeling mu g1) g2 ->
        perm_eq (map mu (get_b g1)) (get_b g2).
      Proof. Admitted.

      Remark eqiso_mapping g1 g2 : eqb_rdf g1 g2 -> iso_mapping g1 g2.
      Proof. rewrite /is_iso_mapping -{1}(relabeling_id g1). exists id; apply /andP; split; last by exact: H.
             by apply: relabeling_get_b H.
      Qed.

      Lemma eqb_rdf_relabeling_sym g1 g2 mu nu :
        eqb_rdf (relabeling mu g1) g2 -> is_pre_iso g2 g1 nu -> eqb_rdf (relabeling nu g2) g1.
      Proof. Admitted.

      Definition iso_mapping_sym g1 g2 : iso_mapping g1 g2 <-> iso_mapping g2 g1.
      Proof.
        suffices imp h1 h2 : iso_mapping h1 h2 -> iso_mapping h2 h1 by split; exact: imp.
        move=> [mu /andP [eqbn rel]].
        rewrite /iso_mapping/is_iso_mapping.
        have [nu nuP]: pre_iso h2 h1. rewrite pre_iso_sym; exists mu; exact eqbn.
        exists nu; apply /andP; split; first exact: nuP.
        by apply (eqb_rdf_relabeling_sym rel).
      Qed.

      Lemma perm_map_comp (T1 T2 T3 : eqType) (f: T1 -> T2) (g : T2 -> T3) s1 s2 s3 :
        perm_eq (map f s1) s2 ->
        perm_eq (map g s2) s3 ->
        perm_eq (map (g \o f) s1) s3.
      Proof. by move=> /(perm_map g); rewrite -map_comp; apply perm_trans. Qed.

      Lemma eqb_relabeling_comp g1 g2 g3 mu12 mu23:
        eqb_rdf (relabeling mu12 g1) g2 ->
        eqb_rdf (relabeling mu23 g2) g3 ->
        eqb_rdf (relabeling (mu23 \o mu12) g1) g3.
      Proof. rewrite /eqb_rdf/relabeling/relabeling_seq_triple. Admitted.


      Definition iso_mapping_trans g1 g2 g3 : iso_mapping g1 g2 -> iso_mapping g2 g3 -> iso_mapping g1 g3.
      Proof. rewrite /iso_mapping/is_iso_mapping; move=> [mu12 /andP[peq12 eqb12]] [mu23 /andP[peq23 eqb23]].
             exists (mu23 \o mu12); apply /andP; split; first by apply: is_pre_iso_trans peq12 peq23.
             apply : eqb_relabeling_comp eqb12 eqb23.
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
      Proof. rewrite /isocanonical_mapping. split; first by apply iso_out.
             split.
             + by apply: same_res_impl_iso_mapping iso_out.
             + by apply dt.
      Qed.


    End IsoMapping.

    Definition is_iso_local g1 g2  (μ :  B -> B) :=
      ({in (get_b g2), bijective μ})
      /\ g1 == (relabeling μ g2).

    Definition iso_local g1 g2:= exists mu, @is_iso_local g1 g2 mu.

    Definition isocanonical_mapping_local (M : rdf_graph I B L -> rdf_graph I B L) :=
      forall g, iso_local (M g) g /\
             (forall g1 g2, (M g1) == (M g2) <-> iso_local g1 g2).

    Lemma iso_local_refl g : iso_local g g.
    Proof. rewrite /iso_local /is_iso_local; exists id; split; first by exists id.
                                                                     by rewrite relabeling_id.
    Qed.

    Remark eqiso_local g1 g2 : g1 == g2 -> iso_local g1 g2.
    Proof. exists id. rewrite /is_iso_local; split; first by exists id.
                                                          by move/eqP: H ->; rewrite relabeling_id.
    Qed.

    Lemma iso_local_symm g1 g2 : iso_local g1 g2 <-> iso_local g2 g1.
    Proof.
      rewrite /iso_local /is_iso_local.
      split; case=> mu [mu_bij heqb_rdf]; case: (mu_bij)
           => [nu h1 h2]; exists nu.
    Admitted.

    Lemma iso_local_trans g1 g2 g3 : iso_local g1 g2 -> iso_local g2 g3 -> iso_local g1 g3.
    Proof. rewrite /iso_local/is_iso_local/relabeling => [[μ1 [bij1/eqP eqb1]] [μ2 [bij2/eqP eqb2]]].
           exists (μ1 \o μ2). split. admit.
           (* apply bij_comp. *)
           by rewrite eqb1 eqb2 relabeling_seq_triple_comp.
    Admitted.

    Definition mapping_is_iso_local (M : rdf_graph I B L -> rdf_graph I B L) := forall g, iso_local (M g) g.

    Definition dt_names_local (M : rdf_graph I B L -> rdf_graph I B L) := forall g μ, {in (get_b g), bijective μ} -> M g == M (relabeling μ g).

    (* Definition dont_manipulate_names_mapping_idem (M : rdf_graph I B L -> rdf_graph I B L) (dnmn : dont_manipulate_names_mapping M) : forall g (μ : B -> B), (bijective μ) -> M (M g) = M g. *)

    Lemma iso_leads_canonical_local M (nmn : dt_names_local M) g1 g2 (iso_g1_g2: iso_local g1 g2) :
      M g1 == M g2.
    Proof. case iso_g1_g2=> μ [bijmu /eqP ->].
           suffices ->: M g2 = M (relabeling μ g2). by [].
           apply /eqP; apply (nmn g2 μ bijmu).
    Qed.

    Lemma same_res_impl_iso_local M g1 g2 (iso_output : mapping_is_iso_local M) : M g1 == M g2 -> iso_local g1 g2.
    Proof.
      have isog1k1 : iso_local g1 (M g1). rewrite iso_local_symm; apply iso_output.
      have isog2k2 : iso_local (M g2) g2. by apply iso_output.
      by move=> /eqP k1_eq_k2; rewrite k1_eq_k2 in isog1k1; apply (iso_local_trans isog1k1 isog2k2).
    Qed.

    Lemma isocanonical_mapping_dt_out_local M (iso_out: mapping_is_iso_local M) (dt: dt_names_local M) : isocanonical_mapping_local M.
    Proof. rewrite /isocanonical_mapping. split; first by apply iso_out.
           split.
           + by apply: same_res_impl_iso_local iso_out.
           + by apply: (iso_leads_canonical_local dt).
    Qed.

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

