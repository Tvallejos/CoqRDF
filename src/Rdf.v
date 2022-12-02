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

    Lemma merge_cons t ts : {| graph := t::ts |} = merge_rdf_graph (mkRdfGraph [:: t]) (mkRdfGraph ts).
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
        relabeling_seq_triple μ1 (relabeling_seq_triple μ2 ts) = relabeling_seq_triple (μ1 \o μ2) ts.
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

      Lemma relabeling_nil B1 B2 (μ: B1 -> B2) : relabeling μ {| graph := [::] |} = {| graph := [::] |}.
      Proof. by []. Qed.

      Lemma relabeling_cons B1 B2 (μ: B1 -> B2) (trpl : triple I B1 L) (ts : seq (triple I B1 L)) :
        relabeling μ {| graph := trpl :: ts |} = {| graph := relabeling_triple μ trpl :: (relabeling_seq_triple μ ts) |}.
      Proof. by []. Qed.

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

    Lemma eqb_rdf_trans g1 g2 g3: eqb_rdf g1 g2 -> eqb_rdf g2 g3 -> eqb_rdf g1 g3.
    Proof. by rewrite /eqb_rdf=> /eqP -> /eqP ->. Qed.

      Definition rdf_eqP : Equality.axiom eqb_rdf.
    Proof. rewrite /Equality.axiom => x y.
           apply: (iffP idP) => //= [| ->]; case: x y=> [g1] [g2].
           by rewrite /eqb_rdf => /eqP /= ->.
           by apply eqb_rdf_refl.
    Qed.

    Canonical rdf_eqType := EqType (rdf_graph I B L) (EqMixin rdf_eqP).
    Canonical rdf_predType := PredType (pred_of_seq \o (@graph I B L)).

    (* Variable g : rdf_graph I B L. *)
    (* Variable trm : term I B L. *)
    (* Variable t : triple I B L. *)
    (* Check trm \in t. *)
    (* Check t \in g. *)
    (* Print SetDef.finset. *)
    (* (* requieres trm to be finType *) *)
    (* Fail Check finset (trm \in g). *)

    Definition terms g : seq (term I B L) :=
      undup (flatten (map (@terms_triple I B L) g)).

    Definition terms_cons (trpl : triple I B L) (ts : seq (triple I B L)) :
      terms (mkRdfGraph (trpl :: ts)) = undup (terms_triple trpl ++ (terms (mkRdfGraph ts))).
    Proof. by rewrite /terms; case: ts=>  [ // | ? ? ] ; rewrite undup_cat_r. Qed.

    Definition bnodes g : seq (term I B L) :=
      undup (filter (@is_bnode _ _ _) (terms g)).

    Lemma bnodes_cons (trpl : triple I B L) (ts : seq (triple I B L)) :
        bnodes {| graph := trpl :: ts |} = undup ((bnodes_triple trpl) ++ (bnodes {| graph := ts |})).
    Proof.
           elim: ts trpl => [| h ts' IHts]=> trpl; rewrite /bnodes/bnodes_triple.
           + by rewrite /terms /= !cats0 filter_undup undup_idem.
           + by rewrite terms_cons filter_undup undup_idem undup_cat_r filter_cat.
    Qed.

    Lemma ground_no_bnodes g : bnodes g = [::] <-> is_ground g.
    Proof. split=> [|].
           + rewrite /is_ground /bnodes. elim g=> g'; elim: g' => [| a t IHts]; first by rewrite all_nil.
             rewrite -filter_undup. case a=> s p o; case: s; case: p; case o=> // x y z sib pii;
                                                                             rewrite terms_cons undup_cat_l undup_idem  filter_undup /=.
           - exact: IHts.
           - exact: IHts.
           - case e: (Bnode x \in [seq x <- terms {| graph := t |} | is_bnode x]) => contr; last by done.
             by apply undup_nil in contr; rewrite contr in_nil in e.
           -
             case e: (Bnode z \in [seq x <- terms {| graph := t |} | is_bnode x]) => contr; last by done.
             apply undup_nil in contr. rewrite contr in_nil in e. done. 
           - case e: (Bnode z \in [seq x <- terms {| graph := t |} | is_bnode x]) => contr; last by done.
             apply undup_nil in contr. rewrite contr in_nil in e. done.
           - case e: (Bnode x \in [seq x <- terms {| graph := t |} | is_bnode x]);
               case e2: (Bnode z \in Bnode x :: [seq x <- terms {| graph := t |} | is_bnode x])=> contr; try done; first by apply undup_nil in contr; rewrite contr in_nil in e.
             + rewrite /is_ground /bnodes /terms. elim g=> g'; elim g'=> [//| h t IHts].
               move=> /= /andP [groundT allT]. apply IHts in allT. apply undup_nil in allT.
               rewrite undup_cat filter_cat allT cats0.
               rewrite -!filter_undup undup_idem !filter_undup -filter_predI.
               case: h groundT=> s p o; case: s; case: p; case: o=> // ? ? ? ? ?;
                     by rewrite /terms_triple filter_undup.
    Qed.

    Definition get_b g : seq B.
    Proof. case g=> g'. elim g' => [| t ts ihts].
           + exact : [::].
           + apply get_b_triple in t. exact (undup (t ++ ihts)).
    Defined.


    (* Definition all_b_in_g g : all (\in g) (get_b g). *)

    Lemma uniq_bnodes g : uniq (bnodes g).
    Proof. exact: undup_uniq. Qed.

    Lemma bijective_eqb_rdf mu nu g1 g2 :
      cancel mu nu -> eqb_rdf g1 (relabeling mu g2) ->  eqb_rdf g2 (relabeling nu g1).
    Proof.
      move=> cancel_mu_nu. rewrite /eqb_rdf => /eqP /= ->.
      rewrite relabeling_seq_triple_comp.
      have /relabeling_seq_triple_ext-> : nu \o mu =1 id by [].
      rewrite relabeling_seq_triple_id; exact: eqb_rdf_refl.
    Qed.

    Definition is_iso g1 g2 (μ : B -> B) :=
      (* ({in bnodes g2, bijective μ}) *)
      (bijective μ) 

      /\ g1 == (relabeling μ g2).

    Definition iso g1 g2 := exists (μ : B -> B),
        is_iso g1 g2 μ.

    Remark id_bij T: bijective (@id T). Proof. by exists id. Qed.

    Lemma iso_refl g : iso g g.
    Proof. rewrite /iso /is_iso; exists id; split.
           exact: id_bij.
           by rewrite relabeling_id.
    Qed.

    Remark eqiso g1 g2 : g1 == g2 -> iso g1 g2.
    Proof. exists id. rewrite /is_iso; split; first by apply id_bij.
           + by rewrite relabeling_id.
    Qed.

    (* Remark eqiso' g1 g2 : eqb_rdf g1 g2 -> iso g1 g2. *)
    (* Proof. move=> /eqP eq. by rewrite eq; apply iso_refl. Qed *)
(*          Error: The LHS of eq *)
(*     (graph g1) *)
(* does not match any subterm of the goal *)

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

    (* Definition mapping_preserves_isomorphism (μ : rdf_graph I B L -> rdf_graph I B L) := forall g, iso (μ g) g. *)

    Definition isocanonical_mapping (M : rdf_graph I B L -> rdf_graph I B L) :=
      forall g, iso (M g) g /\
                  (forall g1 g2, (M g1) == (M g2) <-> iso g1 g2).

    Definition dont_manipulate_names_mapping (M : rdf_graph I B L -> rdf_graph I B L) := forall g μ, (bijective μ) -> M g == M (relabeling μ g).

    (* Definition dont_manipulate_names_mapping_idem (M : rdf_graph I B L -> rdf_graph I B L) (dnmn : dont_manipulate_names_mapping M) : forall g (μ : B -> B), (bijective μ) -> M (M g) = M g. *)

    Definition iso_leads_canonical M (nmn : dont_manipulate_names_mapping M) g1 g2 (iso_g1_g2: iso g1 g2) : M g1 == M g2.
    Proof. case iso_g1_g2=> μ [bijmu /eqP ->].
           (* eq_rel_g1g2]. *)
           suffices ->: M g2 = M (relabeling μ g2). by [].
           by apply /eqP; apply (nmn g2 μ bijmu).
    Qed. 

  End EqRdf.
  Section Relabeling_alt.
    Variables I B L : choiceType.
    Implicit Type g : rdf_graph I B L.
    Definition relabeling_alt {g} (mu : {ffun (seq_sub (bnodes g)) -> B}) g1 : rdf_graph I B L. Admitted.

  End Relabeling_alt.

  Section CodeRdf.

    Variables (I B L : Type).

    Implicit Type g : rdf_graph I B L.

    Definition code_rdf g : (seq (triple I B L))%type :=
      graph g.

    Definition decode_rdf (s: seq (triple I B L)) : (rdf_graph I B L) :=
      (mkRdfGraph s).

    Lemma pcancel_code_decode : cancel code_rdf decode_rdf.
    Proof. by case. Qed.
  End CodeRdf.



    (* Definition code_rdf g := graph g. *)
    (* Definition decode_rdf (ts : seq (triple I B L)) := mkRdfGraph ts. *)

    (* Lemma cancel_rdf_encode : cancel code_rdf decode_rdf. *)
  (* Proof. by case. Qed. *)


    Definition rdf_canChoiceMixin' (I B L : choiceType) := CanChoiceMixin (@pcancel_code_decode I B L).
    Definition rdf_canCountMixin' (I B L : countType):= CanCountMixin (@pcancel_code_decode I B L).

    (* Definition rdf_canChoiceMixin := CanChoiceMixin cancel_rdf_encode. *)
    (* Definition rdf_canCountMixin := CanCountMixin cancel_rdf_encode. *)

    Canonical rdf_choiceType (I B L: choiceType):= Eval hnf in ChoiceType (rdf_graph I B L) (@rdf_canChoiceMixin' I B L).
    Canonical rdf_countType (I B L: countType):= Eval hnf in CountType (rdf_graph I B L) (@rdf_canCountMixin' I B L).

    Definition rdf_canPOrderMixin (I B L: countType):= PcanPOrderMixin (@pickleK (rdf_countType I B L)).
    Canonical rdf_POrderType (I B L: countType):= Eval hnf in POrderType tt (rdf_graph I B L) (@rdf_canPOrderMixin I B L).

    Section CountRdf.
    Variables I B L : countType.
    Implicit Type g : rdf_graph I B L.

    (* assia : this requires rewriting relabeling function(. cf error message
The term "g1" has type "rdf_graph I B L" while it is expected to have type
 "rdf_graph I (seq_sub_finType (bnodes g1)) ?L" *)
    Definition is_iso_alt g1 g2  (μ :  {ffun (seq_sub (bnodes g1)) -> B}) :=
      bijective μ /\ g2 == (relabeling_alt μ g1).

    Definition iso_alt g1 g2:= exists mu, @is_iso_alt g1 g2 mu.

    Definition isocanonical_mapping_alt (M : rdf_graph I B L -> rdf_graph I B L) :=
      forall g, iso_alt (M g) g /\
        (forall g1 g2, (M g1) == (M g2) <-> iso g1 g2).


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

