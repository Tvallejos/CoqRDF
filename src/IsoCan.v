From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term Util.


Section HashedData.

  (* A type for a data (t : T) paired with its current hash (h : H) *)

  Variables (H T: Type).

  Inductive hash  := Hash of T * H.

  Definition input t :=  let: Hash th := t in th.1.

  Definition current_hash h := let: Hash th := h in th.2.

  Definition mkHinput (t : T) (h : H) := Hash (t, h).

  Definition pair_of_hash h := let: Hash th := h in th.

  Canonical hash_subType := [newType for pair_of_hash].

  Definition forget_hashes (hbs: seq hash) : seq T :=
    map (fun b=> input b) hbs.

End HashedData.

(* Various transfers of structures *)
Definition hash_eqMixin (H T : eqType) := Eval hnf in [eqMixin of hash H T by <:].
Canonical hash_eqType (H T : eqType) :=
  Eval hnf in EqType (hash H T) (hash_eqMixin H T).
Lemma eq_i_ch (H T : eqType) (h1 h2: hash H T) :
  h1 == h2 = ((input h1) == (input h2)) && ((current_hash h1) == (current_hash h2)).
Proof. by case h1; case h2. Qed.

Definition hash_choiceMixin (H T : choiceType) := [choiceMixin of hash H T by <:].
Canonical hash_choiceType (H T : choiceType) :=
  Eval hnf in ChoiceType (hash H T) (hash_choiceMixin H T).
Definition hash_countMixin (H T : countType) := [countMixin of hash H T by <:].
Canonical hash_countType (H T : countType) :=
  Eval hnf in CountType (hash H T) (hash_countMixin H T).
Canonical hash_subCountType (H T : countType) :=
  Eval hnf in [subCountType of hash H T].

(* Waiting for inisight on using subtypes for automated transfer *)
Axiom hin_canPOrderMixin : forall (H T : countType), lePOrderMixin (hash_eqType H T).
Canonical hin_POrderType (H T : countType) :=
  Eval hnf in POrderType tt (hash H T) (hin_canPOrderMixin H T).


Section IsoCan.

  Variable I B L: countType.

  Implicit Type trm : term I B L.

  Section IsoCanAlgorithm.

    Variable h : countType.
    Local Notation hash := (hash h).

    Variable h0 : h.

    Definition init_bnode (b : B) : (hash B) :=
      mkHinput b h0.

    Lemma init_bnode_inj : injective init_bnode.
    Proof. by move=> x y []. Qed.

    Section Hterms.

      Definition hterm := term I (hash B) L.

      (* should this be a coercion? let's see *)
      Definition term_of_hterm (ht : hterm) : term I B L :=
        match ht with
        | Iri i => Iri i
        | Bnode hb => Bnode (input hb)
        | Lit l => Lit l
        end.

      Definition eqb_trm_hi trm (ht : hterm) : bool := trm == (term_of_hterm ht).

      Definition eqb_b_hterm (b : B) (ht : (term I (hash B) L)) : bool :=
        if ht is Bnode hb then b == (input hb) else false.

      Lemma eqb_b_hterm_is_bnode b (ht : hterm) : eqb_b_hterm b ht -> is_bnode ht.
      Proof. by case ht. Qed.

      Lemma eqb_b_hterm_trans (b b': B) (ht : (term I (hash B) L)) :
        eqb_b_hterm b ht -> eqb_b_hterm b' ht -> b = b'.
      Proof. by case: ht=> // ? /eqP-> /eqP->. Qed.

      Definition lookup_hash (hb : hterm) : option (hash B) :=
        if hb is Bnode hin then some hin else None.

      Definition lookup_hash_default_ (hb : (term I (hash B) L) ) : h :=
        if hb is Bnode hin then current_hash hin else h0.

      Definition eq_hash (b1 b2 : hterm) : bool :=
        match (lookup_hash b1), (lookup_hash b2) with
        | Some hin1, Some hin2 => current_hash hin1 == current_hash hin2
        | _,_ => false
        end.

      Lemma eq_hash_refl b : is_bnode b -> eq_hash b b.
      Proof. by case: b=> // ?; rewrite /eq_hash/= eqxx. Qed.

      Lemma eq_hash_refl_singl b g :
        bnodes g = [:: b] ->
        (if eq_hash b b then ([:: b], [::]) else ([::], [:: b])).1 = [:: b].
      Proof. by move=> /b_in_bnode_is_bnode/eq_hash_refl ->. Qed.

      Definition cmp_bnode (b : B) (ht : hterm) : bool :=
        match ht with
        | Bnode hin => b == (input hin)
        | _ => false
        end.

      Definition mu_ext (mu : B -> B) : (hash B) -> (hash B):=
        fun b => (mkHinput (mu (input b)) (current_hash b)).

      Definition relabeling_hterm (mu : B -> B) ht : hterm :=
        relabeling_term (mu_ext mu) ht.

      Lemma eqb_b_hterm_relabel f b ht (injF: injective f): (eqb_b_hterm b ht) = (eqb_b_hterm (f b) (relabeling_hterm f ht)).
      Proof. by case ht=> //= name; rewrite inj_eq. Qed.

      Lemma has_map_eqbb s f b (injF: injective f): has (eqb_b_hterm b) s = has (eqb_b_hterm (f b)) (map (relabeling_hterm f) s).
      Proof. elim: s=> [//|hd tl IHtl] /=.
             by rewrite IHtl (@eqb_b_hterm_relabel f b).
      Qed.

    End Hterms.

    Section Htriple.

      Definition htriple := triple I (hash B) L.
      Definition hts := seq (triple I (hash B) L).

      Definition has_term_triple trm (trpl : htriple) : option hterm :=
        match (filter (eqb_trm_hi trm) (terms_triple trpl)) with
        | nil => None
        | t :: ts => Some t
        end.

      Definition lookup_bnode_in_triple (b : B) (t : htriple) : option hterm :=
        match (filter (cmp_bnode b) (terms_triple t)) with
        | nil => None
        | t :: ts => Some t
        end.

    End Htriple.

    Section Hgraph.

      Definition hgraph := rdf_graph I (hash_eqType h B) L.

      Definition get t (g : hgraph) : option hterm :=
        let otrs := (map (has_term_triple t) (graph g)) in
        head None (filter isSome otrs).

      Lemma init_hash_uniq {i l : eqType} (g : rdf_graph i B l) :
        uniq (@relabeling_seq_triple i l _ _ init_bnode (graph g)).
      Proof. by case g=> g' ug; rewrite map_inj_uniq //; apply: relabeling_triple_inj init_bnode_inj. Qed.

      Definition init_hash_ts (ts : seq (triple I B L)) : hts :=
        relabeling_seq_triple init_bnode ts.

      (* Algorithm 1, lines 2-8
       initializes every blank node with a known default name *)
      Definition init_hash (g : rdf_graph _ _ _) : hgraph :=
        @relabeling _ _ _ _ init_bnode g (init_hash_uniq g).

      Lemma init_hash_ts_nil : init_hash_ts [::] = [::]. Proof. by []. Qed.

      Lemma init_hash_nil : init_hash empty_rdf_graph = empty_rdf_graph. Proof. by apply rdf_inj. Qed.

      Lemma init_hash_ts_h0 b g : Bnode b \in bnodes_ts (init_hash_ts g) -> current_hash b = h0.
      Proof. by rewrite bnodes_ts_relabel_mem=> /map_inv [[]//? []->]. Qed.

      Lemma init_hash_h0 b g : Bnode b \in bnodes (init_hash g) -> current_hash b = h0.
      Proof. by apply init_hash_ts_h0. Qed.

      (* updates the current hash of b by b' in all the ocurrences
       in every triple of ts *)
      Definition replace_bnode_ts (b b': hash B) (ts : hts) : hts :=
        relabeling_seq_triple (fun a_hash => if a_hash == b then b' else a_hash) ts.

      (* updates the current hash of b by b' in all the ocurrences
       in g *)
      Definition replace_bnode (b b': hash B) (g : hgraph) us : hgraph :=
        @mkRdfGraph _ _ _ (replace_bnode_ts b b' (graph g)) us.

      Definition lookup_bnode_in_ts (ts : seq htriple) (b : B) : option hterm :=
        let otrms := map (lookup_bnode_in_triple b) ts in
        head None (filter isSome otrms).

      Definition lookup_bnode_in_graph (g : hgraph) (b : B) : option hterm :=
        lookup_bnode_in_ts (graph g) b.

      Definition relabeling_hgraph (mu : B -> B) (g: hgraph) us : hgraph :=
        @relabeling _ _ _ _ (mu_ext mu) g us.

      Lemma eqb_b_hterm_relabeling b ht (mu : B -> B) :
        eqb_b_hterm b ht ->
        eqb_b_hterm (mu b) (relabeling_hterm mu ht).
      Proof. by case: ht=> //? /eqP ->; rewrite /eqb_b_hterm/= eqxx. Qed.

    End Hgraph.

  End IsoCanAlgorithm.
End IsoCan.
