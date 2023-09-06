From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term Util.


Section HashedData.

  (* A type for a data (t : T) paired with its current hash (h : H) *)

  Variables (H T : Type).

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

  Section IsoCanAlgorithm.

    Variable h : countType.
    Variables h0 hfwd hbwd hmark herror: h.
    Variable b0 : B.
    (* add conditions on the input *)
    Variable hashTerm : term I B L -> h.
    Hypothesis perfectHashingSchemeTerm : injective hashTerm.
    Variable hashTuple : seq h -> h.
    Hypothesis hashTuple_inj : injective hashTuple.
    Hypothesis hashTuple_neq_error : forall s, hashTuple s == herror = false.
    Hypothesis hashTuple_neq_init : forall s, hashTuple s == h0 = false.

    Implicit Type trm : term I B L.

    Local Notation hash_alt := hash.
    Local Notation hash := (hash h).

    Lemma by_perf_hash trm (o : h) (eqb : hashTerm trm == o) : hashTerm trm = o.
    Proof. by apply/eqP; apply eqb. Qed.

    Definition init_bnode (b : B) : (hash B) :=
      mkHinput b h0.

    Lemma init_bnode_inj : injective init_bnode.
    Proof. by move=> x y []. Qed.

    Hypothesis to_string_nat : nat -> B.
    Hypothesis to_string_nat_inj : injective to_string_nat.
    Definition n0 := 0%N.

    Definition init_bnode_nat (b : B) : (hash_alt nat B) :=
      mkHinput b n0.

    Lemma init_bnode_nat_inj : injective init_bnode_nat.
    Proof. by move=> x y []. Qed.

    (* Algorithm 3, line 13
       hashes b incorporating an arbitrary hash hmark *)
    Definition mark_hash (b : hash B) : hash B :=
      mkHinput (input b) (hashTuple [:: (current_hash b) ; hmark]).

    Lemma mark_hash_idem_inj b1 b2:
      mark_hash (mark_hash b1) == mark_hash (mark_hash b2) ->
      (mark_hash b1 == mark_hash b2).
    Proof. case b1; case b2=> [[a b] [a' b']] /=.
           by rewrite /mark_hash eq_i_ch /==> /andP [/eqP -> /eqP/hashTuple_inj [->]].
    Qed.

    Lemma appn_mark_hash (b1 b2: hash B) n:
      (mark_hash (app_n mark_hash (mkHinput (input b1) h0) n) ==
         mark_hash (app_n mark_hash (mkHinput (input b2) h0) n)) ->
      ((input b1) == (input b2)) &&
        (app_n mark_hash (mkHinput (input b1) h0) n ==
           app_n mark_hash (mkHinput (input b2) h0) n).
    Proof. elim: n=> [/=| n' IHn].
           case b1; case b2=> [[a b] [a' b']]; first by rewrite eq_i_ch/==> [/andP [/eqP ->]]; rewrite !eqxx.
           by move=> /=/mark_hash_idem_inj/IHn => /andP [-> /eqP ->] /=.
    Qed.

    Lemma appn_mark_hash_eq_input (b1 b2: hash B) n:
      ((app_n mark_hash (mkHinput (input b1) h0) n) ==
         app_n mark_hash (mkHinput (input b2) h0) n) ->
      ((input b1) == (input b2)).
    Proof.
      case: n=> [| n' /= /appn_mark_hash/andP [/eqP ->]]; last by rewrite eqxx.
      by rewrite eq_i_ch /= eqxx Bool.andb_true_r.
    Qed.

    Definition mu_ext (mu : B -> B) : (hash B) -> (hash B):=
      fun b => (mkHinput (mu (input b)) (current_hash b)).

    Hypothesis to_string : h -> B.
    Hypothesis to_string_inj : injective to_string.
    Definition label_bnode (hb : (hash B)) : B :=
      to_string (current_hash hb).


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

      Definition eqb_b_hterm (T : countType) (b : B) (ht : (term I (hash_alt T B) L)) : bool :=
        if ht is Bnode hb then b == (input hb) else false.

      Lemma eqb_b_hterm_is_bnode b (ht : hterm) : eqb_b_hterm b ht -> is_bnode ht.
      Proof. by case ht. Qed.

      Lemma eqb_b_hterm_trans (T : countType) (b b': B) (ht : (term I (hash_alt T B) L)) :
        eqb_b_hterm b ht -> eqb_b_hterm b' ht -> b = b'.
      Proof. by case: ht=> // ? /eqP-> /eqP->. Qed.

      Definition lookup_hash (hb : hterm) : option (hash B) :=
        if hb is Bnode hin then some hin else None.

      Definition lookup_hash_default_ (T : countType) (t0 : T) (hb : (term I (hash_alt T B) L) ) : T :=
        if hb is Bnode hin then current_hash hin else t0.

      Definition lookup_hash_default (hb : hterm) : h :=
        lookup_hash_default_ herror hb.

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

      Definition label_term (htrm : hterm) : term I B L :=
        relabeling_term label_bnode htrm.

      Definition term_hash (trm : hterm) : h :=
        match trm with
        | Iri x | Lit x => hashTerm (term_of_hterm trm)
        | Bnode hb => current_hash hb
        end.

      Definition cmp_bnode (b : B) (ht : hterm) : bool :=
        match ht with
        | Bnode hin => b == (input hin)
        | _ => false
        end.

      Definition mark_bnode (b : hterm) : hterm :=
        match b with
        | Iri i| Lit i => Bnode (mkHinput b0 herror)
        | Bnode hb=> Bnode (mark_hash hb)
        end.

      Lemma mark_bnode_inj g: {in (bnodes g), injective mark_bnode}.
      Proof. move=> x in_bns y.
             (* with just x in bnodes? and not y? *)
             case: x in_bns; case y=> x' y'; rewrite ?i_in_bnodes ?l_in_bnodes // => in_bns /=
                 => [[]] i_eq /eqP; rewrite ?hashTuple_neq_error //
                 => /eqP/hashTuple_inj []=> ch_eq.
             by f_equal; apply /eqP; rewrite eq_i_ch i_eq ch_eq !eqxx.
      Qed.

      Definition relabeling_hterm (mu : B -> B) ht : hterm :=
        relabeling_term (mu_ext mu) ht.

      (* Definition relabeling_pterm (T : countType) (mu : B -> B) ht : (term I (hash_alt T B) L) := *)
      (*   relabeling_term (mu_ext mu) ht. *)

      Lemma lookup_hash_relabeling ht mu: (lookup_hash_default ht) = (lookup_hash_default (relabeling_hterm mu ht)).
      Proof. by case ht. Qed.

      (* Lemma lookup_hash__relabeling (T : countType) (ht: term I (hash_alt T B) L) (mu : B -> B) n0 : (lookup_hash_default_ n0 ht) = (lookup_hash_default_ n0 (relabeling_hterm mu ht)). *)
      (* Proof. case ht=> //=b. Qed. *)

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

      Definition label_triple ht : triple I B L :=
        relabeling_triple label_bnode ht.

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

      Definition init_hash_ts_nat (ts : seq (triple I B L)) : (seq (triple I (hash_alt nat B) L)) :=
        relabeling_seq_triple init_bnode_nat ts.

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

      Lemma mark_bnode_init_hash_ts_mark_hash ts b n:
        Bnode b \in bnodes_ts (init_hash_ts ts) ->
                    app_n mark_bnode (Bnode b) n =
                      Bnode (app_n mark_hash (mkHinput (input b) h0) n).
      Proof. move=> /init_hash_ts_h0 b_hash.
             elim n=> /=[| n' IHn]; last by rewrite IHn.
             by congr Bnode; case: b b_hash=> /= [[]] ? ? /= ->.
      Qed.

      Lemma mark_bnode_init_hash_mark_hash g b n:
        Bnode b \in bnodes (init_hash g) ->
                    app_n mark_bnode (Bnode b) n =
                      Bnode (app_n mark_hash (mkHinput (input b) h0) n).
      Proof. by apply mark_bnode_init_hash_ts_mark_hash. Qed.

      Lemma eq_appn_init_ts_eq_num b1 b2 ts (b1in_bns : Bnode b1 \in bnodes_ts (init_hash_ts ts))
        (b2in_bns : Bnode b2 \in bnodes_ts (init_hash_ts ts)) n m :
        (app_n mark_bnode (Bnode b1) n) =
          (app_n mark_bnode (Bnode b2) m) ->
        n = m.
      Proof.
        have b1_hash := init_hash_ts_h0 b1in_bns.
        have b2_hash := init_hash_ts_h0 b2in_bns.
        rewrite (mark_bnode_init_hash_ts_mark_hash n b1in_bns) (mark_bnode_init_hash_ts_mark_hash m b2in_bns).
        elim: n m=> [// m | n' IHn m]; first by case: m=> [//| m' [_ /eqP]]; rewrite eq_sym hashTuple_neq_init.
        + case: m IHn=> [//| m'] IHn []; first by move=> _ /eqP /=; rewrite hashTuple_neq_init.
          - move=> eq_i /hashTuple_inj [eq_ch].
            by rewrite (IHn m')=> //; congr Bnode; apply /eqP; rewrite eq_i_ch eq_i eq_ch !eqxx.
      Qed.

      Lemma eq_appn_init_eq_num b1 b2 g (b1in_bns : Bnode b1 \in bnodes (init_hash g))
        (b2in_bns : Bnode b2 \in bnodes (init_hash g)) n m :
        (app_n mark_bnode (Bnode b1) n) =
          (app_n mark_bnode (Bnode b2) m) ->
        n = m.
      Proof. by apply (eq_appn_init_ts_eq_num b1in_bns). Qed.

      Lemma app_n_mark_ts_eq_bns (b1 b2: hash B) ts (b1in_bns : Bnode b1 \in bnodes_ts (init_hash_ts ts))
        (b2in_bns : Bnode b2 \in bnodes_ts (init_hash_ts ts)) n:
        (app_n mark_bnode (Bnode b1) n) == (app_n mark_bnode (Bnode b2) n) ->
        (@Bnode I (hash B) L b1) == (Bnode b2).
      Proof.
        rewrite (mark_bnode_init_hash_ts_mark_hash n b1in_bns) (mark_bnode_init_hash_ts_mark_hash n b2in_bns)
                => /eqP [/eqP] /appn_mark_hash_eq_input eq_i; apply /eqP; congr Bnode.
        by apply /eqP; rewrite eq_i_ch eq_i (init_hash_ts_h0 b1in_bns) (init_hash_ts_h0 b2in_bns) eqxx.
      Qed.

      Lemma app_n_mark_eq_bns (b1 b2: hash B) g (b1in_bns : Bnode b1 \in bnodes (init_hash g))
        (b2in_bns : Bnode b2 \in bnodes (init_hash g)) n:
        (app_n mark_bnode (Bnode b1) n) == (app_n mark_bnode (Bnode b2) n) ->
        (@Bnode I (hash B) L b1) == (Bnode b2).
      Proof. by apply (app_n_mark_ts_eq_bns b1in_bns). Qed.

      Lemma can_app_n_mb_init_ts ts b1 b2 (b1_bns : Bnode b1 \in bnodes_ts (init_hash_ts ts))
        (b2_bns : Bnode b2 \in bnodes_ts (init_hash_ts ts)) n m :
        app_n mark_bnode (Bnode b1) n = app_n mark_bnode (Bnode b2) m ->
        (@Bnode I (hash B) L b1 == Bnode b2) && (n == m).
      Proof.
        move=> injH.
        have nmeq := eq_appn_init_ts_eq_num b1_bns b2_bns injH.
        by move: injH=> /eqP; rewrite nmeq eqxx andbT; apply: app_n_mark_ts_eq_bns b1_bns b2_bns _.
      Qed.

      Lemma can_app_n_mb_init g b1 b2 (b1_bns : Bnode b1 \in bnodes (init_hash g))
        (b2_bns : Bnode b2 \in bnodes (init_hash g)) n m :
        app_n mark_bnode (Bnode b1) n = app_n mark_bnode (Bnode b2) m ->
        (@Bnode I (hash B) L b1 == Bnode b2) && (n == m).
      Proof. by apply (can_app_n_mb_init_ts b1_bns). Qed.

      Definition label_ts (ts : hgraph) : seq (triple I B L) :=
        relabeling_seq_triple label_bnode ts.

      Definition label (g : hgraph) us : rdf_graph I B L :=
        @relabeling _ _ _ _ label_bnode g us.

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

      Definition lookup_bnode_in_graph_default (g : hgraph) (b : B) : h :=
        if lookup_bnode_in_graph g b is Some trm then term_hash trm else herror.

      Definition relabeling_hgraph (mu : B -> B) (g: hgraph) us : hgraph :=
        @relabeling _ _ _ _ (mu_ext mu) g us.

      Lemma eqb_b_hterm_relabeling b ht (mu : B -> B) :
        eqb_b_hterm b ht ->
        eqb_b_hterm (mu b) (relabeling_hterm mu ht).
      Proof. by case: ht=> //? /eqP ->; rewrite /eqb_b_hterm/= eqxx. Qed.

    End Hgraph.

    Section Partition.

      (* change for finset *)
      Fixpoint partitionate (f : hterm -> bool) (s : seq hterm) : seq hterm * seq hterm :=
        match s with
        | nil => (nil, nil)
        | x :: tl => let (g,d) := partitionate f tl in
                     if f x then (x::g,d) else (g,x::d)
        end.

      Definition partitionate' (f : hterm -> bool) (s : seq hterm) : seq hterm * seq hterm :=
        (filter f s, filter (negb \o f) s).

      (* should be parameterized by an hgraph
         part shoud be the finset of (hash B) that shares hash in g *)
      Definition part := seq (hash B).

      (* the finset of parts in g *)
      Definition partition := seq part.

      Definition mkPartition_ts (ts : hts) : partition :=
        let bnodes := (bnodes_ts ts) in
        let equiv := (fun b => (fun t=> eq_hash b t)) in
        (* undup up to permutation *)
        let P := undup (map (fun b=> (partitionate (equiv b) bnodes).1 ) bnodes) in
        let ohs := map (fun bs => map lookup_hash bs) P in
        map someT_to_T ohs.

      Definition mkPartition (g : hgraph) : partition :=
        mkPartition_ts (graph g).

      Definition is_trivial (p : part) : bool :=
        size p == 1%N.

      Definition is_non_trivial (p : part) : bool :=
        ~~ is_trivial p.

      (* assumes order and no dup in parts *)
      Definition cmp_part (p1 p2 : part) : bool :=
        all2 (fun b1 b2 => input b1 == input b2) p1 p2.

      Definition is_fine (P : partition) : bool :=
        all is_trivial P.

      Definition is_coarse (P : partition) : bool :=
        size P == 1%N.

      Definition is_intermediate (P : partition) :=
        ~~ is_fine P && ~~ is_coarse P.

      (* assumes order and no dup in partition *)
      (* answers true if every part in the partition of g is equal to the respective part in h *)
      Definition cmp_partition_ts (g h: hts) : bool :=
        let Pg := mkPartition_ts g in
        let Ph := mkPartition_ts h in
        all2 (fun p1 p2 => cmp_part p1 p2) Pg Ph.

      Definition cmp_partition (g h: hgraph) : bool :=
        cmp_partition_ts (graph g) (graph h).

      (* algorithm 3, lines 9-10
       chooses the canonical part which is not trivial *)
      Fixpoint choose_part (P : partition) : part :=
        match P with
        | nil => nil (* FIXME: is this the good way to do it? *)
        | cons p t => if is_trivial p then choose_part t else p
        end.

      (* choose canonical graph from sequence of graphs that have fine partitions *)
      Definition choose_graph (gs : seq hgraph) : hgraph :=
        if insub gs : {? x | all (is_fine \o mkPartition) x} is Some _
        then foldl Order.max empty_rdf_graph gs
        else empty_rdf_graph.

    End Partition.

    Section Blabel.
      Variable hashBag : seq h -> h.
      Hypothesis hashBag_assoc : forall (l1 l2 l3: seq h),
          hashBag ([:: hashBag (l1 ++ l2)] ++ l3) = hashBag (l1 ++ [:: hashBag (l2 ++ l3)]).
      Hypothesis hashBag_comm : forall (l1 l2: seq h),
          hashBag (l1 ++ l2) = hashBag (l2 ++ l1).

      Lemma hasTuple_neq_errorP s: hashTuple s = herror -> False.
      Proof. by apply /eqP; rewrite /negb hashTuple_neq_error. Qed.

      Section Algorithm1.

        Definition new_hash (s p o : hterm) gacc h_dflt : option ((hash B) * (hash B)) :=
          if s is Bnode hb
          then
            let c := hashTuple [:: (term_hash o) ; (term_hash p) ; h_dflt] in
            let b_curr := lookup_bnode_in_graph_default gacc (input hb) in
            Some (hb,(mkHinput (input hb) (hashBag [:: c ; b_curr ])))
          else None.

        Definition new_hash_fwd (s p o: hterm) gacc : option ((hash B) * (hash B)) :=
          new_hash s p o gacc hfwd.

        Definition new_hash_bwd (s p o : hterm) gacc : option ((hash B) * (hash B)) :=
          new_hash o p s gacc hbwd.

        Axiom todo : forall {t}, t.

        (* Algorithm 1, lines 12-17
       update the hashes of blank nodes using the neighborhood
       it hashes differently outgoing edges from incoming ones *)
        Definition update_bnodes (g : hgraph) : hgraph :=
          let fix help g gacc hfun :=
            match g with
            | nil => gacc
            | cons t ts => let (s,p,o,_,_) := t : htriple in
                           let newhash := hfun s p o gacc in
                           if newhash is Some (hb,hb')
                           then let gacc' := @replace_bnode hb hb' gacc todo in
                                help ts gacc' hfun
                           else help ts gacc hfun
            end in
          let g_fwd := help g g new_hash_fwd in
          help g g_fwd new_hash_bwd.

        (* Algorithm 1, lines 9-18
       the iteration: computes the update of blank nodes until
           - the partition is fine
           - the partition did not change with respect to the previous one
         *)
        Fixpoint iterate (g : hgraph) (fuel : nat) : hgraph :=
          match fuel with
          | O => g
          | S n' =>
              let h := update_bnodes g in
              if cmp_partition g h || is_fine (mkPartition h) then h else
                iterate h n'
          end.

        Definition hashNodes_initialized (g : hgraph) : hgraph :=
          iterate g (size (graph g)).

        (* need the lemma stating hashNodes terminates without
       getting out of fuel *)
        (* Algorithm 1*)
        Definition hashNodes (g : rdf_graph _ _ _) : hgraph :=
          hashNodes_initialized (init_hash g).

      End Algorithm1.

      Section Algorithm2.
        (* Definition 4.6 ≡ ~G *)
        Definition reachability_rel (g : hgraph) (t1 t2 : htriple) : bool :=
          let (s1, _, o1, _, _) := t1 in
          let (s2, _, o2, _, _) := t2 in
          let s1s2 := (s1 == s2) && is_bnode s1 in
          let s1o2 := (s1 == o2) && is_bnode s1 in
          let o1s2 := (o1 == s2) && is_bnode o1 in
          let o1o2 := (o1 == o2) && is_bnode o1 in
          s1s2 || s1o2 || o1s2 || o1o2.

        (* Algorithm 2, line 2:
       computes the connected components based on definition 4.6 (~G)
         *)
        (* Definition blank_node_split (t u v : Type) (g : rdf_graph t u v) : seq (rdf_graph t u v). *)
        (* Proof. *)
        (* compute the graph G,
         where V := g and
         (t,u) : (triple I B L * triple I B L) \in E iff
         [:: t ; u] is graph and bnodes(t) ∩ bnodes(u) ≠ ϕ

       Then compute the connected componens using reachability rel*)
        (* Admitted. *)

        (* The graph that contains all (and only the) ground triples of G *)
        (* Definition ground_split {t u v : Type} (g : rdf_graph t u v) : rdf_graph t u v := *)
        (*   let groundTriples := filter (fun t => is_ground_triple t) g in *)
        (*   mkRdfGraph groundTriples. *)

        (* Lemma merge_split {t u v : Type} (g : rdf_graph t u v) : *)
        (*   merge_rdf_graph (merge_seq_rdf_graph (blank_node_split g)) (ground_split g) = g. *)
        (* Admitted. *)

        (* Algorithm 2 *)
        (* Definition hashBnodesPerSplit (g : hgraph) : hgraph := *)
        (*   let splitG := blank_node_split g in *)
        (*   foldr (@merge_rdf_graph _ _ _) (empty_rdf_graph _ _ _) splitG. *)

      End Algorithm2.

      Section Algorithm3.

        (* Algorithm 3, lines 13-14 when color refine is hashBnodes_initialized.
       b is_bnode *)
        Definition distinguishBnode g (color_refine : hgraph -> hgraph ) (b : hash B) : hgraph :=
          let b' := mark_hash b in
          let g' := @replace_bnode b b' g todo in
          color_refine g'.


        (* give partition and proof that partition is not fine *)
        (* or compute it again ... *)
        (* Algorithm 3, function distinguish, lines 9-20
       lines 16-18 were moved to a higher level: should consume more space
       FIXME just call distinguish_ with not fine partitions so
       is not needed to repeat the question *)
        Fixpoint distinguish_ g (color : hgraph -> hgraph) (fuel:nat) : hgraph :=
          match fuel with
          | O => g
          | S n' =>
              let P := mkPartition g in
              if is_fine P then g
              else
                let p := choose_part P in
                let gs := map (distinguishBnode g color) p in
                let just_fine := (fun g: hgraph =>
                                    if is_fine (mkPartition g) then g
                                    else distinguish_ g color n') in
                choose_graph (map just_fine gs)
          end.

        (* Algorithm 3, function distinguish
       when color_refine is hashBnodes_initialized *)
        Definition distinguish g (color_refine : hgraph -> hgraph) : hgraph :=
          distinguish_ g color_refine (size g).

      End Algorithm3.

      Section Isocanonicalise.

        Definition isoCanonicalTemplate g (color color_refine: hgraph -> hgraph)
          p_refining : rdf_graph I B L:=
          let g' := color (init_hash g) in
          let P := mkPartition g' in
          let g_iso := if is_fine P then g' else p_refining g' color_refine in
          @label g_iso todo.

        (* first approach *)
        Definition justDistinguish g :=
          isoCanonicalTemplate g id id distinguish.

        Lemma distinguish_preserves_isomorphism g : iso (justDistinguish g) g.
        Proof.
        Admitted.

        Definition isoCanonicalNoIter g :=
          isoCanonicalTemplate g update_bnodes update_bnodes distinguish.

        Definition isoCanonicalIter g :=
          isoCanonicalTemplate g hashNodes_initialized hashNodes_initialized distinguish.

        (* Definition blabel g := *)
        (*   isoCanonicalTemplate g hashBnodesPerSplit hashNodes_initialized distinguish. *)

      End Isocanonicalise.
    End Blabel.

    Section Kmapping.

      Definition k_distinguish bns : seq (term I (hash B) L) :=
        let fix help bns n :=
          match bns with
          | nil => nil
          | trm :: trms => app_n mark_bnode trm n :: help trms (S n)
          end in
        help bns 0.

      Definition ak_mapping_ts (ts : seq (triple I B L)) : seq hterm :=
        let bns := bnodes_ts (init_hash_ts ts) in
        mapi (app_n mark_bnode) bns.

      Definition ak_mapping (g : rdf_graph I B L) : seq hterm :=
        ak_mapping_ts (graph g).

      Lemma empty_ak_mapping : ak_mapping empty_rdf_graph = [::]. Proof. by []. Qed.


      Definition build_kmapping_from_seq_alt (trms : seq (term I (hash_alt nat B) L)) : B -> B :=
        fun b =>
          if has (eqb_b_hterm b) trms then
            let the_bnode := nth (Bnode (mkHinput b n0)) trms (find (eqb_b_hterm b) trms) in
            to_string_nat (lookup_hash_default_ n0 the_bnode)
          else
            b.

      Definition build_kmapping_from_seq (trms : seq hterm) : B -> B :=
        fun b =>
          if has (eqb_b_hterm b) trms then
            let the_bnode := nth (Bnode (mkHinput b herror)) trms (find (eqb_b_hterm b) trms) in
            to_string (lookup_hash_default the_bnode)
          else
            b.

      Definition k_mapping_alt (ts : seq (triple I B L)) : seq (triple I B L) :=
        let perms :=  permutations (get_bts ts) in
        let all_maps := map
                          (map (fun an=> Bnode (mkHinput an.1 an.2)))
                          (map (fun s=> zip s (iota 0 (size s))) perms)
        in
        let mus := map build_kmapping_from_seq_alt all_maps in
        let isocans := map (fun mu => (relabeling_seq_triple mu ts)) mus in
        foldl Order.max [::] isocans.


      Definition k_mapping_ts (ts : seq (triple I B L)) : seq (triple I B L) :=
        let all_maps :=
          map (mapi (app_n mark_bnode)) (permutations (bnodes_ts (init_hash_ts ts))) in
        let mus := map build_kmapping_from_seq all_maps in
        let isocans := map (fun mu => (relabeling_seq_triple mu ts)) mus in
        foldl Order.max [::] isocans.

      Lemma app_mark_inj ts :
        {in zip (bnodes_ts (init_hash_ts ts)) (iota 0 (size (bnodes_ts (init_hash_ts ts)))) &,
              injective (fun an : hterm * nat => app_n mark_bnode an.1 an.2)}.
        Proof. set ts' := init_hash_ts ts.
        move=> [t n] [u m] /in_zip/andP [tin_bns n_iota] /in_zip/andP [uin_bns m_iota] /= eq_app_n.
        case: t tin_bns uin_bns eq_app_n; case: u
            => nt nu; rewrite ?i_in_bnodes_ts ?l_in_bnodes_ts // => nu_bns nt_bns injH.
        by apply /eqP; rewrite xpair_eqE; apply (can_app_n_mb_init_ts nu_bns nt_bns injH).
        Qed.

      Lemma k_mapping_seq_uniq_ts ts: uniq (mapi (app_n mark_bnode) (bnodes_ts (init_hash_ts ts))).
      Proof.
        set ts' := init_hash_ts ts.
        suffices f_inj : {in zip (bnodes_ts ts') (iota 0 (size (bnodes_ts ts'))) &,
    injective (fun an : hterm * nat => app_n mark_bnode an.1 an.2)}.
          by rewrite map_inj_in_uniq; first by apply (zip_uniq_l _ (uniq_bnodes_ts ts')).
        apply app_mark_inj.
      Qed.

      Lemma k_mapping_seq_uniq_graph g: uniq (mapi (app_n mark_bnode) (bnodes (init_hash g))).
      Proof. by apply k_mapping_seq_uniq_ts. Qed.

      Lemma k_mapping_seq_uniq_perm_eq_ts ts s: perm_eq s (bnodes_ts (init_hash_ts ts)) -> uniq (mapi (app_n mark_bnode) s).
      Proof. rewrite /mapi perm_sym=> perm_eq.
             suffices f_inj :  {in zip s (iota 0 (size s)) &, injective (fun an : hterm * nat => app_n mark_bnode an.1 an.2)}.
               by rewrite map_inj_in_uniq //; apply uniq_zip_iota.
             move=> [x1 n] [y1 m] /in_zip/andP [x1_ins n_iniota] /in_zip/andP [y1_ins m_iniota] /=.
             move: (all_bnodes_perm perm_eq x1_ins) (all_bnodes_perm perm_eq y1_ins).
             case :y1 x1_ins y1_ins; case x1=> // namey namex; rewrite -!(perm_mem perm_eq)=> y_ins x_ins _ _.
             by move=> ?; apply /eqP; rewrite xpair_eqE; apply (can_app_n_mb_init_ts y_ins).
      Qed.

      Lemma k_mapping_seq_uniq_perm_eq g s: perm_eq s (bnodes (init_hash g)) -> uniq (mapi (app_n mark_bnode) s).
      Proof. by apply k_mapping_seq_uniq_perm_eq_ts. Qed.

      Lemma nil_minimum (ts: seq (triple I B L)) : [::] <= ts.
      Proof. by case ts. Qed.

      Lemma eq_lookup_eq_hash ht1 ht2 :
        is_bnode ht1 -> is_bnode ht2 -> lookup_hash_default ht1 = lookup_hash_default ht2 ->
        exists h1 h2 h, (Bnode h1 == ht1) && (Bnode h2 == ht2) &&
                     (current_hash h1 == h) && (current_hash h2 == h).
      Proof. case: ht1=> //b1; case ht2=> //b2=> _ _ /= eqch.
             by exists b1; exists b2; exists (current_hash b2); rewrite eqch !eqxx.
      Qed.

      Lemma all_kmapb_b s : all [eta all [eta is_bnode (L:=L)]] s ->
                            all (all [eta is_bnode (L:=L)]) [seq mapi (app_n mark_bnode) i | i <- s].
      Proof. elim: s=> // a l IHl /andP[bhd btl] /=. rewrite IHl // andbT {IHl}.
             move: bhd. rewrite /mapi all_map=> allb_a.
             set an := zip a (iota 0 (size a)).
             suffices : all (fun b=> is_bnode b.1) an.
             elim: an=> // anhd antl IHantl /andP[banhd bantl] /=.
             rewrite IHantl // andbT {IHantl bantl}.
             move: banhd. case anhd=> [[]]//=b n _.
             by elim: n=> //= n'; case (app_n mark_bnode (Bnode b) n')=> //.
             by apply all_zip1.
      Qed.

      Lemma minn_refl n : minn n n = n.
      Proof. by rewrite /minn; case e: (_ < _)%N. Qed.

      Lemma nth_mapzip (T1 T2 : Type) (S0 T0 : eqType) (x0 : S0) (y0 : T0) [s : seq S0] [t : seq T0] (i : nat) :
              size s = size t -> nth (@Bnode T1 (hash_alt T0 S0) T2 (mkHinput x0 y0)) [seq Bnode (mkHinput an.1 an.2) | an <- zip s t ] i = Bnode (mkHinput (nth x0 s i) (nth y0 t i)).
        Proof.
            move=> eqsize.
            case/orP : (leqVgt (size t) i)=> leq.
            + suffices notin : (size [seq Bnode (mkHinput an.1 an.2) | an <- zip s t] <= i)%N.
                by rewrite !nth_default // eqsize.
              by move=> ? ? ; rewrite size_map size_zip eqsize minn_refl.
            by rewrite (nth_map (x0,y0)) ?size_zip ?eqsize ?minn_refl // ; congr Bnode; apply/eqP; rewrite eq_i_ch /= nth_zip //= !eqxx.
        Qed.

        Lemma get_bts_in_l_perm (ts : seq (triple I B L)) u
          (mem : u \in [seq [seq Bnode (mkHinput an.1 an.2) | an <- i]
                       | i <- [seq zip s (iota 0 (size s)) | s <- permutations (get_bts ts)]]) :
          forall b, b \in get_bts ts -> has (eqb_b_hterm b) u.
        Proof.
          move=> b bin.
          move/mapP : mem=> [/= bns /mapP[/= bs]]. rewrite mem_permutations=> /perm_mem peq -> ->.
          rewrite seq.has_map /=.
          apply/hasP=> /=.
          have eqsize : size bs = size (iota 0 (size bs)) by rewrite size_iota.
          rewrite -peq in bin.
          have [/= st [stin [<- [t2 t2eq]]]]:= in_zip_l eqsize bin.
          by exists st.
        Qed.

    Lemma find_index_eqbb (T : countType) bs s (bn : B) : size s = size bs ->
                          find (@eqb_b_hterm T bn) [seq Bnode (mkHinput an.1 an.2) | an <- zip bs s] =
                            index bn bs.
          elim: bs s => [| a l IHl]; first by move=> ?; rewrite zip0s.
          by case =>  [//| b l2] /= [eqsize_tl]; rewrite eq_sym IHl //.
    Qed.

      Lemma nth_bperms (ts : seq (triple I B L))
          (uniq_ts : uniq ts)
          (bn : B) db dn
          (bin : bn \in get_bts ts)
          u (mem : u \in  [seq [seq Bnode (mkHinput an.1 an.2) | an <- i] | i <-
                                    [seq zip s (iota 0 (size s)) | s <- permutations (get_bts ts)]]) :
                                       exists n : nat, nth (Bnode (mkHinput db dn)) u (find (eqb_b_hterm bn) u) = Bnode (mkHinput bn n).
        Proof.
          move/mapP : mem=> [/= bns /mapP[/= bs]].
          rewrite mem_permutations=> peq_bs bnseq ueq; rewrite ueq bnseq.
          have permbs := perm_mem peq_bs.
          have uniqbs := perm_uniq peq_bs.
          suffices H1 :
 (find (eqb_b_hterm bn) [seq Bnode (mkHinput an.1 an.2) | an <- zip bs (iota 0 (size bs))]) =
   (index bn bs).
          suffices H2 : forall [S0 T0 : eqType] (x : S0) (y : T0) [s : seq S0] [t : seq T0] (i : nat),
              size s = size t -> nth (Bnode (mkHinput x y)) [seq Bnode (mkHinput an.1 an.2) | an <- zip s t ] i = Bnode (mkHinput (nth x s i) (nth y t i)).
            exists (index bn bs).
            rewrite H2; last by rewrite size_iota.
            congr Bnode.
            rewrite H1 //; apply/eqP; rewrite eq_i_ch /=; apply /andP; split; apply/eqP.
              + by rewrite nth_index // permbs.
              + by rewrite nth_iota // index_mem permbs //.
            by apply nth_mapzip.
          by apply find_index_eqbb; rewrite size_iota.
        Qed.

    Lemma in_perm_luh_inj (ts : seq (triple I B L))
                  u :
      u \in [seq [seq Bnode (mkHinput an.1 an.2) | an <- i]
            | i <- [seq zip s (iota 0 (size s)) | s <- permutations (get_bts ts)]] ->
            {in u&, injective (lookup_hash_default_ n0)}.
      Proof.
        move => /mapP[tgd_perm tgin ->] /=.
        move=> ht1 ht2 /mapP[tgd_instx tgdinsxin ->] /mapP[tgd_insty tgdinsyin ->].
        move/mapP : tgin=> [aperm pinperm tgdeq].
        rewrite tgdeq in tgdinsxin tgdinsyin.
        move=> /= eq2; congr Bnode.
        suffices minnrefl s : minn (size s) (size s) = size s.
          have eqsize : size aperm = size (iota 0 (size aperm)) by rewrite size_iota.
          move/nthP : tgdinsxin=> /= /(_ tgd_instx)[xn]; rewrite size_zip -eqsize minnrefl=> sizex.
          move: eq2; case : tgd_instx=> /= tagx1 tagx2 eq2.
          rewrite nth_zip // => /eqP; rewrite xpair_eqE=> /andP[/eqP x1nth /eqP x2nth].
          move/nthP : tgdinsyin=> /= /(_ tgd_insty)[yn]; rewrite size_zip -eqsize minnrefl=> sizey.
          move: eq2; case: tgd_insty=> /= tagy1 tagy2 eq2.
          rewrite nth_zip // => /eqP; rewrite xpair_eqE=> /andP[/eqP y1nth /eqP y2nth].
          rewrite -x2nth -y2nth in eq2.
          rewrite -x1nth{x1nth} -x2nth{x2nth} -y1nth{y1nth} -y2nth{y2nth}.
          move: eq2; rewrite (set_nth_default tagx2); last by rewrite -eqsize.
          move=> /eqP; rewrite nth_uniq //; rewrite -?eqsize //; last by apply iota_uniq.
          by move=> /eqP ->; apply/eqP; rewrite eq_i_ch /= eqxx andbC /= (set_nth_default tagx1) //.
      by move=> ?; apply minn_refl.
      Qed.

  Lemma labeled_perm_inj
    (ts : seq (triple I B L))
    (uniq_ts : uniq ts)
    u
    (mem : u \in [seq [seq Bnode (mkHinput an.1 an.2) | an <- i] | i <- [seq zip s (iota 0 (size s)) | s <- permutations (get_bts ts)]]) :
{in get_bts ts &, injective (build_kmapping_from_seq_alt u)}.
    Proof.
      move=> x y xin yin;rewrite /build_kmapping_from_seq_alt.
      suffices mem_has: forall b, b \in get_bts ts -> has (eqb_b_hterm b) u.
        rewrite !mem_has // => /to_string_nat_inj.
        set dflt := (Bnode (mkHinput y n0)).
        have ->: (nth (Bnode (mkHinput x n0)) u (find (eqb_b_hterm x) u)) = (nth dflt u (find (eqb_b_hterm x) u)) by rewrite (set_nth_default (Bnode (mkHinput x n0))) // -has_find mem_has.
        move: (nth_bperms uniq_ts y n0 xin mem) (nth_bperms uniq_ts y n0 yin mem)=> [n eqnnthx] [m eqmnthy].
        rewrite eqnnthx eqmnthy.
        suffices J: {in u&, injective (lookup_hash_default_ n0)}.
          move=> /J; rewrite -eqnnthx -eqmnthy.
          move : (mem_has x xin) (mem_has y yin); rewrite !has_find=> nthxin nthyin.
          by rewrite !mem_nth // => /(_ isT isT); rewrite eqnnthx eqmnthy; move=> [->].
        by apply (in_perm_luh_inj mem).
    by apply get_bts_in_l_perm.
    Qed.

    Lemma auto_iso_rel_perm (ts : seq (triple I B L))
      (uts : uniq ts)
      (perm : seq B)
      (inperm : perm \in permutations (get_bts ts))
      (mu_inj : {in get_bts ts&, injective (build_kmapping_from_seq_alt [seq Bnode (mkHinput an.1 an.2) | an <- zip perm (iota 0 (size perm))])}) :

      is_pre_iso_ts ts (relabeling_seq_triple (build_kmapping_from_seq_alt [seq Bnode (mkHinput an.1 an.2) | an <- zip perm (iota 0 (size perm))]) ts) (build_kmapping_from_seq_alt [seq Bnode (mkHinput an.1 an.2) | an <- zip perm (iota 0 (size perm))]).
    Proof. set sgen := [seq Bnode (mkHinput an.1 an.2) | an <- zip perm (iota 0 (size perm))] : seq (term I (hash_alt nat B) L).

           apply uniq_perm.
           + by rewrite map_inj_in_uniq // uniq_get_bts.
           + by rewrite uniq_get_bts.
           + suffices rt_inj: {in ts &, injective (relabeling_triple (build_kmapping_from_seq_alt sgen))}.
              by rewrite -(get_bs_map _ (all_bnodes_ts _)); apply eq_mem_pmap=> b; rewrite bnodes_ts_relabel_mem.
            by apply: inj_get_bts_inj_ts mu_inj.
      Qed.

      Lemma candidate_in_perm (ts : seq (triple I B L)) perm (bin : perm \in permutations (get_bts ts)) :
  [seq (@Bnode I (hash_alt nat B) L (mkHinput an.1 an.2)) | an <- zip perm (iota 0 (size perm))]
    \in [seq [seq Bnode (mkHinput an.1 an.2) | an <- i]
        | i <- [seq zip s (iota 0 (size s)) | s <- permutations (get_bts ts)]].
        Proof.
          by apply/mapP; exists (zip perm (iota 0 (size perm)))=> //; apply /mapP; exists perm=> //.
        Qed.

      Lemma uniq_k_mapping_res (ts : rdf_graph I B L) : uniq (k_mapping_alt ts).
      Proof.
      case: ts => ts uniq_ts /=; rewrite /k_mapping_alt.
      set perm_bs := permutations _.
      set tg_labels_perm := [seq zip s (iota 0 (size s)) | s <- perm_bs].
      set label_perm := [seq [seq Bnode (mkHinput an.1 an.2) | an <- i] | i <- tg_labels_perm].
      set build_kmap := [seq build_kmapping_from_seq_alt i | i <- label_perm].
      set relab := [seq relabeling_seq_triple mu ts | mu <- build_kmap].
      suffices relab_uniq : all uniq relab.
        by case: (foldl_max relab [::])=> [-> //|]; apply: (allP relab_uniq).
      apply /allP; rewrite /relab/build_kmap -map_comp=> t /mapP[u mem ->] {relab build_kmap}; apply uniq_relabeling_pre_iso=> //.
      move/mapP : mem=> /= [x /mapP[/= perm bin ->]] ->.
      suffices mu_inj : {in get_bts ts&, injective (build_kmapping_from_seq_alt [seq Bnode (mkHinput an.1 an.2) | an <- zip perm (iota 0 (size perm))])}.
        by apply auto_iso_rel_perm.
      by apply (labeled_perm_inj uniq_ts (candidate_in_perm bin)).
      Qed.

      Definition k_mapping (g : rdf_graph I B L) : rdf_graph I B L :=
        @mkRdfGraph I B L (k_mapping_alt (graph g)) (uniq_k_mapping_res g).

      Lemma injection_kmap b b' (ht : hterm ) s (eb: eqb_b_hterm b ht) (eb': eqb_b_hterm b' ht):
        (build_kmapping_from_seq (mapi (app_n mark_bnode) s) b) =
          (build_kmapping_from_seq (mapi (app_n mark_bnode) s) b').
      Proof. by rewrite (eqb_b_hterm_trans eb eb'). Qed.

      Lemma size_neq0 (T : eqType) (s : seq T): (size s != 0) = (s != [::]).
      Proof. by congr negb; apply size_eq0. Qed.

      Lemma map_kmap b n s :
        (build_kmapping_from_seq s b) = n ->
        (has (eqb_b_hterm b) s) ->
        forall s' (f : B -> B), injective f -> s' = map (relabeling_hterm f) s ->
                                (build_kmapping_from_seq s' (f b)) = n.
      Proof.
        elim: s=> [| hd tl IHtl]; first by rewrite has_nil.
        move=> beq has_b s'; case: s'=> [//| hd' tl'] f injF [eqhd eqtl].
        move: IHtl; rewrite /build_kmapping_from_seq eqhd eqtl -map_cons -has_map_eqbb ; last by apply injF.
        rewrite has_b /= -eqb_b_hterm_relabel; last by apply injF. rewrite /= in has_b.
        case/orP: has_b beq; first by rewrite /build_kmapping_from_seq=> H /=; rewrite H; case hd=> // name /=.
        + rewrite /build_kmapping_from_seq /= ; case e: (eqb_b_hterm b hd)
                  => /=; first by move=> _; rewrite -lookup_hash_relabeling.
          move=> /= has_tl /=; rewrite has_tl=> eq IHtl.
          have IHtl' := IHtl eq isT tl' f injF eqtl.
          by rewrite eqtl -has_map_eqbb ?has_tl in IHtl'; last by apply injF.
      Qed.

      (* Lemma lt0_size_permutations (T : eqType) (s : seq T) : 0 < size (permutations s). *)
      (* Proof. elim: s=> [//|a l IHl]. *)
      (*        suffices lt : size (permutations l) <= size (permutations (a :: l)). *)
      (*          by apply: Order.POrderTheory.lt_le_trans IHl lt. *)
      (*          rewrite /permutations /=. rewrite /seq.perms_rec. *)
      (*          Admitted. *)
             (* rewrite !size_permutations. *)
             (* apply lt_trans. *)


      Lemma permutations_neq_nil (T : eqType) (s : seq T) : permutations s != [::].
      Proof. suffices: size (permutations s) != 0 by rewrite size_neq0.
             (* rewrite size_permutations. *)
             (* elim: s=> [//| a l IHl]. *)
      Admitted.
             (* rewrite size_permutations /=. *)
             (* rewrite -lt0n //. Abott. *)
        (*      Set Printing All. *)
        (*      apply lt0n_neq0.//.  *)

        (* elim: s=> [| a l IHl]; first by rewrite empty_permutations. *)
        (*      have /permutationsE: (0 < size (a :: l)) by []. *)
        (*      move=> peq. *)
        (*      rewrite /=. *)

      Lemma k_mapping_nil_is_nil ts: k_mapping_alt ts = [::] -> ts = [::].
        Proof.
          move=> /max_foldl_minimum /orP[]//.
          + rewrite -map_comp /= !map_nil_is_nil => /eqP.
            by apply contra_eq; rewrite permutations_neq_nil.
          + by rewrite -map_comp=> /mapP[/=xs /mapP[/= a ain]] -> => /eqP; rewrite eq_sym=> /eqP/relabeling_seq_triple_is_nil ->.
        Qed.

      Lemma kmapping_iso_out g: iso g (k_mapping g).
      Proof. rewrite /mapping_is_iso_mapping/k_mapping/iso/iso_ts/is_iso_ts.
             have := uniq_k_mapping_res g.
             case : g=> ts uts /=.
             rewrite /k_mapping_alt.
             case : (foldl_max ([seq relabeling_seq_triple mu0 ts
                   | mu0 <- [seq build_kmapping_from_seq_alt i
                               | i <- [seq [seq Bnode (mkHinput an.1 an.2) | an <- i]
                                         | i <- [seq zip s (iota 0 (size s))
                                               | s <- permutations (get_bts ts)]]]]) [::]).
             by move=> /k_mapping_nil_is_nil=> ts_nil; exists id; rewrite ts_nil.
             rewrite /= -map_comp=> /mapP /=[s sin H]; rewrite H.
             move=> ukres; exists (build_kmapping_from_seq_alt s).
             suffices preiso : is_pre_iso_ts ts (relabeling_seq_triple (build_kmapping_from_seq_alt s) ts) (build_kmapping_from_seq_alt s).
               by apply ts_pre_iso_iso=> //.
             move/mapP : sin=> /=[bn /mapP[/= perm inperm ->] ->].
             apply auto_iso_rel_perm=> //.
        by apply: labeled_perm_inj=> //; apply candidate_in_perm.
      Qed.

      Lemma iso_structure (ts1 ts2: seq (triple I B L)) :
        iso_ts ts1 ts2 -> ((ts1 == [::]) && (ts2 == [::]) || (ts1 != [::]) && (ts2 != [::])).
      Proof.
        rewrite /iso_ts/is_iso_ts /=; move=> [? /and3P [_ _]] ; case: ts1=> [|h1 tl1].
          + by rewrite relabeling_seq_triple_nil perm_sym=> /perm_nilP ->.
          + by apply contraTneq=> -> ; apply /perm_nilP.
      Qed.

      Lemma eq_mem_foldl_max [disp : unit] [T : orderType disp] [l1 l2 : seq T] [x y : T]:
        l1 =i l2 -> foldl Order.max x l1 = foldl Order.max x l2.
      Proof. Admitted.

      Lemma eq_mem_foldl_max_rdf [l1 l2 : seq (seq (triple I B L))] :
        (forall c1, c1 \in l1 -> exists c', c' \in l2 /\ c1 =i c') ->
        foldl Order.max [::] l1 =i foldl Order.max [::] l2.
      Proof. Admitted.

      Lemma build_from_nil (ts : seq (triple I B L)) :
        relabeling_seq_triple (build_kmapping_from_seq_alt [::]) ts = ts.
      Proof. by elim: ts=> [//| a l IHl]; by rewrite /= relabeling_triple_id IHl. Qed.

      Lemma index_map_in [T1 T2 : eqType] [f : T1 -> T2] (s : seq T1) :
  {in s&, injective f} -> forall (x : T1), x \in s -> index (f x) [seq f i | i <- s] = index x s.
      Proof. elim: s => [//| a t IHtl] inj_f x xin /=.
             case : ifP; first by move/eqP/inj_f; rewrite in_cons eqxx /==> /(_ isT) -> //; rewrite eqxx.
             case : ifP; first by move/eqP=> ->; rewrite eqxx //.
             move=> neq fneq; rewrite IHtl //.
             by move=> ? ? xinn yinn; apply inj_f; rewrite in_cons ?xinn ?yinn orbT.
             by move: xin; rewrite in_cons eq_sym neq /=.
      Qed.

      Lemma eqb_b_hterm_memP (b : B) (s : seq B) : b \in s -> has (eqb_b_hterm b)  [seq Bnode (mkHinput an.1 an.2) | an <- zip s (iota 0 (size s))].
      Proof.
        move=> b1in; apply/ (has_nthP (Bnode (mkHinput b 0))).
        exists (index b s).
        by rewrite size_map size_zip size_iota minn_refl index_mem.
        by rewrite nth_mapzip /= ?size_iota // nth_index // eqxx.
      Qed.

      Lemma out_of_build b s :
        b \in s -> uniq s ->
              build_kmapping_from_seq_alt [seq Bnode (mkHinput an.1 an.2) | an <- zip s (iota 0 (size s))] b =
                to_string_nat (nth 0 (iota 0 (size s)) (index b s)).
      Proof.
        move=> bin ubs.
        rewrite /build_kmapping_from_seq_alt (eqb_b_hterm_memP bin); congr to_string_nat.
        by rewrite find_index_eqbb ?size_iota // nth_mapzip ?size_iota //.
      Qed.

      Lemma iso_can_kmapping : isocanonical_mapping k_mapping.
      Proof.
        split=> [|g1 g2]; first by apply kmapping_iso_out.
        split=> [| isog1g2]; first by apply same_res_impl_iso_mapping; rewrite /mapping_is_iso_mapping; apply kmapping_iso_out.
        have: iso (k_mapping g1) (k_mapping g2).
        by apply: iso_can_trans _ isog1g2; rewrite /mapping_is_iso_mapping; apply kmapping_iso_out.
        rewrite /k_mapping/k_mapping_alt rdf_perm_mem_eq rdf_mem_eq_graph /iso /==> /=.
        rewrite -!map_comp.
        set cand1 :=
       [seq ((((relabeling_seq_triple (B2:=B))^~ g1 \o build_kmapping_from_seq_alt) \o
                map (fun an : B * nat => Bnode (mkHinput an.1 an.2))) \o
               (fun s : seq B => zip s (iota 0 (size s)))) i
          | i <- permutations (get_bts g1)].
        set cand2 :=
       [seq ((((relabeling_seq_triple (B2:=B))^~ g2 \o build_kmapping_from_seq_alt) \o
                map (fun an : B * nat => Bnode (mkHinput an.1 an.2))) \o
               (fun s : seq B => zip s (iota 0 (size s)))) i
          | i <- permutations (get_bts g2)].
        move=> isokg1kg2.
        suffices eq_can : (forall c1 : seq (triple I B L),
  c1 \in cand1 -> exists c' : seq (triple I B L), c' \in cand2 /\ c1 =i c').
          by move=> ?; rewrite (eq_mem_foldl_max_rdf eq_can).
        move=> c1 /mapP[/= pg1 pinperm  ->].
        have /perm_mem pg1mem : perm_eq pg1 (get_bts g1) by rewrite -mem_permutations.
        have /perm_uniq pg1uniq : perm_eq pg1 (get_bts g1) by rewrite -mem_permutations.
        rewrite mem_permutations in pinperm.
        rewrite /iso/iso_ts/is_iso_ts/is_pre_iso_ts in isog1g2.
        move : isog1g2=> [mu /and3P[piso12 urel peq]].
        apply (perm_map mu) in pinperm.
        have := (perm_trans pinperm piso12).
        rewrite -mem_permutations.
        set mu2 := (build_kmapping_from_seq_alt \o
                    map (fun an : B * nat => Bnode (mkHinput an.1 an.2)) \o
                   (fun s : seq B => zip s (iota 0 (size s)))) (map mu pg1).
        move=> peqg2; exists (relabeling_seq_triple mu2 g2).
        split; first by apply/mapP; exists (map mu pg1).
        rewrite /mu2/cand2 => trpl /=.
        have eqsize : size (map mu pg1) = size pg1 by rewrite size_map.
        (*  *)
        apply/mapP/mapP=> /= [[t tin ->]|[t tin ->]] .
        exists (relabeling_triple mu t); first by apply perm_mem in peq; rewrite -peq; apply map_f.
        have mu_inj : {in pg1 &, injective mu}. by move=> x y xin yin; apply (is_pre_iso_inj piso12); rewrite -pg1mem.
        suffices build_modulo_map : forall b, b \in pg1 ->
          build_kmapping_from_seq_alt [seq Bnode (mkHinput an.1 an.2) | an <- zip pg1 (iota 0 (size pg1))] b =
  build_kmapping_from_seq_alt
    [seq Bnode (mkHinput an.1 an.2) | an <- zip [seq mu i | i <- pg1] (iota 0 (size [seq mu i | i <- pg1]))]
    (mu b).
        case : t tin=> [[]]//s []p []o// sib pii tin //=;
        apply triple_inj=> //=; congr Bnode;
        rewrite build_modulo_map //;
        rewrite pg1mem; apply (mem_ts_mem_triple_bts tin);
        rewrite /bnodes_triple filter_undup mem_undup /= ?in_cons ?eqxx ?orbT //.
        suffices upg1 : uniq pg1.
        move=> b bin.
        rewrite (out_of_build bin upg1) out_of_build.
        congr to_string_nat; rewrite !nth_iota.
        rewrite index_map_in //.
        by rewrite index_mem; apply map_f.
        by rewrite index_mem.
        by apply map_f.
        by rewrite map_inj_in_uniq.
        by rewrite pg1uniq uniq_get_bts.
        + have : t \in (relabeling_seq_triple mu g1) by apply perm_mem in peq; rewrite peq.



      Lemma all_kmaps_bijective g : List.Forall (fun mu => bijective mu) [seq build_kmapping_from_seq i
                                                                         | i <- [seq mapi (app_n mark_bnode) i
                                                                                | i <- permutations (bnodes (init_hash g))]].
      Proof.
        have map2Listmap U V (f : U -> V) (s : seq U) : map f s = List.map f s. admit.
        have nth2Listnth U (d : U) (s : seq U) n : nth d s n = List.nth n s d. admit.
        have size2Listlength U (s : seq U) : List.length s = size s. admit.
        rewrite !map2Listmap !List.Forall_map.
        suffices step s : perm_eq s (bnodes (init_hash g)) -> bijective (build_kmapping_from_seq (mapi (app_n mark_bnode) s)).
        apply/List.Forall_nth=> i d lti. apply: step. rewrite -mem_permutations -nth2Listnth. apply: mem_nth.
        by rewrite -size2Listlength; apply/ltP.
        (* by using k_mapping_seq_uniq_perm_eq *)
        admit.
      Admitted.

      Section experiment.

      Lemma all_kmaps_local_bijective g : List.Forall (fun mu => {in (get_b g) , bijective mu}) [seq build_kmapping_from_seq i
                                                                         | i <- [seq mapi (app_n mark_bnode) i
                                                                                | i <- permutations (bnodes (init_hash g))]].
      Proof.
        have map2Listmap U V (f : U -> V) (s : seq U) : map f s = List.map f s. admit.
        have nth2Listnth U (d : U) (s : seq U) n : nth d s n = List.nth n s d. admit.
        have size2Listlength U (s : seq U) : List.length s = size s. admit.
        rewrite !map2Listmap !List.Forall_map.
        suffices step s : perm_eq s (bnodes (init_hash g)) -> {in (get_b g), bijective (build_kmapping_from_seq (mapi (app_n mark_bnode) s))}.
        apply/List.Forall_nth=> i d lti. apply: step. rewrite -mem_permutations -nth2Listnth. apply: mem_nth.
        by rewrite -size2Listlength; apply/ltP.
        have ext_pred_bij: forall (T1 T2 : eqType) (d1 d2: {pred T1}) (f : T1 -> T2), {in d1, bijective f} -> d1 =i d2 -> {in d2, bijective f}.
        admit.
        have mem_hash_unhash : perm_eq s (bnodes (init_hash g)) -> (get_b g) =i (forget_hashes (get_bs s)).
        admit.
        move=> /mem_hash_unhash peq.
        have bij_fget: {in (forget_hashes (get_bs s)), bijective (build_kmapping_from_seq (mapi (app_n mark_bnode) s))}.
        (* the hard one *)
        admit.

        have mem_eq_sym: forall (T: eqType) (d1 d2: {pred T}), d1 =i d2 -> d2 =i d1. by move=> T d1 d2 d12 x;  rewrite d12.
        eapply ext_pred_bij. apply bij_fget. apply mem_eq_sym.
      Admitted.

      End experiment.

    End Kmapping.

  End IsoCanAlgorithm.

  (* Section Example. *)
  (*   (* From Coq Require Import Strings.String. *) *)
  (*   Require Import Strings.Ascii. *)
  (*   Variables (b : seq ascii) (p : nat). *)
  (*   Definition B_ := (@Bnode nat (seq ascii) nat b). *)
  (*   Definition P := (@Iri nat (seq ascii) nat p). *)
  (*   Lemma inib : is_in_ib B_. *)
  (*   Proof. by []. Qed. *)

  (*   Lemma ini : is_in_i P. Proof. by []. Qed. *)
  (*   (* Check nat : countType. *) *)

  (*   Definition t := mkTriple B_ inib ini. *)
  (*   Definition g := @mkRdfGraph _ _ _ [:: t] todo. *)
  (*   Variable h:countType. *)
  (*   Variable h0 h1 h2 h3 h4: h. *)
  (*   Check g. *)
  (*   (* Open *) *)
  (*   Open Scope char_scope. *)
  (*   Check ascii. *)
  (*   Definition berror := [:: "e"; "r"; "r"; "o"; "r"] : seq ascii. *)
  (*   About Countable.pack. *)
  (*   About Countable.mixin_of. *)
  (*   Variable ascii_countMixin : Countable.mixin_of ascii. *)
  (*   Fail Canonical ascii_countType := Eval hnf in CountType ascii ascii_countMixin. *)
  (*   (* CountType ascii ascii_countMixin. *) *)

  (*   Fail Compute isoCanonicalise h0 h1 h2 h3 h4 berror g . *)

  (* End Example. *)


End IsoCan.
