From mathcomp Require Import all_ssreflect fingraph.
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

    Local Notation hash := (hash h).

    Lemma by_perf_hash trm (o : h) (eqb : hashTerm trm == o) : hashTerm trm = o.
    Proof. by apply/eqP; apply eqb. Qed.

    Definition init_bnode (b : B) : (hash B) :=
      mkHinput b h0.

    Lemma init_bnode_inj : injective init_bnode.
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

      Definition eqb_b_hterm b (ht : hterm) : bool :=
        if ht is Bnode hb then b == (input hb) else false.

      Lemma eqb_b_hterm_is_bnode b (ht : hterm) : eqb_b_hterm b ht -> is_bnode ht.
      Proof. by case ht. Qed.

      Lemma eqb_b_hterm_trans b b' ht : eqb_b_hterm b ht -> eqb_b_hterm b' ht -> b = b'.
      Proof. by case: ht=> // ? /eqP-> /eqP->. Qed.

      Definition lookup_hash (hb : hterm) : option (hash B) :=
        if hb is Bnode hin then some hin else None.

      Definition lookup_hash_default (hb : hterm) : h :=
        if hb is Bnode hin then current_hash hin else herror.

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

      Lemma lookup_hash_relabeling ht mu: (lookup_hash_default ht) = (lookup_hash_default (relabeling_hterm mu ht)).
      Proof. by case ht. Qed.

      Lemma eqb_b_hterm_relabel f b ht (injF: injective f): (eqb_b_hterm b ht) = (eqb_b_hterm (f b) (relabeling_hterm f ht)).
      Proof. by case ht=> //= name; rewrite inj_eq. Qed.

      Lemma has_map s f b (injF: injective f): has (eqb_b_hterm b) s = has (eqb_b_hterm (f b)) (map (relabeling_hterm f) s).
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
        head None (filter is_some otrs).

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
        head None (filter is_some otrms).

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

      Definition build_kmapping_from_seq (trms : seq hterm) : B -> B :=
        fun b =>
          if has (eqb_b_hterm b) trms then
            let the_bnode := nth (Bnode (mkHinput b herror)) trms (find (eqb_b_hterm b) trms) in
            to_string (lookup_hash_default the_bnode)
          else
            b.

      Definition k_mapping_ts (ts : seq (triple I B L)) : seq (triple I B L) :=
        let all_maps :=
          map (mapi (app_n mark_bnode)) (permutations (bnodes_ts (init_hash_ts ts))) in
        let mus := map build_kmapping_from_seq all_maps in
        let isocans := map (fun mu => (relabeling_seq_triple mu ts)) mus in
        foldl Order.max [::] isocans.

      Lemma k_mapping_seq_uniq_ts ts: uniq (mapi (app_n mark_bnode) (bnodes_ts (init_hash_ts ts))).
      Proof.
        rewrite /mapi; pose ts' := init_hash_ts ts.
        rewrite map_inj_in_uniq; first by apply (zip_uniq_l _ (uniq_bnodes_ts ts')).
        move=> [t n] [u m] /in_zip/andP [tin_bns n_iota] /in_zip/andP [uin_bns m_iota] /= eq_app_n.
        case: t tin_bns uin_bns eq_app_n; case: u
            => nt nu; rewrite ?i_in_bnodes_ts ?l_in_bnodes_ts // => nu_bns nt_bns injH.
        by apply /eqP; rewrite xpair_eqE; apply (can_app_n_mb_init_ts nu_bns nt_bns injH).
      Qed.

      Lemma k_mapping_seq_uniq_graph g: uniq (mapi (app_n mark_bnode) (bnodes (init_hash g))).
      Proof. by apply k_mapping_seq_uniq_ts. Qed.

      Lemma all_bnodes_perm {i b l: eqType} (ts : seq (triple i b l)) s:
        perm_eq (bnodes_ts ts) s -> forall x, x \in s -> is_bnode x.
      Proof. by move=> peq x xin; apply (in_all xin); rewrite -(perm_all _ peq) all_bnodes_ts. Qed.

      Lemma k_mapping_seq_uniq_perm_eq_ts ts s: perm_eq s (bnodes_ts (init_hash_ts ts)) -> uniq (mapi (app_n mark_bnode) s).
      Proof. rewrite /mapi perm_sym=> perm_eq. rewrite map_inj_in_uniq. apply uniq_zip_iota.
             move=> [x1 n] [y1 m] /in_zip/andP [x1_ins n_iniota] /in_zip/andP [y1_ins m_iniota] /=.
             have := all_bnodes_perm perm_eq x1_ins.
             have := all_bnodes_perm perm_eq y1_ins.
             case :y1 x1_ins y1_ins; case x1=> // namey namex; rewrite -!(perm_mem perm_eq)=> y_ins x_ins _ _.
             by move=> ?; apply /eqP; rewrite xpair_eqE; apply (can_app_n_mb_init_ts y_ins).
      Qed.

      Lemma k_mapping_seq_uniq_perm_eq g s: perm_eq s (bnodes (init_hash g)) -> uniq (mapi (app_n mark_bnode) s).
      Proof. by apply k_mapping_seq_uniq_perm_eq_ts. Qed.

      (* to prove *)
      Lemma uniq_k_mapping_res ts: uniq (k_mapping_ts ts).
      Proof. rewrite /k_mapping_ts.
             case: (foldl_max  [seq relabeling_seq_triple mu ts
                               | mu <- [seq build_kmapping_from_seq i
                                      | i <- [seq mapi (app_n mark_bnode) i | i <- permutations (bnodes_ts (init_hash_ts ts))]]] [::]).
             by move=> ->.
             pose s:= foldl Order.max [::]
                        [seq relabeling_seq_triple mu ts
                        | mu <- [seq build_kmapping_from_seq i
                               | i <- [seq mapi (app_n mark_bnode) i | i <- permutations (bnodes_ts (init_hash_ts ts))]]].
             rewrite -/s.
             Abort.


      Definition k_mapping (g : rdf_graph I B L) : rdf_graph I B L :=
        @mkRdfGraph I B L (k_mapping_ts (graph g)) todo.

      Lemma injection_kmap b b' ht s (eb: eqb_b_hterm b ht) (eb': eqb_b_hterm b' ht):
        (build_kmapping_from_seq (mapi (app_n mark_bnode) s) b) =
          (build_kmapping_from_seq (mapi (app_n mark_bnode) s) b').
      Proof. by rewrite (eqb_b_hterm_trans eb eb'). Qed.

      Lemma map_kmap b n s :
        (build_kmapping_from_seq s b) = n ->
        (has (eqb_b_hterm b) s) ->
        forall s' (f : B -> B), injective f -> s' = map (relabeling_hterm f) s ->
                                (build_kmapping_from_seq s' (f b)) = n.
      Proof.
        elim: s=> [| hd tl IHtl]; first by rewrite has_nil.
        move=> beq has_b s'; case: s'=> [//| hd' tl'] f injF [eqhd eqtl].
        move: IHtl; rewrite /build_kmapping_from_seq eqhd eqtl -map_cons -has_map; last by apply injF.
        rewrite has_b /= -eqb_b_hterm_relabel; last by apply injF. rewrite /= in has_b.
        case/orP: has_b beq; first by rewrite /build_kmapping_from_seq=> H /=; rewrite H; case hd=> // name /=.
        + rewrite /build_kmapping_from_seq /= ; case e: (eqb_b_hterm b hd)
                  => /=; first by move=> _; rewrite -lookup_hash_relabeling.
          move=> /= has_tl /=; rewrite has_tl=> eq IHtl.
          have IHtl' := IHtl eq isT tl' f injF eqtl.
          by rewrite eqtl -has_map ?has_tl in IHtl'; last by apply injF.
      Qed.

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

      Lemma k_mapping_iso_output : mapping_is_iso_mapping k_mapping.
      Proof. rewrite /mapping_is_iso_mapping/iso/is_iso=> g.
             exists todo.
             suffices eqb: eqb_rdf (relabeling todo) g.
             apply /and3P; split; last by apply eqb.
             admit.
      Admitted.

      Lemma k_mapping_dont_manipulate_names : (dt_names_mapping k_mapping).
      Proof.
      Admitted.

      Lemma k_mapping_isocan : isocanonical_mapping k_mapping.
      Proof. apply: isocanonical_mapping_dt_out_mapping k_mapping_iso_output k_mapping_dont_manipulate_names. Qed.

      Lemma k_mapping_iso g : iso (k_mapping g) g.
      Proof. rewrite /iso/is_iso. Admitted.

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
