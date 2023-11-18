From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term Util IsoCan.

    Section Blabel.
    Variable I B L: countType.
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

      Variable hashBag : seq h -> h.
      Hypothesis hashBag_assoc : forall (l1 l2 l3: seq h),
          hashBag ([:: hashBag (l1 ++ l2)] ++ l3) = hashBag (l1 ++ [:: hashBag (l2 ++ l3)]).
      Hypothesis hashBag_comm : forall (l1 l2: seq h),
          hashBag (l1 ++ l2) = hashBag (l2 ++ l1).

      Lemma hasTuple_neq_errorP s: hashTuple s = herror -> False.
      Proof. by apply /eqP; rewrite /negb hashTuple_neq_error. Qed.

      Definition hterm := hterm I B L h.
      Local Notation hash := (hash h).

      Lemma by_perf_hash trm (o : h) (eqb : hashTerm trm == o) : hashTerm trm = o.
    Proof. by apply/eqP; apply eqb. Qed.

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

    Hypothesis to_string : h -> B.
    Hypothesis to_string_inj : injective to_string.

    Definition label_bnode (hb : (hash B)) : B :=
      to_string (current_hash hb).

    Definition lookup_hash_default (hb : hterm) : h :=
      lookup_hash_default_ herror hb.

    Definition label_term (htrm : hterm) : term I B L :=
        relabeling_term label_bnode htrm.

      Definition term_hash (trm : hterm) : h :=
        match trm with
        | Iri x | Lit x => hashTerm (term_of_hterm trm)
        | Bnode hb => current_hash hb
        end.

      Definition mark_bnode (b : hterm) : hterm :=
        match b with
        | Iri i| Lit i => Bnode (mkHinput b0 herror)
        | Bnode hb=> Bnode (mark_hash hb)
        end.

      Lemma mark_bnode_inj g: {in (bnodes g), injective mark_bnode}.
      Proof. move=> x in_bns y.
             case: x in_bns; case y=> x' y'; rewrite ?i_in_bnodes ?l_in_bnodes // => in_bns /=
                 => [[]] i_eq /eqP; rewrite ?hashTuple_neq_error //
                 => /eqP/hashTuple_inj []=> ch_eq.
             by f_equal; apply /eqP; rewrite eq_i_ch i_eq ch_eq !eqxx.
      Qed.

      Lemma lookup_hash_relabeling ht mu: (lookup_hash_default ht) = (lookup_hash_default (relabeling_hterm mu ht)).
      Proof. by case ht. Qed.


      Definition label_triple ht : triple I B L :=
        relabeling_triple label_bnode ht.

      Definition init_hash_ts := @init_hash_ts I B L h h0.

      Lemma mark_bnode_init_hash_ts_mark_hash ts b n:
        Bnode b \in bnodes_ts (init_hash_ts ts) ->
                    app_n mark_bnode (Bnode b) n =
                      Bnode (app_n mark_hash (mkHinput (input b) h0) n).
      Proof. move=> /init_hash_ts_h0 b_hash.
             elim n=> /=[| n' IHn]; last by rewrite IHn.
             by congr Bnode; case: b b_hash=> /= [[]] ? ? /= ->.
      Qed.

      Definition init_hash := @init_hash I B L h h0.

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

      Definition hgraph := @hgraph I B L h.

      Definition label_ts (ts : hgraph) : seq (triple I B L) :=
        relabeling_seq_triple label_bnode ts.

      Definition label (g : hgraph) us : rdf_graph I B L :=
        @relabeling _ _ _ _ label_bnode g us.

      Definition lookup_bnode_in_graph_default (g : hgraph) (b : B) : h :=
        if lookup_bnode_in_graph g b is Some trm then term_hash trm else herror.


      (* assumes order and no dup in partition *)
      (* answers true if every part in the partition of g is equal to the respective part in h *)
      Definition hts := @hts I B L h.

      Definition cmp_partition_ts (g h: hts) : bool :=
        let Pg := mkPartition_ts g in
        let Ph := mkPartition_ts h in
        all2 (fun p1 p2 => cmp_part p1 p2) Pg Ph.

      Definition cmp_partition (g h: hgraph) : bool :=
        cmp_partition_ts (graph g) (graph h).

      Section Partition.

      Fixpoint partitionate (f : hterm -> bool) (s : seq hterm) : seq hterm * seq hterm :=
        match s with
        | nil => (nil, nil)
        | x :: tl => let (g,d) := partitionate f tl in
                   if f x then (x::g,d) else (g,x::d)
        end.

      Definition partitionate' (f : hterm -> bool) (s : seq hterm) : seq hterm * seq hterm :=
        (filter f s, filter (negb \o f) s).

      Definition part := seq (hash B).

      Definition partition := seq part.

      Definition lookup_hash := @lookup_hash I B L h.

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

    End Partition.

      (* algorithm 3, lines 9-10
       chooses the canonical part which is not trivial *)
      Fixpoint choose_part (P : partition) : part :=
        match P with
        | nil => nil
        | cons p t => if is_trivial p then choose_part t else p
        end.

      (* choose canonical graph from sequence of graphs that have fine partitions *)
      Definition choose_graph (gs : seq hgraph) : hgraph :=
        if insub gs : {? x | all (is_fine \o mkPartition) x} is Some _
        then foldl Order.max empty_rdf_graph gs
        else empty_rdf_graph.

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

        Definition htriple := @htriple I B L h.

        Axiom todo: forall {T : Type}, T.

        Definition replace_bnode := @replace_bnode I B L h.

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
                           then let gacc' := (@replace_bnode hb hb' gacc todo) in
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

        (* requires the lemma stating hashNodes terminates without getting out of fuel *)
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

        Definition isoCanonicalNoIter g :=
          isoCanonicalTemplate g update_bnodes update_bnodes distinguish.

        Definition isoCanonicalIter g :=
          isoCanonicalTemplate g hashNodes_initialized hashNodes_initialized distinguish.

        (* Definition blabel g := *)
        (*   isoCanonicalTemplate g hashBnodesPerSplit hashNodes_initialized distinguish. *)

      End Isocanonicalise.
    End Blabel.
