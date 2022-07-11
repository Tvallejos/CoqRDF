From mathcomp Require Import all_ssreflect fingraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term.

Section IsoCan.
  Axiom todo: forall t,t.

  Variable I B L: countType.

  (*   Definition isocanonical_function (M : B -> B) (g : rdf_graph_) :=
    iso g (Rdf.relabeling M g) /\
      forall (h : rdf_graph_), iso g h <-> (relabeling M g) = (relabeling M h). *)

  Section IsoCanAlgorithm.
    Variable h : countType.
    Variables h0 hfwd hbwd hmark : h.
    (* add conditions on the input *)
    Variable hashTerm : term I B L -> h.
    Hypothesis perfectHashingSchemeTerm : injective hashTerm.
    Implicit Type trm : term I B L.

    Section Hash.

      Record hash (T : Type) := mkHinput {
                                   input : T ;
                                   current_hash : h
                                 }.

      Lemma by_perf_hash trm (o : h) (eqb : hashTerm trm == o) : hashTerm trm = o.
      Proof. apply /eqP. apply eqb. Qed.

      Section CountHash.
        Variable T : countType.
        Definition code_hash (x : hash T) : GenTree.tree nat :=
          let (i,o) := x in
          GenTree.Node 0 [:: GenTree.Leaf (pickle i); GenTree.Leaf (pickle o)].

        Definition decode_hash (x : GenTree.tree nat) : option (hash T) :=
          match x with
          | GenTree.Node 0 [:: GenTree.Leaf n; GenTree.Leaf m] =>
              match (@unpickle T n, @unpickle h m) with
              | (Some i, Some o) => Some (mkHinput i o)
              | (_, _) => None
              end
          | _ => None
          end.

        Definition cancel_hin_encode : pcancel code_hash decode_hash.
        Proof. by case => i o; rewrite /code_hash /decode_hash !pickleK. Qed.

        Definition hin_eqMixin := PcanEqMixin cancel_hin_encode.
        Definition hin_canChoiceMixin := PcanChoiceMixin cancel_hin_encode.
        Definition hin_canCountMixin := PcanCountMixin cancel_hin_encode.

        Canonical hin_eqType := Eval hnf in EqType (hash T) hin_eqMixin.
        Canonical hin_choiceType := Eval hnf in ChoiceType (hash T) hin_canChoiceMixin.
        Canonical hin_ct := Eval hnf in CountType (hash T) hin_canCountMixin.
        Definition hin_canPOrderMixin := PcanPOrderMixin (@pickleK hin_ct).
        Canonical hin_POrderType := Eval hnf in POrderType tt (hash T) hin_canPOrderMixin.

      End CountHash.
    End Hash.

    Definition hterm := term I (hash B) L.

    Definition eqb_trm_hi trm (ht : hterm) : bool :=
      match trm, ht with
      | Iri i, Iri i' => i == i'
      | Bnode b, Bnode hin => b == (input hin)
      | Lit l, Lit l' => l == l'
      | _,_ => false
      end.

    Definition htriple := triple I (hash B) L.

    Definition get_triple trm (trpl : htriple) : option hterm :=
      let (s,p,o,_,_,_) := trpl in
      if eqb_trm_hi trm s then Some s
      else if eqb_trm_hi trm p then Some p
           else if eqb_trm_hi trm o then Some o
                else None.

    Definition is_some {T : Type} (ot : option T) : bool :=
      match ot with Some _ => true | None => false end.

    Definition hgraph := rdf_graph I (hash B) L.

    Definition get t (g : hgraph) : option hterm :=
      let otrs := (map (get_triple t) (graph g)) in
      head None (filter is_some otrs).

    Definition lookup_hash (hb : hterm) : option (hash B) :=
      match hb with
      | Bnode hin => Some hin
      | _ => None
      end.

    Section Partition.

      Definition eq_hash (b1 b2 : hterm) : bool :=
        match (lookup_hash b1), (lookup_hash b2) with
        | Some hin1, Some hin2 => current_hash hin1 == current_hash hin2
        | _,_ => false
        end.

      (* change for finset *)
      Fixpoint partitionate (f : hterm -> bool) (s : seq hterm) : seq hterm * seq hterm :=
        match s with
        | nil => (nil, nil)
        | x :: tl => let (g,d) := partitionate f tl in
                   if f x then (x::g,d) else (g,x::d)
        end.

      (* should be parameterized by a hgraph
         part shoud be the finset of (hash B) that shares hash in g *)
      Definition part := seq (hash B).

      (* the finset of parts in g *)
      Definition partition := seq part.

      Fixpoint someT_to_T {T : Type} (os : seq (option T)) : seq T :=
        match os with
        | nil => nil
        | Some t :: oss => t :: someT_to_T oss
        | None :: oss => someT_to_T oss
        end.

      Definition mkPartition (g : hgraph) : partition :=
        let bnodes := (bnodes g) in
        let equiv := (fun b => (fun t=> eq_hash b t)) in
        (* undup up to permutation *)
        let P := undup (map (fun b=> (partitionate (equiv b) bnodes).1 ) bnodes) in
        let ohs := map (fun bs => map lookup_hash bs) P in
        map someT_to_T ohs.

      Definition is_trivial (p : part) : bool :=
        size p == 1.

      Definition is_non_trivial (p : part) : bool :=
        ~~ is_trivial p.

      Definition is_fine (P : partition) : bool :=
        all is_trivial P.

      Definition is_coarse (P : partition) : bool :=
        size P == 1.

      Definition is_intermediate (P : partition) :=
        ~~ is_fine P && ~~ is_coarse P.

    End Partition.

    Definition init_bnode (b : B) : (hash B) :=
      mkHinput b h0.

    Definition init_hash (g : rdf_graph _ _ _) : hgraph :=
      relabeling init_bnode g.

    Hypothesis to_string : h -> B.

    Definition label_bnode (hb : (hash B)) : B :=
      to_string (current_hash hb).

    Definition label_term (htrm : hterm) : term I B L :=
      relabeling_term label_bnode htrm.

    Definition label_triple ht : triple I B L :=
      relabeling_triple label_bnode ht.

    Definition label (g : hgraph) : rdf_graph I B L :=
      relabeling label_bnode g.

    (* assumes order and no dup in parts *)
    Definition cmp_part (p1 p2 : part) : bool :=
      all2 (fun b1 b2 => input b1 == input b2) p1 p2.

    (* assumes order and no dup in partition *)
    (* answers true if every part in the partition of g is equal to the respective part in h *)
    Definition cmp_partition (g h: hgraph) : bool :=
      let Pg := mkPartition g in
      let Ph := mkPartition h in
      all2 (fun p1 p2 => cmp_part p1 p2) Pg Ph.

    Definition update_bnodes : hgraph -> hgraph := todo _.

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
    Definition hashNodes (g : rdf_graph _ _ _) : hgraph :=
      hashNodes_initialized (init_hash g).

    Definition reachability_rel (g : hgraph) (t1 t2 : htriple) : bool :=
      let (s1, _, o1, _, _, _) := t1 in
      let (s2, _, o2, _, _, _) := t2 in
      let s1s2 := (s1 == s2) && is_bnode s1 in
      let s1o2 := (s1 == o2) && is_bnode s1 in
      let o1s2 := (o1 == s2) && is_bnode o1 in
      let o1o2 := (o1 == o2) && is_bnode o1 in
      s1s2 || s1o2 || o1s2 || o1o2.

    Definition blank_node_split (t u v : Type) (g : rdf_graph t u v) : seq (rdf_graph t u v) :=
      todo _.

    Definition ground_split {t u v : Type} (g : rdf_graph t u v) : rdf_graph t u v :=
      todo _.

    Lemma merge_split {t u v : Type} (g : @rdf_graph t u v) :
      merge_rdf_graph (merge_seq_rdf_graph (blank_node_split g)) (ground_split g) = g. Admitted.

    Definition hashBnodesPerSplit (g : hgraph) : hgraph :=
      let splitG := blank_node_split g in
      foldr (@merge_rdf_graph _ _ _) (empty_rdf_graph _ _ _) splitG.

    Definition cmp_bnode (b : B) (ht : hterm) : bool :=
      match ht with
      | Bnode hin => b == (input hin)
      | _ => false
      end.

    Definition lookup_bnode_in_triple (t : htriple) (b : B) : hterm :=
      let (s,p,o,_,_,_) := t in
      if cmp_bnode b s then s
      else if cmp_bnode b p then p
           else o.

    Definition mark_bnode (b : hash B) : hterm :=
      todo _.

    Definition replace_bnode (b : hash B) (b' : hterm) (g : hgraph) : hgraph :=
      todo _.

    (* from the Partition choose the canonical part that is not fine *)
    Definition choose_part (P : partition) : part :=
      todo _.

    (* b is_bnode *)
    Definition distinguishBnode g (color_refine : hgraph -> hgraph ) (b : (hash B)) : hgraph :=
      let b' := mark_bnode b in
      let g' := replace_bnode b b' g in
      color_refine g'.

    (* choose canonical graph from sequence of graphs that have fine partitions *)
    Definition choose_graph (gs : seq hgraph) : hgraph :=
      todo _.

    (* give partition and proof that partition is not fine *)
    (* or compute it again ... *)
    Fixpoint distinguish_ g (color : hgraph -> hgraph) (fuel:nat) : hgraph :=
      match fuel with
      | O => g
      | S n' =>
          let P := mkPartition g in
          if is_fine P then g
          else
            let p := choose_part P in
            let gs := map (distinguishBnode g color) p in
            let Ps := map mkPartition gs in
            let gP := zip gs Ps in
            let just_fine := (fun (gP : hgraph * partition) =>
                                if is_fine gP.2 then gP.1
                                else distinguish_ gP.1 color n') in
            choose_graph (map just_fine gP)
      end.

    Definition distinguish g (color_refine : hgraph -> hgraph) : hgraph :=
      distinguish_ g color_refine (size g).

    Definition isoCanonicalTemplate g (color color_refine: hgraph -> hgraph) refine : rdf_graph I B L:=
      let g' := color (init_hash g) in
      let P := mkPartition g' in
      let g_iso := if is_fine P then g' else refine g' color_refine in
      label g_iso.

    (* first approach *)
    Definition justDistinguish g :=
      isoCanonicalTemplate g id id distinguish.

    Definition isoCanonicalNoIter g :=
      isoCanonicalTemplate g update_bnodes update_bnodes distinguish.

    Definition isoCanonicalIter g :=
      isoCanonicalTemplate g hashNodes_initialized hashNodes_initialized distinguish.

    Definition isoCanonicalise g :=
      isoCanonicalTemplate g hashBnodesPerSplit hashNodes_initialized distinguish.

    Lemma singleton_g_is_fine (g: hgraph) : size g = 1 -> is_fine (mkPartition g).
      Proof. rewrite /mkPartition => singleton_g. Abort.

    Lemma distinguish_preserves_isomorphism g : iso (justDistinguish g) g.
    Proof. rewrite /iso/justDistinguish/isoCanonicalTemplate/is_iso.
           elim (graph g) => [|t ts ihts].
           - exists id. split. by exists id.
             rewrite relabeling_id.
           (* need to build μ. and μ bij.
               *)
           Abort.

    Lemma justDistinguish_isocan : isocanonical_mapping justDistinguish.
    Proof. rewrite /isocanonical_mapping=> g1; split. Abort.


    (* Definition lookup_bnode (b : B) (g : hash_graph) : option h := *)
    (*   filter (fun t => match t with *)
    (*                    | Bnode hin => b == hin *)
    (*                    | _ => false *)
    (*                    end) (graph g). *)

    (* Lemma hash_dont_get_equal (g : hash_graph) (b1 b2: B) : True. *)


    (* { hash_term | is_true is_bnode }) : forall n, n+1. *)

    (* () *)
    (*     forall (g : rdf_graph) (hms : seq hashmap) *)
    (*            (ghashh : hashNodes g = hms) *)
    (*            (i j : nat) (ileqj : i <= j) (lim : j < size hms) *)
    (*            (x y : term) (bnx : is_bnode x) (bny : is_bnode y) *)
    (*            (xing : x \in (terms g)) (ying : y \in (terms g)), *)
    (*       (lookup_hashmap (nth [::] hms i) x != lookup_hashmap (nth [::] hms i) y) *)
    (*       -> lookup_hashmap (nth [::] hms j) x != lookup_hashmap (nth [::] hms j) y. *)

    (*
    Hypothesis hashNodes_preserves_isomorphism :
      forall (g h: rdf_graph) (isogh : iso g h)
             (hash_g hash_h: hashmap)
             (hashg_hm : hash_g = last [::] (hashNodes g))
             (hashh_hm : hash_h = last [::] (hashNodes h))
             (b : term) (bing : b \in (bnodes (g)))
             (c : term) (cinh : c \in (bnodes (h))),
      exists μ, (relabeling_term μ b) = c -> lookup_hashmap hash_g b = lookup_hashmap hash_h c. *)

    (* Hypothesis perfectHashingSchemeTriple : injective hashTriple. *)

    Variable hashBag : (seq (hash B) -> (hash B)).
    Hypothesis hashBag_assoc : forall (l1 l2 l3: seq (hash B)),
        hashBag ([:: hashBag (l1 ++ l2)] ++ l3) = hashBag (l1 ++ [:: hashBag (l2 ++ l3)]).
    Hypothesis hashBag_comm : forall (l1 l2: seq (hash B)),
        hashBag (l1 ++ l2) = hashBag (l2 ++ l1).

  End IsoCanAlgorithm.
  (* Hypothesis rdf_total_order   *)

End IsoCan.

