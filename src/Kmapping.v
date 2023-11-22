From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term Util IsoCan.
Import Order.Theory.
Open Scope order_scope.

(******************************************************************************)
(*                                                                            *)
(*            κ-mapping algorithm rewritten in a functional style             *)
(*                                                                            *)
(******************************************************************************)

Section Kmapping.
  Variable disp : unit.
  Variable I B L : orderType disp.
  Hypothesis nat_inj : nat -> B.
  Hypothesis nat_inj_ : injective nat_inj.

  Notation hn := (hash Order.NatOrder.orderType B).
  Notation hterm := (term I hn L).
  Definition HBnode p := @Bnode I hn L (mkHinput p.1 p.2).

  Notation le_triple := (@Rdf.le_triple disp _ I L B).
  Notation join_st := (@Rdf.join_st disp _ I L B).
  Notation le_triple_total := (@Triple.le_total disp disp I L B).
  Notation le_triple_anti := (@Triple.le_triple_anti disp disp I L B).
  Notation le_triple_trans := (@Triple.le_triple_trans disp disp I L B).

  Definition n0 := 0%N.

  Definition init_bnode_nat (b : B) : (hash nat B) := mkHinput b n0.

  Lemma init_bnode_nat_inj : injective init_bnode_nat.
  Proof. by move=> x y []. Qed.

  Definition build_kmapping_from_seq (trms : seq hterm) : B -> B :=
    fun b =>
      if has (eqb_b_hterm b) trms then
        let the_bnode := nth (HBnode (b,n0)) trms (find (eqb_b_hterm b) trms) in
        nat_inj (lookup_hash_default_ n0 the_bnode)
      else
        b.

  Definition hash_kp p := [seq HBnode an | an <- zip p (iota 0 (size p))].
  Definition build_map_k p := build_kmapping_from_seq (hash_kp p).

  Definition k_mapping_ts (ts : seq (triple I B L)) : seq (triple I B L) :=
    let perms :=  permutations (get_bts ts) in
    let all_maps := map
                      (map HBnode)
                      (map (fun s=> zip s (iota 0 (size s))) perms)
    in
    let mus := map build_kmapping_from_seq all_maps in
    let isocansK := map (fun mu => (relabeling_seq_triple mu ts)) mus in
    let isocans := map (sort le_triple) isocansK in
    (* \big[join_st/[::]]_(i <- isocans) i. *)
    (* \big[ Order.max /[::]]_(i <- isocans) i. *)
    foldl join_st [::] isocans.

(******************************************************************************)
(*                  κ-mapping returns a well formed graph                     *)
(******************************************************************************)

  (* For every hashed permutation u,
     if a blank node b is in the blank nodes of ts,
     then u has a blank node whose initial value was b *)
  Lemma get_bts_in_l_perm (ts : seq (triple I B L)) (u : seq hterm)
    (mem : u \in [seq [seq HBnode an | an <- i]
                 | i <- [seq zip s (iota 0 (size s)) | s <- permutations (get_bts ts)]]):
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

  (* For every duplicate-free sequence of triples ts,
     a hashed permutation u,
     a blank node b which is in the blank nodes of ts,
     it exists a natural number n such that
        the element at index (find (eqb_b_hterm b) u) in u is an HBnode (b, n) *)
  Lemma nth_bperms (ts : seq (triple I B L))
    (uniq_ts : uniq ts) (b : B) db dn
    (bin : b \in get_bts ts) (u : seq hterm)
    (mem : u \in  [seq [seq HBnode an | an <- i]
                  | i <- [seq zip s (iota 0 (size s)) | s <- permutations (get_bts ts)]]) :
    exists n : nat, nth (HBnode (db ,dn)) u (find (eqb_b_hterm b) u) = HBnode (b, n).
  Proof.
  move/mapP : mem=> [/= bns /mapP[/= bs]].
  rewrite mem_permutations=> peq_bs bnseq ueq; rewrite ueq bnseq.
  have permbs := perm_mem peq_bs.
  have uniqbs := perm_uniq peq_bs.
  suffices H1 :
    (find (eqb_b_hterm b) [seq Bnode (mkHinput an.1 an.2) | an <- zip bs (iota 0 (size bs))]) =
      (index b bs).
    suffices H2 : forall [S0 T0 : eqType] (x : S0) (y : T0) [s : seq S0] [t : seq T0] (i : nat),
        size s = size t -> nth (Bnode (mkHinput x y)) [seq Bnode (mkHinput an.1 an.2) | an <- zip s t ] i = Bnode (mkHinput (nth x s i) (nth y t i)).
      exists (index b bs).
      rewrite H2; last by rewrite size_iota.
      congr Bnode.
      rewrite H1 //; apply/eqP; rewrite eq_i_ch /=; apply /andP; split; apply/eqP.
      + by rewrite nth_index // permbs.
      + by rewrite nth_iota // index_mem permbs //.
    by apply hash_nth_mapzip.
  by move=> ? ?; apply: find_index_eqbb; rewrite size_iota.
  Qed.

  (* For every sequence of triples: ts and a hashed permutation of ts: u,
     for two hterms ht1 and ht2 which are members of u then
     if lookup_default_ n0 ht1 = lookup_default_ n0 ht2 it implies
     ht1 = ht2. *)
  Lemma in_perm_luh_inj (ts : seq (triple I B L))
    (u : seq hterm) :
    u \in [seq [seq HBnode an | an <- i]
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

  (* For every duplicate-free sequence of triples: ts and a hashed permutation of ts: u,
     for two blank nodes b1 and b2 which are members of the blank nodes of ts then
     if (build_kmapping_from_seq u) b1 = (build_kmapping_from_seq u) b2 it implies
     b1 = b2. *)
  Lemma labeled_perm_inj
    (ts : seq (triple I B L)) (uniq_ts : uniq ts)
    u (mem : u \in [seq [seq HBnode an | an <- i]
                   | i <- [seq zip s (iota 0 (size s))
                         | s <- permutations (get_bts ts)]]) :
    {in get_bts ts &, injective (build_kmapping_from_seq u)}.
  Proof.
  move=> x y xin yin; rewrite /build_kmapping_from_seq.
  suffices mem_has: forall b, b \in get_bts ts -> has (eqb_b_hterm b) u.
    rewrite !mem_has // => /nat_inj_.
    set dflt := HBnode (y,n0).
    have ->: (nth (HBnode (x,n0)) u (find (eqb_b_hterm x) u)) = (nth dflt u (find (eqb_b_hterm x) u)) by rewrite (set_nth_default (HBnode (x,n0))) // -has_find mem_has.
    move: (nth_bperms uniq_ts y n0 xin mem) (nth_bperms uniq_ts y n0 yin mem)=> [n eqnnthx] [m eqmnthy].
    rewrite eqnnthx eqmnthy.
    suffices J: {in u&, injective (lookup_hash_default_ n0)}.
      move=> /J; rewrite -eqnnthx -eqmnthy.
      move : (mem_has x xin) (mem_has y yin); rewrite !has_find=> nthxin nthyin.
      by rewrite !mem_nth // => /(_ isT isT); rewrite eqnnthx eqmnthy; move=> [->].
    by apply (in_perm_luh_inj mem).
  by apply get_bts_in_l_perm.
  Qed.

  (* For every duplicate-free sequence of triples: ts and a permutation of ts blank nodes: perm,
     if (build_map_k perm) is injective in the domain of blank nodes of ts,
     then (build_map_k perm) is a pre-isomorphism from ts to relabeling ts under (build_map_k perm) *)
  Lemma auto_iso_rel_perm (ts : seq (triple I B L))
    (uts : uniq ts) (perm : seq B)
    (inperm : perm \in permutations (get_bts ts))
    (mu_inj : {in get_bts ts&, injective (build_map_k perm)}):
    is_pre_iso_ts ts (relabeling_seq_triple (build_map_k perm) ts) (build_map_k perm).
  Proof.
  apply uniq_perm.
  + by rewrite map_inj_in_uniq // uniq_get_bts.
  + by rewrite uniq_get_bts.
  + suffices rt_inj: {in ts &, injective (relabeling_triple (build_map_k perm))}.
    by rewrite -(get_bs_map _ (all_bnodes_ts _)); apply eq_mem_pmap=> b; rewrite bnodes_ts_relabel_mem.
  by apply: inj_get_bts_inj_ts mu_inj.
  Qed.

  (* For every sequence of triples: ts and a permutation of ts blank nodes: perm,
     the zip of perm and the n first natural numbers is
     in the sequence of hashed permutation candidates of ts *)
  Lemma candidate_in_perm (ts : seq (triple I B L)) perm
    (bin : perm \in permutations (get_bts ts)) :
    [seq (HBnode an) | an <- zip perm (iota 0 (size perm))]
      \in [seq [seq HBnode an | an <- i]
          | i <- [seq zip s (iota 0 (size s)) | s <- permutations (get_bts ts)]].
  Proof.
    by apply/mapP; exists (zip perm (iota 0 (size perm)))=> //; apply /mapP; exists perm=> //.
  Qed.

  (* For every duplicate-free sequence of triples: ts,
     for every possible hashed permutation candidate: u,
     (build_k_mapping_from_seq u) is a pre-isomorphism
     from ts to relabeling ts under (build_kmapping_from_seq u) *)
  Lemma all_kmap_preiso (ts : seq (triple I B L)) (uniq_ts : uniq ts):
    forall u, u \in [seq [seq HBnode an | an <- i]
               | i <- [seq zip s (iota 0 (size s)) | s <- permutations (get_bts ts)]] ->
               is_pre_iso_ts ts
                 (relabeling_seq_triple (build_kmapping_from_seq u) ts)
                 (build_kmapping_from_seq u).
  Proof.
    move=> u /mapP /= [x /mapP[/= perm bin ->]] ->.
    suffices mu_inj : {in get_bts ts&, injective (build_map_k perm)}.
      by apply auto_iso_rel_perm.
    by apply (labeled_perm_inj uniq_ts (candidate_in_perm bin)).
  Qed.

  (* Folding the join of sequences of triples results either in the default value or
     an element of the folded sequence *)
  Lemma foldl_max_st (l : seq (seq (triple I B L))) (x0 : (seq (triple I B L))):
    foldl join_st x0 l = x0 \/ foldl join_st x0 l \in l.
  Proof. elim: l x0 => [//| t ts IHts] x0; first by left.
       + rewrite in_cons /=; case: (IHts (join_st x0 t))=> [ -> |intail] /=.
       - rewrite join_st_def. case: ifP=> _; first by right; rewrite eqxx.
         * by left.
       - by right; rewrite intail orbT.
  Qed.

  Definition join_stA : associative join_st.
  Proof. move=> x y z. rewrite /join_st !lt_st_def.
         repeat (let le := fresh "le" in case : ifP);
         subst=> //; rewrite ?eqxx;
         repeat (case : ifP=> // /eqP ?)=> //.
         by move=> _ ->.
         by move=> _ ->.
         by move=> _ contra H; rewrite H in contra.
  Admitted.

  Definition join_st_nil_idl : left_id [::] join_st. Proof. by move=> []. Qed.
  Definition join_st_nil_idr : right_id [::] join_st. Proof. by move=> []. Qed. 
  Canonical join_ts_monoid := Monoid.Law join_stA join_st_nil_idl join_st_nil_idr. 
  Definition join_st_comm : commutative join_st.
  Proof. move=> x y. rewrite /join_st !lt_st_def.
         case: ifP; case: ifP=> //.
         + move=> /andP[neqxy leyx] /andP[neqyx lexy].
           by apply /eqP/le_st_antisym/andP;split.
         + rewrite Bool.andb_false_iff=> [[|leyx]].
           by rewrite /negb; case: ifP=> // /eqP ->.
           rewrite Bool.andb_false_iff=> [[|lexy]]; first by rewrite /negb; case: ifP=> // /eqP ->.
           * by move: (le_st_total x y); rewrite lexy leyx.
  Qed.

  Canonical join_ts_monoid_com := Monoid.ComLaw join_st_comm.
  Definition join_st_idem : idempotent join_st.
  Proof. by move=> ?; rewrite /join_st lt_st_def eqxx //. Qed.

  Lemma uniq_k_mapping_ts (ts : seq (triple I B L)) (u1 : uniq ts) : uniq (k_mapping_ts ts).
  Proof.
    rewrite /k_mapping_ts.
    set perm_bs := permutations _.
    set tg_labels_perm := [seq zip s (iota 0 (size s)) | s <- perm_bs].
    set label_perm := [seq [seq HBnode an | an <- i] | i <- tg_labels_perm].
    set build_kmap := [seq build_kmapping_from_seq i | i <- label_perm].
    set relab := [seq relabeling_seq_triple mu ts | mu <- build_kmap].
      case: (foldl_max_st (map (sort le_triple) relab) [::])=> [-> //|].
    move=> /mapP[u mem ->].
    suffices relab_uniq : all uniq relab.
      by rewrite sort_uniq; apply (allP relab_uniq)=> //.
    rewrite /relab/build_kmap -map_comp.
    apply/allP=> /= t /mapP[/= s sin ->]; apply uniq_relabeling_pre_iso=> //.
    by apply all_kmap_preiso.
  Qed.

  (* For any RDF graph: ts, its image under k_mapping_ts remains well-formed *)
  Lemma uniq_k_mapping (g : rdf_graph I B L) : uniq (k_mapping_ts g).
  Proof. by apply : uniq_k_mapping_ts (ugraph _). Qed.

  Definition k_mapping (g : rdf_graph I B L) : rdf_graph I B L :=
    @mkRdfGraph I B L (k_mapping_ts (graph g)) (uniq_k_mapping g).

  Section Kmapping_isocan.

(******************************************************************************)
(*            κ-mapping returns graphs isomorphic to the input                *)
(******************************************************************************)

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
  Proof. move=> minimum.
       elim: l=> [//| hd t IHt].
       rewrite /= join_st_def minimum.
       case: (foldl_max_st t hd).
       by move=> -> ->; rewrite in_cons eqxx.
       by move=> H <-; rewrite in_cons H orbT.
  Qed.

    (* Given a sequence of sequence of triples: l,
       if there is a sequence of triples: x for which
       x is less than every other sequence of triples in l,
       then if folding join in l results in x, either l is the empty sequence or x is in l *)
  Lemma max_foldl_minimum_in_st (l : seq (seq (triple I B L))) (x : seq (triple I B L)) :
    (forall y : (seq (triple I B L)) , y \in l -> lt_st x y) -> foldl join_st x l = x -> (l == [::]) || (x \in l).
  Proof.
       elim: l=> [//| hd t IHt] minimum.
       rewrite /= join_st_def minimum; last by rewrite in_cons eqxx.
       case: (foldl_max_st t hd).
       by move=> -> ->; rewrite in_cons eqxx.
       by move=> H <-; rewrite in_cons H orbT.
  Qed.

    (* For any sequence of triples: ts,
       if the image of ts under k_mapping_ts is the empty sequence,
       then ts is also the empty sequence. *)
    Lemma k_mapping_nil_is_nil ts: k_mapping_ts ts = [::] -> ts = [::].
    Proof.
      case: ts=> // t ts'.
      move=> /max_foldl_minimum_in_st /orP[]//.
      move=> y yin.
      suffices neqs : size y != 0.
        have := join_nil_size neqs.
        by rewrite /join_st; case: ifP.
      by move/mapP : yin=> [/= t']; rewrite -!map_comp=> /mapP[/= p pin ->] ->; rewrite size_sort.
      + rewrite -map_comp /= !map_nil_is_nil => /eqP.
        by apply contra_eq; rewrite permutations_neq_nil.
      + rewrite -map_comp=> /mapP[/=xs /mapP[/= a ain]] -> => /eqP.
        by rewrite eq_sym=> /eqP/(sort_nil le_triple_total le_triple_trans le_triple_anti).
    Qed.

    (* For any pair of duplicate-free sequence of triples: ts1 and ts2,
       and an isomorphism mu from ts1 to ts2,
       then for any sequence of triple: ts3
       which is equal to ts2 modulo permutation,
       then mu is also an isomorphism from ts1 to ts3. *)
    Lemma ts_pre_iso_iso_mem [ts1 ts2: seq (triple I B L)] [mu : B -> B]:
      uniq ts1 -> uniq ts2 ->
      is_iso_ts ts1 ts2 mu -> forall (ts3 : (seq (triple I B L))), (perm_eq ts3 ts2) -> is_iso_ts ts1 ts3 mu.
    Proof. move=> u1 u2 /and3P[piso urel peq] ts3 p13.
           apply/and3P; split=> //.
           + rewrite/is_pre_iso_ts.
             apply uniq_perm.
             * rewrite map_inj_in_uniq; first by rewrite uniq_get_bts.
               by apply (is_pre_iso_ts_inj piso).
             * by rewrite uniq_get_bts.
             * move=> b; rewrite (perm_mem piso) /get_bts/get_bs.
             apply eq_mem_pmap=> bb; rewrite /bnodes_ts !mem_undup.
             rewrite !mem_filter; congr (andb (is_bnode bb)).
             rewrite /terms_ts !mem_undup; apply/flatten_mapP/flatten_mapP.
             by move=> [/= t tin bbin]; by exists t=> //; rewrite (perm_mem p13) tin.
             by move=> [/= t tin bbin]; by exists t=> //; rewrite -(perm_mem p13) tin.
            + rewrite perm_sym in p13.
              by apply (perm_trans peq p13).
    Qed.

    Lemma kmapping_iso_out_ts ts (uts : uniq ts) : iso_ts ts (k_mapping_ts ts).
    Proof.
      rewrite /iso_ts/is_iso_ts.
      have := uniq_k_mapping_ts uts.
      (* case : g=> ts uts /=; *)
                  rewrite /k_mapping_ts.
      set isocans := (map (fun mu=> relabeling_seq_triple mu ts) _).
      case : (foldl_max_st (map (sort le_triple) isocans) [::]); rewrite /isocans{isocans}/=; first by move=> /k_mapping_nil_is_nil -> _; exists id.
      rewrite -map_comp -map_comp => /mapP/=[s sin ->]; rewrite sort_uniq=> ukres.
      exists (build_kmapping_from_seq s).
      suffices /(ts_pre_iso_iso ukres) preiso : is_pre_iso_ts ts (relabeling_seq_triple (build_kmapping_from_seq s) ts) (build_kmapping_from_seq s).
      apply (ts_pre_iso_iso_mem uts ukres preiso).
      apply uniq_perm=> //.
       + by rewrite sort_uniq.
       + by move=> ?; rewrite mem_sort.
      by apply all_kmap_preiso.
    Qed.

    (* For any RDF graph g, k_mapping returns a graph which is isomorphic to g *)
    Lemma kmapping_iso_out g: iso g (k_mapping g).
    Proof. by apply: kmapping_iso_out_ts (ugraph _). Qed.

(******************************************************************************)
(*              Proofs to derive κ-mapping is a graph invariant               *)
(******************************************************************************)

    (* For any two sequences of triples ts1 and ts2 which are isomorphic,
       either both are the empty sequence, or both are different from the empty sequence *)
    Lemma iso_structure (ts1 ts2: seq (triple I B L)) :
      iso_ts ts1 ts2 -> ((ts1 == [::]) && (ts2 == [::]) || (ts1 != [::]) && (ts2 != [::])).
    Proof.
      rewrite /iso_ts/is_iso_ts /=; move=> [? /and3P [_ _]] ; case: ts1=> [|h1 tl1].
      + by rewrite relabeling_seq_triple_nil perm_sym=> /perm_nilP ->.
      + by apply contraTneq=> -> ; apply /perm_nilP.
    Qed.

    (* Relabeling a sequence of triples under the build_kmapping_from_seq of the empty sequence
       does not change the sequence of triples *)
    Lemma build_from_nil (ts : seq (triple I B L)) :
      relabeling_seq_triple (build_kmapping_from_seq [::]) ts = ts.
    Proof. by elim: ts=> [//| a l IHl]; by rewrite /= relabeling_triple_id IHl. Qed.

    (* For every blank node: b, which is member of a sequence of blank nodes s,
       the hashed permutation of s has an element whose initial blank node value is b *)
    Lemma eqb_b_hterm_memP (b : B) (s : seq B) :
      b \in s ->
            has (eqb_b_hterm (I:=I) (L:=L) b) [seq Bnode (mkHinput an.1 an.2) | an <- zip s (iota 0 (size s))].
    Proof.
      move=> b1in ; apply/ (has_nthP (Bnode (mkHinput b 0))).
      exists (index b s).
      by rewrite size_map size_zip size_iota minn_refl index_mem.
      by rewrite nth_mapzip /= ?size_iota // nth_index // eqxx.
    Qed.

    (* For every blank node: b, which is member of a duplicate-free sequence of blank nodes s,
       build_map_k of s applid to b is exactly:
       nat_inj (nth 0 (iota 0 (size s)) (index b s). *)
    Lemma out_of_build b s :
      b \in s -> uniq s ->
            (build_map_k s) b = nat_inj (nth 0 (iota 0 (size s)) (index b s)).
    Proof.
      move=> bin ubs.
      rewrite /build_map_k/build_kmapping_from_seq (eqb_b_hterm_memP bin); congr nat_inj.
      by rewrite find_index_eqbb ?size_iota // nth_mapzip ?size_iota //.
    Qed.

    Lemma iso_isokmap_ts ts1 ts2 (igh: iso_ts ts1 ts2) (u1 : uniq ts1) (u2 : uniq ts2) : iso_ts (k_mapping_ts ts1) (k_mapping_ts ts2).
    Proof. apply: iso_can_trans_ts _ igh=> //.
           + by apply uniq_k_mapping_ts.
           + by apply kmapping_iso_out_ts.
    Qed.

    (* For any two RDF graphs g and h which are isomorphic,
       the image of g and h under k_mapping is isomorphic *)
    Lemma iso_isokmap g h (igh: iso g h) : iso (k_mapping g) (k_mapping h).
    Proof. by apply: iso_can_trans _ igh; rewrite /mapping_is_iso_mapping; apply kmapping_iso_out. Qed.

    (* Identity of hash_kp and associativity of function composition *)
    Lemma hkp_comp : (map HBnode \o (fun s : seq B => zip s (iota 0 (size s)))) = hash_kp.
    Proof. by []. Qed.

    (* Identity to fold back build_map_k *)
    Lemma build_hkp : build_kmapping_from_seq \o hash_kp = build_map_k.
    Proof. by []. Qed.

    (* For any two graphs g and h which are isomorphic under mu,
       for any permutation of the blank nodes of h: q,
       such that (build_map_k q) was the canonical kmapping for h,
       then for any permutation of the blank nodes of g: p,
       such that (build_map_k p) was the canonical kmapping for g,
       then relabeling h under (build_map_k q) has the same triples as
       relabeling h under (build_map_k (map mu p)) *)
    Axiom isocan_auto_symmetry :
      forall g h mu, is_iso_ts g h mu ->
                forall q, q \in permutations (get_bts h) ->
                           (k_mapping_ts h) = sort le_triple (relabeling_seq_triple (build_map_k q) h) ->
                           forall p, p \in permutations (get_bts g) ->
                                      (k_mapping_ts g) = sort le_triple (relabeling_seq_triple (build_map_k p) g) ->
                                      (relabeling_seq_triple (build_map_k q) h) =i (relabeling_seq_triple (build_map_k (map mu p)) h).


    Lemma rdf_leP ts1 ts2 : reflect (sort le_triple ts1 = sort le_triple ts2) (perm_eq ts1 ts2).
    Proof. by apply: (perm_sortP le_triple_total le_triple_trans le_triple_anti). Qed.

    Lemma uniq_build_map_k_perm (ts: seq (triple I B L)) (u : uniq ts):
      forall p : seq B, p \in permutations (get_bts ts) -> uniq (relabeling_seq_triple (build_map_k p) ts).
    Proof.
      rewrite /build_map_k=> p pinperm.
      suffices /inj_get_bts_inj_ts : {in get_bts ts &, injective (build_kmapping_from_seq (hash_kp p))}.
        by move=> /map_inj_in_uniq ->.
      by apply labeled_perm_inj=> //; apply candidate_in_perm.
    Qed.

    Lemma kmapping_can_invariant' ts1 ts2 (u1 : uniq ts1) (u2 : uniq ts2) (isogh : iso_ts ts1 ts2) : perm_eq (k_mapping_ts ts1) (k_mapping_ts ts2).
    Proof.
    have := iso_isokmap_ts (isogh) u1 u2.
    rewrite /k_mapping_ts /=.
    rewrite -!map_comp. rewrite -!(compA _ (map HBnode) _). rewrite !hkp_comp.
    rewrite -!(compA _ build_kmapping_from_seq hash_kp) build_hkp.
    move=> /iso_structure/orP[/andP[/eqP -> /eqP ->] // |/andP[]].
    set c1 := map (((relabeling_seq_triple (B2:=B))^~ ts1) \o build_map_k) (permutations (get_bts ts1)).
    have -> : [seq ((sort le_triple \o (relabeling_seq_triple (B2:=B))^~ ts1) \o build_map_k) i
                                      | i <- permutations (get_bts ts1)]
                = map (sort le_triple) c1 by rewrite -map_comp.
    set c2 := map (((relabeling_seq_triple (B2:=B))^~ ts2) \o build_map_k) (permutations (get_bts ts2)).
    have -> : [seq ((sort le_triple \o (relabeling_seq_triple (B2:=B))^~ ts2) \o build_map_k) i
                                      | i <- permutations (get_bts ts2)]
                = map (sort le_triple) c2 by rewrite -map_comp.
    set sc1 := map (sort le_triple) c1.
    set sc2 := map (sort le_triple) c2.
    move: (foldl_max_st sc1 [::]) (foldl_max_st sc2 [::]) =>[-> //| kg1inc1 ] [-> //| khinc2] _ _.
    have: sc1 =i sc2.
      move=> sc. apply/idP/idP.
      move=> /mapP /= [cc1 /mapP[/= p b ->] ->].
      rewrite /sc2.
      apply/mapP=> /=.
      case : isogh => mu /and3P [piso u peq].
      exists (relabeling_seq_triple (build_map_k (map mu p)) ts2).
      rewrite /c2. apply/mapP=> /=.
      exists (map mu p)=> //.
        rewrite mem_permutations. rewrite /is_pre_iso_ts in piso.
        have trans : perm_eq (map mu p) (map mu (get_bts ts1)) by apply perm_map; rewrite -mem_permutations.
        by apply (perm_trans trans piso).
        apply/rdf_leP.
        apply uniq_perm.
        by apply uniq_build_map_k_perm.
        apply uniq_build_map_k_perm=> //.
        rewrite mem_permutations. rewrite /is_pre_iso_ts in piso.
        have trans : perm_eq (map mu p) (map mu (get_bts ts1)) by apply perm_map; rewrite -mem_permutations.
        by apply (perm_trans trans piso).
        move=> t.
        apply perm_mem in peq.
        have <- : (relabeling_seq_triple (build_map_k (map mu p)) (relabeling_seq_triple mu ts1)) =i (relabeling_seq_triple (build_map_k [seq mu i | i <- p]) ts2).
        by apply relabeling_mem.
        rewrite relabeling_seq_triple_comp.
        apply relabeling_ext_in.
        have pg1_mem : p =i get_bts ts1 by rewrite mem_permutations in b; move/perm_mem : b.
        have mu_inj : {in p &, injective mu}. by move=> x y xin yin; apply (is_pre_iso_ts_inj2 piso); rewrite -pg1_mem.
        suffices build_modulo_map :
          forall b, b \in p -> (build_map_k p) b = build_map_k (map mu p) (mu b).
          case=> [[]]//s []p' []o// sib pii tin //=;
                        apply triple_inj=> //=; congr Bnode;
                                          rewrite build_modulo_map //;
                                            rewrite pg1_mem; apply (mem_ts_mem_triple_bts tin);
                                          rewrite /bnodes_triple filter_undup mem_undup /= ?in_cons ?eqxx ?orbT //.
        suffices upg1 : uniq p.
          move=> b1 bin; rewrite (out_of_build bin upg1) out_of_build.
          congr nat_inj; rewrite !nth_iota; first by rewrite index_map_in //.
          by rewrite index_mem; apply map_f.
          by rewrite index_mem.
          by apply map_f.
          by rewrite map_inj_in_uniq.
        by move: b; rewrite mem_permutations => /perm_uniq ->; rewrite uniq_get_bts.
        (* ====== *)
        rewrite iso_ts_sym // in isogh.
      move=> /mapP /= [cc1 /mapP[/= p b ->] ->].
      rewrite /sc2.
      apply/mapP=> /=.
      case : isogh => mu /and3P [piso u peq].
      exists (relabeling_seq_triple (build_map_k (map mu p)) ts1).
      rewrite /c2. apply/mapP=> /=.
      exists (map mu p)=> //.
        rewrite mem_permutations. rewrite /is_pre_iso_ts in piso.
        have trans : perm_eq (map mu p) (map mu (get_bts ts2)) by apply perm_map; rewrite -mem_permutations.
        by apply (perm_trans trans piso).
        apply/rdf_leP.
        apply uniq_perm.
        by apply uniq_build_map_k_perm.
        apply uniq_build_map_k_perm=> //.
        rewrite mem_permutations. rewrite /is_pre_iso_ts in piso.
        have trans : perm_eq (map mu p) (map mu (get_bts ts2)) by apply perm_map; rewrite -mem_permutations.
        by apply (perm_trans trans piso).
        move=> t.
        apply perm_mem in peq.
        have <- : (relabeling_seq_triple (build_map_k (map mu p)) (relabeling_seq_triple mu ts2)) =i (relabeling_seq_triple (build_map_k [seq mu i | i <- p]) ts1).
        by apply relabeling_mem.
        rewrite relabeling_seq_triple_comp.
        apply relabeling_ext_in.
        have pg1_mem : p =i get_bts ts2 by rewrite mem_permutations in b; move/perm_mem : b.
        have mu_inj : {in p &, injective mu}. by move=> x y xin yin; apply (is_pre_iso_ts_inj2 piso); rewrite -pg1_mem.
        suffices build_modulo_map :
          forall b, b \in p -> (build_map_k p) b = build_map_k (map mu p) (mu b).
          case=> [[]]//s []p' []o// sib pii tin //=;
                        apply triple_inj=> //=; congr Bnode;
                                          rewrite build_modulo_map //;
                                            rewrite pg1_mem; apply (mem_ts_mem_triple_bts tin);
                                          rewrite /bnodes_triple filter_undup mem_undup /= ?in_cons ?eqxx ?orbT //.
        suffices upg1 : uniq p.
          move=> b1 bin; rewrite (out_of_build bin upg1) out_of_build.
          congr nat_inj; rewrite !nth_iota; first by rewrite index_map_in //.
          by rewrite index_mem; apply map_f.
          by rewrite index_mem.
          by apply map_f.
          by rewrite map_inj_in_uniq.
        by move: b; rewrite mem_permutations => /perm_uniq ->; rewrite uniq_get_bts.
        rewrite !foldl_idx.
        move=> memeq.
        suffices -> : \big[join_ts_monoid/[::]]_(x <- sc1) x = \big[join_ts_monoid/[::]]_(x <- sc2) x.
          by rewrite perm_refl.
        by rewrite (eq_big_idem (fun x => true) _ join_st_idem memeq).
    Qed.

    (* For any two graphs g and h which are isomorphic,
       k_mapping returns set-equal results for g and h *)
    Lemma kmapping_can_invariant g h (isogh : iso g h) : eqb_rdf (k_mapping g) (k_mapping h).
    Proof.
    have := iso_isokmap (isogh).
    rewrite /k_mapping/k_mapping_ts/eqb_rdf rdf_perm_mem_eq rdf_mem_eq_graph /iso /=.
    rewrite -!map_comp. rewrite -!(compA _ (map HBnode) _). rewrite !hkp_comp.
    rewrite -!(compA _ build_kmapping_from_seq hash_kp) build_hkp.
    set cand1 := [seq (sort le_triple \o (relabeling_seq_triple (B2:=B))^~ g \o build_map_k) i | i <- permutations (get_bts g)].
    set cand2 := [seq (sort le_triple \o (relabeling_seq_triple (B2:=B))^~ h \o build_map_k) i | i <- permutations (get_bts h)].
    move=> /iso_structure/orP[/andP[/eqP -> /eqP ->] // |/andP[]].
    move: (foldl_max_st cand1 [::]) (foldl_max_st cand2 [::]) =>[-> //| kg1inc1 ] [-> //| khinc2] _ _.
    move/mapP : kg1inc1=> [/= p].
    move=> pperm1 eq; rewrite eq.
    move : isogh=> [mu /and3P[pisoP urel peq]] trpl.
    set c2_cand := relabeling_seq_triple (build_map_k (map mu p)) h.
    move/mapP : khinc2=> /=[q qin maxisocanh]; rewrite maxisocanh.
    have pg1_mem : p =i get_bts g. by rewrite mem_permutations in pperm1; move/perm_mem : pperm1.
    rewrite !mem_sort.
    have mu_inj : {in p &, injective mu}. by move=> x y xin yin; apply (is_pre_iso_inj pisoP); rewrite -pg1_mem.
    suffices -> : relabeling_seq_triple (build_map_k q) h =i c2_cand.
    rewrite /c2_cand.
      suffices -> : relabeling_seq_triple (build_map_k [seq mu i | i <- p]) h =i
                   relabeling_seq_triple ((build_map_k [seq mu i | i <- p]) \o mu) g.
        suffices eq1: {in g, relabeling_triple (build_map_k p) =1 relabeling_triple ((build_map_k (map mu p) \o mu))}.
          by rewrite (relabeling_ext_in eq1).
        suffices build_modulo_map :
          forall b, b \in p -> (build_map_k p) b = build_map_k (map mu p) (mu b).
          by case=> [[]]//s []p' []o// sib pii tin //=;
                        apply triple_inj=> //=; congr Bnode;
                                          rewrite build_modulo_map //;
                                            rewrite pg1_mem; apply (mem_ts_mem_triple_bts tin);
                                          rewrite /bnodes_triple filter_undup mem_undup /= ?in_cons ?eqxx ?orbT //.
        suffices upg1 : uniq p.
          move=> b bin; rewrite (out_of_build bin upg1) out_of_build.
          congr nat_inj; rewrite !nth_iota; first by rewrite index_map_in //.
          by rewrite index_mem; apply map_f.
          by rewrite index_mem.
          by apply map_f.
          by rewrite map_inj_in_uniq.
        by move: pperm1; rewrite mem_permutations => /perm_uniq ->; rewrite uniq_get_bts.
      by rewrite -relabeling_seq_triple_comp; apply: relabeling_mem=> x; rewrite (perm_mem peq).
    rewrite /c2_cand.
    have maxh : (k_mapping_ts h) = sort le_triple (relabeling_seq_triple (build_map_k q) h).
    by rewrite -maxisocanh/cand2/k_mapping_ts -!map_comp.
    have maxg1 : (k_mapping_ts g) = sort le_triple (relabeling_seq_triple (build_map_k p) g).
    by rewrite -eq/cand1/k_mapping_ts -!map_comp.
    have isogh : is_iso_ts g h mu by rewrite /is_iso_ts pisoP urel peq.
    by apply (@isocan_auto_symmetry _ _ _ isogh q qin maxh p pperm1 maxg1).
    Qed.

    (* k_mapping is an isocanonical mapping
       (WIP: still working on mechanizing the argument on which k_mapping_can_invariant relies *)
    Theorem iso_can_kmapping : isocanonical_mapping k_mapping.
    Proof.
    split=> [|g h].
    + by apply kmapping_iso_out.
    + split.
      - by apply same_res_impl_iso_mapping; rewrite /mapping_is_iso_mapping; apply kmapping_iso_out.
      - by apply kmapping_can_invariant.
    Qed.

  End Kmapping_isocan.

End Kmapping.
