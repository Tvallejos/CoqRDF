From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term Util IsoCan.

Section Kmapping.
  Variable disp : unit.
  Variable I B L : orderType disp.
  Hypothesis to_string_nat : nat -> B.
  Hypothesis to_string_nat_inj : injective to_string_nat.

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
        to_string_nat (lookup_hash_default_ n0 the_bnode)
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
    foldl join_st [::] isocans.

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

  Lemma nth_bperms (ts : seq (triple I B L))
    (uniq_ts : uniq ts) (bn : B) db dn
    (bin : bn \in get_bts ts) (u : seq hterm)
    (mem : u \in  [seq [seq HBnode an | an <- i]
                  | i <- [seq zip s (iota 0 (size s)) | s <- permutations (get_bts ts)]]) :
    exists n : nat, nth (HBnode (db ,dn)) u (find (eqb_b_hterm bn) u) = HBnode (bn, n).
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
    by apply hash_nth_mapzip.
  by move=> ? ?; apply: find_index_eqbb; rewrite size_iota.
  Qed.

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

  Lemma labeled_perm_inj
    (ts : seq (triple I B L)) (uniq_ts : uniq ts)
    u (mem : u \in [seq [seq HBnode an | an <- i]
                   | i <- [seq zip s (iota 0 (size s))
                         | s <- permutations (get_bts ts)]]) :
    {in get_bts ts &, injective (build_kmapping_from_seq u)}.
  Proof.
  move=> x y xin yin; rewrite /build_kmapping_from_seq.
  suffices mem_has: forall b, b \in get_bts ts -> has (eqb_b_hterm b) u.
    rewrite !mem_has // => /to_string_nat_inj.
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

  Lemma candidate_in_perm (ts : seq (triple I B L)) perm
    (bin : perm \in permutations (get_bts ts)) :
    [seq (HBnode an) | an <- zip perm (iota 0 (size perm))]
      \in [seq [seq HBnode an | an <- i]
          | i <- [seq zip s (iota 0 (size s)) | s <- permutations (get_bts ts)]].
  Proof.
    by apply/mapP; exists (zip perm (iota 0 (size perm)))=> //; apply /mapP; exists perm=> //.
  Qed.

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


  Lemma foldl_max_st (l : seq (seq (triple I B L))) (x0 : (seq (triple I B L))):
    foldl join_st x0 l = x0 \/ foldl join_st x0 l \in l.
  Proof. elim: l x0 => [//| t ts IHts] x0; first by left.
       + rewrite in_cons /=; case: (IHts (join_st x0 t))=> [ -> |intail] /=.
       - rewrite join_st_def. case: ifP=> _; first by right; rewrite eqxx.
         * by left.
       - by right; rewrite intail orbT.
  Qed.

  Lemma max_foldl_minimum_st (l : seq (seq (triple I B L))) (x : seq (triple I B L)) :
    (forall y : (seq (triple I B L)) , lt_st x y) -> foldl join_st x l = x -> (l == [::]) || (x \in l).
  Proof. move=> minimum.
       elim: l=> [//| hd t IHt].
       rewrite /= join_st_def minimum.
       case: (foldl_max_st t hd).
       by move=> -> ->; rewrite in_cons eqxx.
       by move=> H <-; rewrite in_cons H orbT.
  Qed.

  Lemma max_foldl_minimum_in_st (l : seq (seq (triple I B L))) (x : seq (triple I B L)) :
    (forall y : (seq (triple I B L)) , y \in l -> lt_st x y) -> foldl join_st x l = x -> (l == [::]) || (x \in l).
  Proof.
       elim: l=> [//| hd t IHt] minimum.
       rewrite /= join_st_def minimum; last by rewrite in_cons eqxx.
       case: (foldl_max_st t hd).
       by move=> -> ->; rewrite in_cons eqxx.
       by move=> H <-; rewrite in_cons H orbT.
  Qed.

  Lemma uniq_k_mapping (ts : rdf_graph I B L) : uniq (k_mapping_ts ts).
  Proof.
    case: ts => ts uniq_ts /=; rewrite /k_mapping_ts.
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

  Definition k_mapping (g : rdf_graph I B L) : rdf_graph I B L :=
    @mkRdfGraph I B L (k_mapping_ts (graph g)) (uniq_k_mapping g).

  Section Kmapping_isocan.

    Lemma join_nil_size (h : seq (triple I B L)) :
      (size h != 0) -> join_st [::] h != [::].
    Proof. by case: h=> //. Qed.

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

    Lemma kmapping_iso_out g: iso g (k_mapping g).
    Proof.
      rewrite /mapping_is_iso_mapping/k_mapping/iso/iso_ts/is_iso_ts.
      have := uniq_k_mapping g.
      case : g=> ts uts /=; rewrite /k_mapping_ts.
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

    Lemma iso_structure (ts1 ts2: seq (triple I B L)) :
      iso_ts ts1 ts2 -> ((ts1 == [::]) && (ts2 == [::]) || (ts1 != [::]) && (ts2 != [::])).
    Proof.
      rewrite /iso_ts/is_iso_ts /=; move=> [? /and3P [_ _]] ; case: ts1=> [|h1 tl1].
      + by rewrite relabeling_seq_triple_nil perm_sym=> /perm_nilP ->.
      + by apply contraTneq=> -> ; apply /perm_nilP.
    Qed.

    Lemma build_from_nil (ts : seq (triple I B L)) :
      relabeling_seq_triple (build_kmapping_from_seq [::]) ts = ts.
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

    Lemma eqb_b_hterm_memP (b : B) (s : seq B) :
      b \in s ->
            has (eqb_b_hterm (I:=I) (L:=L) b) [seq Bnode (mkHinput an.1 an.2) | an <- zip s (iota 0 (size s))].
    Proof.
      move=> b1in ; apply/ (has_nthP (Bnode (mkHinput b 0))).
      exists (index b s).
      by rewrite size_map size_zip size_iota minn_refl index_mem.
      by rewrite nth_mapzip /= ?size_iota // nth_index // eqxx.
    Qed.

    Lemma out_of_build b s :
      b \in s -> uniq s ->
            (build_map_k s) b = to_string_nat (nth 0 (iota 0 (size s)) (index b s)).
    Proof.
      move=> bin ubs.
      rewrite /build_map_k/build_kmapping_from_seq (eqb_b_hterm_memP bin); congr to_string_nat.
      by rewrite find_index_eqbb ?size_iota // nth_mapzip ?size_iota //.
    Qed.

    Lemma iso_isokmap g h (igh: iso g h) : iso (k_mapping g) (k_mapping h).
    Proof. by apply: iso_can_trans _ igh; rewrite /mapping_is_iso_mapping; apply kmapping_iso_out. Qed.

    Lemma hkp_comp : (map HBnode \o (fun s : seq B => zip s (iota 0 (size s)))) = hash_kp.
    Proof. by []. Qed.

    Lemma build_hkp : build_kmapping_from_seq \o hash_kp = build_map_k.
    Proof. by []. Qed.

    Axiom isocan_auto_symmetry :
      forall g h mu, is_iso_ts g h mu ->
                forall q, q \in permutations (get_bts h) ->
                           (k_mapping_ts h) = sort le_triple (relabeling_seq_triple (build_map_k q) h) ->
                           forall p, p \in permutations (get_bts g) ->
                                      (k_mapping_ts g) = sort le_triple (relabeling_seq_triple (build_map_k p) g) ->
                                      (relabeling_seq_triple (build_map_k q) h) =i (relabeling_seq_triple (build_map_k (map mu p)) h).

    Lemma kmapping_can_invariant g g2 (isogg2 : iso g g2) : eqb_rdf (k_mapping g) (k_mapping g2).
    Proof.
    have := iso_isokmap (isogg2).
    rewrite /k_mapping/k_mapping_ts/eqb_rdf rdf_perm_mem_eq rdf_mem_eq_graph /iso /=.
    rewrite -!map_comp. rewrite -!(compA _ (map HBnode) _). rewrite !hkp_comp.
    rewrite -!(compA _ build_kmapping_from_seq hash_kp) build_hkp.
    set cand1 := [seq (sort le_triple \o (relabeling_seq_triple (B2:=B))^~ g \o build_map_k) i | i <- permutations (get_bts g)].
    set cand2 := [seq (sort le_triple \o (relabeling_seq_triple (B2:=B))^~ g2 \o build_map_k) i | i <- permutations (get_bts g2)].
    move=> /iso_structure/orP[/andP[/eqP -> /eqP ->] // |/andP[]].
    move: (foldl_max_st cand1 [::]) (foldl_max_st cand2 [::]) =>[-> //| kg1inc1 ] [-> //| kg2inc2] _ _.
    move/mapP : kg1inc1=> [/= p].
    move=> pperm1 eq; rewrite eq.
    move : isogg2=> [mu /and3P[pisoP urel peq]] trpl.
    set c2_cand := relabeling_seq_triple (build_map_k (map mu p)) g2.
    move/mapP : kg2inc2=> /=[q qin maxisocanh]; rewrite maxisocanh.
    have pg1_mem : p =i get_bts g. by rewrite mem_permutations in pperm1; move/perm_mem : pperm1.
    rewrite !mem_sort.
    have mu_inj : {in p &, injective mu}. by move=> x y xin yin; apply (is_pre_iso_inj pisoP); rewrite -pg1_mem.
    suffices -> : relabeling_seq_triple (build_map_k q) g2 =i c2_cand.
    rewrite /c2_cand.
      suffices -> : relabeling_seq_triple (build_map_k [seq mu i | i <- p]) g2 =i
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
          congr to_string_nat; rewrite !nth_iota; first by rewrite index_map_in //.
          by rewrite index_mem; apply map_f.
          by rewrite index_mem.
          by apply map_f.
          by rewrite map_inj_in_uniq.
        by move: pperm1; rewrite mem_permutations => /perm_uniq ->; rewrite uniq_get_bts.
      by rewrite -relabeling_seq_triple_comp; apply: relabeling_mem=> x; rewrite (perm_mem peq).
    rewrite /c2_cand.
    have maxg2 : (k_mapping_ts g2) = sort le_triple (relabeling_seq_triple (build_map_k q) g2).
    by rewrite -maxisocanh/cand2/k_mapping_ts -!map_comp.
    have maxg1 : (k_mapping_ts g) = sort le_triple (relabeling_seq_triple (build_map_k p) g).
    by rewrite -eq/cand1/k_mapping_ts -!map_comp.
    have isogh : is_iso_ts g g2 mu by rewrite /is_iso_ts pisoP urel peq.
    by apply (@isocan_auto_symmetry _ _ _ isogh q qin maxg2 p pperm1 maxg1).
    Qed.

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
