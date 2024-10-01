From Equations Require Import Equations.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
(* Unset Strict Implicit. *)
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term Util IsoCan.

(******************************************************************************)
(*                                                                            *)
(*            template defined with equations                                 *)
(*                                                                            *)
(******************************************************************************)



Section Template.
  Variable disp : unit.
  Variable I B L : orderType disp.

  Hypothesis nat_inj : nat -> B.
  Hypothesis nat_inj_ : injective nat_inj.

  Definition hash_map := seq (B * nat).
  Definition part := seq (B * nat).
  Definition partition := seq part.
  Definition pred_eq {T : eqType} (t: T):= fun t'=> t == t'.
  Definition eq_hash (n : nat) (p: B * nat) := pred_eq n p.2.
  Definition eq_bnode (b : B) (p: B * nat) := pred_eq b p.1.
  Definition partitionate (n : nat) (hm : hash_map) :=
    (filter (eq_hash n) hm, filter (negb \o eq_hash n) hm).
  (* Definition inspect {A} (x : A) : { y : A | x = y } := @exist _ _ x (eq_refl x). *)

  Lemma size_filter {T : Type} (f : T -> bool) (l : seq T) : size (filter f l ) <= size l.
  Proof. elim: l=> // hd tl IHl /=. case (f hd)=> //.
         have /(_ (size tl)) H : forall n, n < n.+1 by apply ltnSn.
         by apply (Order.POrderTheory.le_le_trans IHl H).
  Qed.

  Lemma nat_coq_nat (n m : nat) :  (n < m)%nat = (n < m). Proof. by []. Qed.

  Equations? gen_partition (hm : hash_map) (acc : partition) : partition by wf (size hm) lt :=
    gen_partition nil acc := acc;
    gen_partition (bn::l) acc := gen_partition (partitionate bn.2 (bn::l)).2 ((partitionate bn.2 (bn::l)).1::acc).
  Proof.
    rewrite /= /eq_hash/pred_eq/negb /= eqxx /=.
    have H := size_filter ((fun b : bool => if b then false else true) \o (fun p : B * nat => n == p.2)) l.
    apply /ltP.
    by apply : leq_trans H _.
  Qed.

  Definition is_trivial (p : part) : bool := size p == 1.
  Definition is_fine (P : partition) : bool := all is_trivial P.
  Variable choose_part : hash_map -> part.
  Definition n0 := 0.

  Definition fun_of_hash_map (hm : hash_map) : B -> B :=
    fun b =>
      if has (eq_bnode b) hm then
        let the_label := nth n0 (map snd hm) (find (eq_bnode b) hm) in
        nat_inj the_label
      else
        b.

  Definition bnodes_hm (hm : hash_map): seq B :=
    map fst hm.

  Definition hashes_hm (hm : hash_map): seq nat :=
    map snd hm.

    Equations? foldl_In {T R : eqType} (s : seq T) (f : R -> forall (y : T), y \in s -> R) (z : R) : R :=
    foldl_In nil f z := z;
    foldl_In (a :: l) f z := foldl_In l (fun x y inP=> f x y _) (f z a _).
  Proof.
    by rewrite in_cons inP orbT.
    by rewrite in_cons eqxx.
  Qed.

  Lemma foldl_foldl_eq {T R : eqType} (s : list T) (f : R -> T -> R) z :
    @foldl_In _ _ s (fun r t (_ : t \in s) => f r t) z = foldl f z s.
  Proof.
    funelim (foldl_In s _ z).
    - by [].
    - autorewrite with foldl_In; apply H.
  Qed.

  Section Distinguish.
    Variables (color color_refine : seq (triple I B L) -> hash_map -> hash_map).
    Variable (mark : B -> hash_map -> hash_map).
    Variable (cmp : seq (triple I B L) -> seq (triple I B L) -> bool).
    Variable (M : hash_map -> nat).

    Hypothesis (markP : forall (bn : B * nat) (hm : hash_map), bn \in choose_part hm -> M (mark bn.1 hm) < M hm).
    Hypothesis (color_refineP : forall (g : seq (triple I B L)) (hm : hash_map) , M (color_refine g hm) <= M hm).
    Hypothesis in_part_in_bnodes : forall bn hm, bn \in choose_part hm -> bn.1 \in bnodes_hm hm.
    Variable (init_hash : seq (triple I B L) -> hash_map).

    Lemma bnodes_hm_exists (hm : hash_map) :
      forall b, b \in bnodes_hm hm -> exists n, (b,n) \in hm.
    Proof.
      move=> b /mapP/=[[b' n] bin ->]/=. by exists n.
    Qed.

    Lemma bnodes_hm_has_eq_bnodes (hm : hash_map) :
        forall b, b \in bnodes_hm hm -> has (eq_bnode b) hm.
    Proof.
    move=> b /bnodes_hm_exists/=[n bnin].
    apply /hasP. exists (b,n)=> //.
    by rewrite /eq_bnode/pred_eq eqxx.
    Qed.

    Lemma find_index_eq_bnode bs s (bn : B) :
      size s = size bs ->
      find (eq_bnode bn) (zip bs s) = index bn bs.
    Proof.
      elim: bs s => [| a l IHl]; first by move=> ?; rewrite zip0s.
      by case =>  [//| b l2] /= [eqsize_tl]; rewrite eq_sym IHl //.
    Qed.

    Lemma is_fine_uniq (hm : hash_map) :
      is_fine (gen_partition hm [::]) -> uniq (map snd hm).
    Proof.
    (* elim: hm=> [//| [b n] tl IHtl]. *)
    funelim (gen_partition hm [::]); first by [].
    rewrite /==> fine.
    apply /andP; split.
    admit.
    apply H.
    rewrite /=.
    case: ifP.
    case : bn H Heqcall fine=> b n H Heqcall fine=> /=.
    + case_eq (eq_hash n (b,n)); first by [].
      move=> eqhash _.
      apply DepElim.pack_sigma_eq_nondep.
      Set Printing All. congr .
      apply IHtl.
      move/allP : fine=> /==> fineIn.
      apply /allP.
      move=> /= p pin.
      apply fineIn.

      autorewrite with gen_partition=> /=; rewrite eqhash /=. => fine.

      rewrite /=.

      rewrite eq_hash.
    rewrite /negb. move=> neq_hash. rewrite neq_hash.
    move /eqP.
    rewrite /eq_hash.

    Admitted.

    Lemma size_proj (T1 T2 : Type) (s : seq (T1 * T2)) : size [seq i.2 | i <- s] = size [seq i.1 | i <- s].
    Proof. by elim: s=> [//| h tl IHtl] /=; rewrite IHtl. Qed.

    Lemma nth_funof (g : seq (triple I B L)) (hm : hash_map) :
      bnodes_hm hm =i get_bts g ->
          is_fine (gen_partition hm [::]) ->
          forall (b : B) dfb dfn (bin : b \in get_bts g),
      exists n, (nth (dfb, dfn) hm (index b [seq i.1 | i <- hm])) = (b,n).
    Proof. move=> mem_eq fine b bdf dfn. rewrite -mem_eq.
           exists (nth dfn [seq i.2 | i <- hm] (index b [seq i.1 | i <- hm])).
           have hm_zip : hm = zip (map fst hm) (map snd hm).
           rewrite zip_map; elim: hm {mem_eq fine bin}=> [//| [h1 h2] tl IHtl] /=; by rewrite -IHtl.
           rewrite hm_zip.
           rewrite nth_zip; last by rewrite size_proj.
           congr pair.
           by rewrite -hm_zip nth_index.
           by rewrite -hm_zip.
    Qed.

    Lemma funof_snd_inj (g : seq (triple I B L)) (hm : hash_map) :
      bnodes_hm hm =i get_bts g ->
      is_fine (gen_partition hm [::]) ->
      uniq (hashes_hm hm) ->
      {in hm &, injective [eta snd]}.
    Proof.
    have hm_zip : hm = zip (map fst hm) (map snd hm).
    rewrite zip_map; elim: hm=> [//| [h1 h2] tl IHtl] /=; by rewrite -IHtl.
    rewrite hm_zip.
    set hm' := zip _ _.
    move=> mem_eq fine uhm /= bn bn' bnin bn'in.
    eapply (zip_uniq_proj2 ).
    apply is_fine_uniq; apply fine.
    symmetry; by apply size_proj.
    by rewrite /hm' -hm_zip.
    by rewrite /hm' -hm_zip.
    Qed.

    Lemma uniq_get_bts_is_fine (g : seq (triple I B L)) hm :
      bnodes_hm hm =i get_bts g ->
      is_fine (gen_partition hm [::]) ->
      uniq [seq fun_of_hash_map hm i | i <- get_bts g].
    Proof.
      have hm_zip : hm = zip (map fst hm) (map snd hm).
      rewrite zip_map; elim: hm=> [//| [h1 h2] tl IHtl] /=; by rewrite -IHtl.
      move=> mem_eq fine.
      apply /in_map_injP; first by apply uniq_get_bts.
      move=> b b' bin b'in.
      rewrite /fun_of_hash_map.
      rewrite -!mem_eq in bin b'in.
      have  hasb:= (bnodes_hm_has_eq_bnodes _ _ bin).
      have hasb' := (bnodes_hm_has_eq_bnodes _ _ b'in).
      rewrite hasb hasb'.
      move=> /nat_inj_.
      rewrite hm_zip.
      have eqsize: size [seq i.2 | i <- hm] = size [seq i.1 | i <- hm] by apply size_proj.
      rewrite !find_index_eq_bnode //.
      rewrite -!hm_zip.
      move=> eq_nth.
      have [n nin]:= bnodes_hm_exists hm b bin.
      have [n' n'in]:= bnodes_hm_exists hm b' b'in.
      move/eqP : eq_nth.
      suffices [inb inb'] : (index b [seq i.1 | i <- hm] < size hm)%N /\ (index b' [seq i.1 | i <- hm] < size hm)%N.
      rewrite (nth_map (b,O)) // (nth_map (b',O)) //.
      have [n'' n''P]: exists n, (nth (b, O) hm (index b [seq i.1 | i <- hm])) = (b,n). by apply (nth_funof g)=> //; rewrite -mem_eq.
      rewrite n''P.
      have [n''' n'''P]: exists n, (nth (b', O) hm (index b' [seq i.1 | i <- hm])) = (b',n). by apply (nth_funof g)=> //; rewrite -mem_eq.
      rewrite n'''P.
      move=> /eqP eqpair.
      apply (funof_snd_inj g hm mem_eq fine) in eqpair.
      by move : eqpair => [->].
      by apply is_fine_uniq.
      by rewrite -n''P; apply mem_nth.
      by rewrite -n'''P; apply mem_nth.
      split.
      rewrite -(find_index_eq_bnode (map fst hm) (map snd hm)) //.
      by rewrite -hm_zip -has_find.
      rewrite -(find_index_eq_bnode (map fst hm) (map snd hm)) //.
      by rewrite -hm_zip -has_find.
    Qed.

    Lemma uniq_label_is_fine (g : seq (triple I B L)) (ug: uniq g) (hm : hash_map) :
      bnodes_hm hm =i get_bts g ->
      is_fine (gen_partition hm [::]) ->
      uniq (relabeling_seq_triple (fun_of_hash_map hm) g).
    Proof. move=> mem_eq fine.
           have := uniq_get_bts_is_fine _ _ mem_eq fine.
           move=> /(in_map_injP _ (uniq_get_bts _)) mu_inj.
           rewrite map_inj_in_uniq=> //.
           by apply inj_get_bts_inj_ts.
    Qed.

    Hypothesis good_mark : forall (g : seq (triple I B L)) hm, bnodes_hm hm =i get_bts g -> forall b, b \in bnodes_hm hm -> bnodes_hm (mark b hm) =i get_bts g.

    Hypothesis good_init :
      forall (g : seq (triple I B L)),
        bnodes_hm (init_hash g) =i get_bts g.
    Hypothesis color_good_hm :
      forall (g : seq (triple I B L)) hm,
        bnodes_hm hm =i get_bts g -> bnodes_hm (color g hm) =i get_bts g.

    Hypothesis color_refine_good_hm :
      forall (g : seq (triple I B L)) hm,
                 bnodes_hm hm =i get_bts g -> bnodes_hm (color_refine g hm) =i get_bts g.

    Notation le_triple := (@le_triple disp I B L).

    Variable can : seq (triple I B L).
    Hypothesis ucan : uniq can.

    Equations? distinguish__
      (g : seq (triple I B L))
        (hm : hash_map)
        (gbot : seq (triple I B L))
        : seq (triple I B L) by wf (M hm) lt :=
      distinguish__ g hm gbot :=
      let p := choose_part hm in
	    let d := fun bn inP =>
	               let hm' := color_refine g (mark bn.1 hm) in
	               if is_fine (gen_partition hm' [::]) then
	                 let candidate := sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g) in
	                 candidate
	               else (distinguish__ g hm' gbot) in
      let f := fun gbot bn inP  =>
                 let candidate := d bn inP in
                 if cmp gbot candidate then candidate else gbot in
      foldl_In p f gbot.
      Proof.
        apply /ltP.
        rewrite nat_coq_nat.
        eapply (Order.POrderTheory.le_lt_trans). apply color_refineP.
        by apply : (markP (s,n)).
      Qed.

    Definition distinguish (g : seq (triple I B L)) (hm : hash_map) : seq (triple I B L) :=
      distinguish__ g hm can.

    Definition distinguish_ (g : seq (triple I B L)) (hm : hash_map) : seq (triple I B L) :=
      let p := choose_part hm in
	    let d := fun bn =>
	               let hm' := color_refine g (mark bn.1 hm) in
	               if is_fine (gen_partition hm' [::]) then
	                 let candidate := sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g) in
	                 candidate
	               else (distinguish g hm') in
      let f := fun gbot bn  =>
                 let candidate := d bn in
                 if cmp gbot candidate then candidate else gbot in
      foldl f can p.

    Lemma eq_distinguish (g : seq (triple I B L)) (hm : hash_map) :
      distinguish g hm = distinguish_ g hm.
    Proof. rewrite /distinguish_/distinguish. rewrite -foldl_foldl_eq.
           autorewrite with distinguish__. by []. Qed.

    Definition canonicalize (g : seq (triple I B L)) (hm : hash_map)
      (* (gbot : seq (triple I B L)) *)
      (bn : (B * nat)) :=
	      let hm' := color_refine g (mark bn.1 hm) in
	      if is_fine (gen_partition hm' [::]) then
	        let candidate := sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g) in
	        candidate
	      else (distinguish g hm').

    Definition choose_graph (gbot candidate : seq (triple I B L)) :=
      if cmp gbot candidate then candidate else gbot.

    Definition distinguish_fold (g : seq (triple I B L)) (hm : hash_map) : seq (triple I B L) :=
      let p := choose_part hm in
      foldl choose_graph can (map (canonicalize g hm) p).

    Lemma fold_map (T1 T2 R : Type) (f : R -> T2 -> R) (g : T1 -> T2) (z : R) (s : seq T1) :
      foldl (fun r1 t1=> f r1 (g t1)) z s = foldl f z (map g s).
    Proof. by elim: s z=> [//| a tl IHl] /= z; rewrite -IHl. Qed.

    Lemma distinguish_fold_map (g : seq (triple I B L)) (hm : hash_map) :
      distinguish g hm = distinguish_fold g hm.
    Proof. by rewrite /distinguish_fold eq_distinguish /distinguish_  -fold_map /canonicalize. Qed.

    Hypothesis init_hash_bnodes : forall (g : seq (triple I B L)), bnodes_hm (init_hash g) =i get_bts g.

    Hypothesis color_bnodes : forall (g : seq (triple I B L)) hm, bnodes_hm (color g hm) =i bnodes_hm hm.

    Definition template (g : seq (triple I B L)) :=
      let hm := init_hash g in
      let hm' := color g hm in
      let iso_g := if is_fine (gen_partition hm' [::])
                   then (sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g))
                   else distinguish g hm' in
      iso_g.

    Lemma distinguish_choice (g : seq (triple I B L)) (hm: hash_map) :
      distinguish g hm = can \/ distinguish g hm \in (map (canonicalize g hm) (choose_part hm)).
    Proof.
      rewrite distinguish_fold_map/distinguish_fold.
      set l := (choose_part hm).
      set x0 := can.
      elim: l x0 => [//| t ts IHts] x0; first by left.
      + rewrite in_cons /=. case: (IHts (choose_graph x0 (canonicalize g hm t)))=> [ -> |intail] /=.
      - rewrite /choose_graph; case: ifP=> _; first by right; rewrite eqxx.
        * by left.
      - by right; rewrite intail orbT.
    Qed.

    Lemma uniq_distinguish (g : seq (triple I B L)) (ug: uniq g) hm :
      bnodes_hm hm =i get_bts g -> (negb \o is_fine) (gen_partition hm [::]) -> uniq (distinguish g hm).
    Proof.
      have : M hm < S (M hm) by apply ltnSn.
      move: hm (M hm).+1.
      move=> hm n; move: n hm=> n.
      elim: n => [//| n IHn hm].
      case: (distinguish_choice g hm); first by move=> ->; rewrite ucan.
      move=> /mapP/= [bn pin ->].
      move=> MH eqbns finePn.
      rewrite /canonicalize.
      case: ifP.
      -  move=> isFine; rewrite sort_uniq.
         apply uniq_label_is_fine=> //. apply color_refine_good_hm. apply good_mark. apply eqbns.
         by apply in_part_in_bnodes.
      - move=> finePn1. apply IHn.
        eapply Order.POrderTheory.le_lt_trans.
        apply color_refineP.
        eapply Order.POrderTheory.lt_le_trans.
        by apply markP.  apply MH.
      -  apply color_refine_good_hm. apply good_mark. by [].
      -  by apply in_part_in_bnodes.
      -  by move=> /=; rewrite finePn1.
    Qed.

    Lemma uniq_template (g : seq (triple I B L)) (ug: uniq g) : uniq (template g).
    Proof. rewrite /template.
           case: ifP=> H. rewrite sort_uniq.
           apply uniq_label_is_fine=> //.
           by move=> h; rewrite color_bnodes init_hash_bnodes.
           apply uniq_distinguish=> //.
           apply color_good_hm.
           apply good_init.
           by rewrite /= H.
    Qed.

    Lemma mem_nilP (T : eqType) (s : seq T) : s =i [::] <-> s = [::].
    Proof. case: s=> [//| h tl]. split; last by move=> ->.
           move=> mem.
           have := in_nil h.
           by rewrite -mem in_cons eqxx //.
    Qed.

    Lemma mem_eq_terms_ts (g h : seq (triple I B L)) :
      g =i h -> terms_ts g =i terms_ts h.
    Proof.
    move=> /= mem_eq t.
    rewrite /terms_ts.
    rewrite !mem_undup.
    apply /idP/idP.
    move=> /flatten_mapP /=[t' t'ing tinterm].
    apply /flatten_mapP=> /=.
    exists t'. by rewrite -mem_eq. by apply tinterm.
    move=> /flatten_mapP /=[t' t'ing tinterm].
    apply /flatten_mapP=> /=.
    exists t'. by rewrite mem_eq. by apply tinterm.
    Qed.

    Lemma mem_eq_bnodes_ts (g h : seq (triple I B L)) :
      g =i h -> bnodes_ts g =i bnodes_ts h.
    Proof.
      move=> /mem_eq_terms_ts mem_eq b; rewrite /bnodes_ts !mem_undup.
      by rewrite !mem_filter mem_eq.
    Qed.

    Lemma mem_eq_get_bts (g h : seq (triple I B L)) :
      g =i h -> get_bts g =i get_bts h.
    Proof.
      move=> /mem_eq_bnodes_ts mem_eq b.
      by apply eq_mem_pmap.
    Qed.


    Lemma piso_sort (g: seq (triple I B L)) (mu : B -> B) :
      is_pre_iso_ts g (sort le_triple (relabeling_seq_triple mu g)) mu <-> is_pre_iso_ts g (relabeling_seq_triple mu g) mu.
    Proof.
      rewrite /is_pre_iso_ts/bnode_map_bij.
      rewrite !uniq_get_bts/=.
      split=> H.
      apply uniq_perm.
      by rewrite (perm_uniq H) uniq_get_bts.
      by rewrite uniq_get_bts.
      move=> b; rewrite (perm_mem H).
      by apply mem_eq_get_bts=> b'; rewrite mem_sort.
      apply uniq_perm.
      by rewrite (perm_uniq H) uniq_get_bts.
      by rewrite uniq_get_bts.
      move=> b; rewrite (perm_mem H).
      by apply mem_eq_get_bts=> b'; rewrite mem_sort.
      Qed.

    Lemma uniq_map_pre_iso (mu : B -> B) (ts : seq (triple I B L)) :
      uniq (map mu (get_bts ts)) ->
      is_pre_iso_ts ts (relabeling_seq_triple mu ts) mu.
    Proof. move=> umu. rewrite /is_pre_iso_ts. rewrite /bnode_map_bij. rewrite !uniq_get_bts /=.
           apply perm_eq_bts_relabel_inj_in.
           apply /in_map_injP=> //. apply uniq_get_bts.
           by apply perm_refl.
    Qed.


    Lemma piso_funof (g : seq (triple I B L)) (hm: hash_map) :
        bnodes_hm hm =i get_bts g ->
        is_fine (gen_partition hm [::]) ->
        is_pre_iso_ts g (relabeling_seq_triple (fun_of_hash_map hm) g) (fun_of_hash_map hm).
    Proof.
      move=> mem_eq fine. apply uniq_map_pre_iso. by apply uniq_get_bts_is_fine.
    Qed.

    Lemma init_hash_nil : init_hash [::] = [::].
    Proof.
    move: (good_init [::]).
    case: (init_hash [::]) ; first by [].
    move=> [b n] l; rewrite /get_bts/==> contr.
    have := in_nil b.
    by rewrite -contr in_cons eqxx.
    Qed.

    Lemma color_nil_nil : color [::] [::] = [::].
    Proof.
    move: (color_good_hm [::] [::]).
    rewrite /get_bts/=.
    have /(_ B) H : [::] =i [::] by move=> b.
    move=> /(_ H){H}.
    case: (color [::] [::]) ; first by [].
    move=> [b n] l contr.
    have := in_nil b.
    by rewrite -contr in_cons eqxx.
    Qed.

    Lemma template_nil_nil : template [::] = [::].
    Proof.
    rewrite /template/=; case: ifP; first by [].
    rewrite init_hash_nil. rewrite color_nil_nil.
    autorewrite with gen_partition.
    by [].
    Qed.

    Lemma nil_is_nil (g : seq (triple I B L)) (hm : hash_map) :
      ~~ is_fine (gen_partition (color g (init_hash g)) [::]) ->
      distinguish g hm = can -> g = can.
    Proof.
    Admitted.
    (* prove this *)

    Hypothesis sort_can : sort le_triple can = can.

    Lemma distinguish_piso : forall (g : seq (triple I B L)) (ug: uniq g),
        ~~ is_fine (gen_partition (color g (init_hash g)) [::]) ->
      exists mu : B -> B,
        distinguish g (color g (init_hash g)) = sort le_triple (relabeling_seq_triple mu g) /\
          is_pre_iso_ts g (distinguish g (color g (init_hash g))) mu.
    Proof.
      move=> g ug finePn.
      set hm := (color g (init_hash g)).
      have : M hm < S (M hm) by apply ltnSn.
      have : bnodes_hm hm =i get_bts g by apply color_good_hm; apply good_init.
      move: hm (M hm).+1.
      move=> hm n; move: n hm=> n.
      elim: n => [//| n IHn hm' ghm hmM].
      move: (distinguish_choice g hm')=> /=[].
      + move=> H. rewrite H. exists id. split. apply (nil_is_nil _ _ finePn) in H.
        by rewrite relabeling_seq_triple_id H.
        apply (nil_is_nil _ _ finePn) in H.
        rewrite H.
        rewrite /is_pre_iso_ts /= /bnode_map_bij.
        by rewrite (uniq_get_bts _) /= map_id perm_refl.
      + move=> /mapP/=[bn inp ->].
        case_eq  (is_fine (gen_partition (color_refine g (mark bn.1 hm')) [::]))=> H.
        exists (fun_of_hash_map (color_refine g (mark bn.1 hm'))).
        split=> //.
        by rewrite /canonicalize H.
        rewrite /canonicalize H.
        apply piso_sort.
        apply piso_funof.
        apply color_refine_good_hm. apply good_mark=> //.
        by apply in_part_in_bnodes.
        by apply H.
      + rewrite /canonicalize H. apply IHn.
        apply color_refine_good_hm.
        apply good_mark=> //.
        by apply in_part_in_bnodes.
        eapply Order.POrderTheory.le_lt_trans.
        apply color_refineP.
        eapply Order.POrderTheory.lt_le_trans.
        by apply markP.
        by apply hmM.
    Qed.

    Lemma preiso_out_template (g : seq (triple I B L)) (ug : uniq g) :
      exists mu, (template g) = sort le_triple (relabeling_seq_triple mu g) /\ is_pre_iso_ts g (template g) mu.
    Proof.
      move/eqP : (eq_refl (template g)).
      rewrite {2}/template.
      case: ifP=> is_fine ->.
      exists (fun_of_hash_map (color g (init_hash g))).
      split=> //. apply piso_sort. apply piso_funof=> //.
      apply color_good_hm; apply good_init.
      by apply distinguish_piso=> //; rewrite is_fine.
    Qed.

    Lemma eiso_sort (g: seq (triple I B L)) (mu : B -> B) :
        is_effective_iso_ts g (relabeling_seq_triple mu g) mu ->
        is_effective_iso_ts g (sort le_triple (relabeling_seq_triple mu g)) mu.
    Proof. move=> /and3P/= [piso urel peq].
           apply /and3P; split=> //.
           by apply piso_sort.
           apply uniq_perm=> //.
           by rewrite sort_uniq.
           by move=> b; rewrite mem_sort.
    Qed.

    Lemma eiso_out_template (g : seq (triple I B L)) (ug : uniq g) : effective_iso_ts g (template g).
    Proof.
      rewrite /iso_ts.
      move: (uniq_template g ug).
      suffices [mu  [-> piso utg]]: exists mu, (template g) = sort le_triple (relabeling_seq_triple mu g) /\ is_pre_iso_ts g (template g) mu.
      rewrite sort_uniq in utg.
      exists mu; apply eiso_sort.
      have {piso}piso : is_pre_iso_ts g (relabeling_seq_triple mu g) mu. apply piso_sort in piso. by apply piso.
      move : (ts_pre_iso_effective_iso utg piso)=> eiso //.
      by apply preiso_out_template.
    Qed.


    Hypothesis iso_color_fine : forall (g h : seq (triple I B L)),
      uniq g -> uniq h ->
      effective_iso_ts g h ->
      is_fine (gen_partition (color g (init_hash g)) [::]) =
        is_fine (gen_partition (color h (init_hash h)) [::]).

    Hypothesis iso_color_fine_can : forall (g h : seq (triple I B L)),
        uniq g -> uniq h ->
        effective_iso_ts g h ->
        relabeling_seq_triple (fun_of_hash_map (color g (init_hash g))) g
        =i relabeling_seq_triple (fun_of_hash_map (color h (init_hash h))) h.

    Hypothesis distinguish_complete : forall (g h : seq (triple I B L)),
        uniq g -> uniq h ->
        effective_iso_ts g h ->
        is_fine (gen_partition (color g (init_hash g)) [::]) = false ->
        distinguish g (color g (init_hash g)) == distinguish h (color h (init_hash h)).

    Hypothesis choose_graphA : associative choose_graph.
    Hypothesis choose_graphC : commutative choose_graph.
    Hypothesis choose_graph_idem : idempotent choose_graph.
    Hypothesis gbot_lid : left_id can choose_graph.

    HB.instance Definition _ :=
    Monoid.isComLaw.Build
      (seq (triple I B L)) can
      (choose_graph) choose_graphA
      choose_graphC
      gbot_lid.

    Hypothesis eiso_mem_eq_canonicalize : forall (g h : seq (triple I B L)) (ug: uniq g) (uh: uniq h),
        effective_iso_ts g h ->
        is_fine (gen_partition (color g (init_hash g)) [::]) = false ->
        map (canonicalize g (color g (init_hash g))) (choose_part (color g (init_hash g))) =i
             map (canonicalize h (color h (init_hash h))) (choose_part (color h (init_hash h))).

    Lemma eiso_correct_complete (g h : seq (triple I B L)) (ug: uniq g) (uh: uniq h) :
      effective_iso_ts g h <-> (template g) == (template h).
    Proof.
      split; last first.
      move=> /eqP eqmgmh.
      have := eiso_out_template g ug.
      rewrite eqmgmh=> mgh.
      have /(effective_iso_ts_sym uh) hmh := eiso_out_template h uh.
      by apply: (effective_iso_ts_trans mgh hmh).
      rewrite /template=> eiso.
      rewrite -(iso_color_fine _ _ eiso) //.
      case: ifP.
      move=> is_fineP.
      apply /eqP/rdf_leP.
      apply uniq_perm.
      apply uniq_label_is_fine=> //. apply color_good_hm. apply good_init.
      rewrite (iso_color_fine _ _ eiso) // in is_fineP.
      apply uniq_label_is_fine=> //. apply color_good_hm. apply good_init.
      by apply iso_color_fine_can.
      move=> is_finePn.
      rewrite !distinguish_fold_map /distinguish_fold.
      set cang := (map _ (choose_part (color g (init_hash g)))).
      set canh := (map _ (choose_part (color h (init_hash h)))).
      suffices mem_eq : cang =i canh.
      by rewrite !foldl_idx (eq_big_idem (fun x => true) _ choose_graph_idem mem_eq) eqxx.
      by apply eiso_mem_eq_canonicalize.
    Qed.

  End Distinguish.









