From Equations Require Import Equations.
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
  Variable chose_part : hash_map -> part.
  Hypothesis chose_part_non_trivial : forall hm, negb (is_fine (gen_partition hm [::])) -> negb (is_trivial (chose_part hm)).
  Definition n0 := 0.

  Definition fun_of_hash_map (hm : hash_map) : B -> B :=
    fun b =>
      if has (eq_bnode b) hm then
        let the_label := nth n0 (map snd hm) (find (eq_bnode b) hm) in
        nat_inj the_label
      else
        b.

  Fixpoint bnodes_of_hash_map (hm : hash_map): seq B :=
    match hm with
    | [::] => [::]
    | (b,n)::tl => b::(bnodes_of_hash_map tl)
    end.

  Hypothesis fun_of_fine_hash_map_uniq :
    forall (g : seq (triple I B L)) hm, (uniq g) ->
                                        is_fine (gen_partition hm [::]) ->
                                        bnodes_of_hash_map hm =i get_bts g -> uniq (relabeling_seq_triple (fun_of_hash_map hm) g).

    Equations? foldl_In {T R : eqType} (s : seq T) (f : R -> forall (y : T), y \in s -> R) (z : R) : R :=
    foldl_In nil f z := z;
    foldl_In (a :: l) f z := foldl_In l (fun x y inP=> f x y _) (f z a _).
  Proof.
    by rewrite in_cons inP orbT.
    by rewrite in_cons eqxx.
  Qed.

  Lemma foldl_foldl_eq {T R : eqType} (s : list T) (f : R -> T -> R) z :

    @foldl_In _ _ s (fun r t (_ : t \in s) => f r t) z =
      foldl f z s.
  Proof.
    funelim (foldl_In s _ z).
    - by [].
    - autorewrite with foldl_In; apply H.
  Qed.

  Section Distinguish.
    Hypothesis (color color_refine : seq (triple I B L) -> hash_map -> hash_map).
    Hypothesis (mark : B -> hash_map -> hash_map).
    Hypothesis (cmp : seq (triple I B L) -> seq (triple I B L) -> bool).
    Hypothesis (M : hash_map -> nat).
    Hypothesis (markP : forall bn  (hm : hash_map), bn \in chose_part hm -> M (mark bn.1 hm) < M hm).
    Hypothesis (color_refineP : forall (g : seq (triple I B L)) (hm : hash_map) , M (color_refine g hm) <= M hm).
    Variable bnodes_hm : hash_map -> seq B.
    Hypothesis in_part_in_bnodes : forall bn hm, bn \in chose_part hm -> bn.1 \in bnodes_hm hm.
    Hypothesis (init_hash : seq (triple I B L) -> hash_map).
    Hypothesis uniq_label_is_fine :
      forall (g : seq (triple I B L)) hm, bnodes_hm hm =i get_bts g ->
                                          is_fine (gen_partition hm [::]) ->
                                          uniq (relabeling_seq_triple (fun_of_hash_map hm) g).
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

      Equations? distinguish
      (g : seq (triple I B L))
        (hm : hash_map)
        (gbot : seq (triple I B L))
        : seq (triple I B L) by wf (M hm) lt :=
      distinguish g hm gbot :=
      let p := chose_part hm in
	    let d := fun bn inP =>
	    (* let d := fun bn => *)
	               let hm' := color_refine g (mark bn.1 hm) in
	               if is_fine (gen_partition hm' [::]) then
	                 let candidate := relabeling_seq_triple (fun_of_hash_map hm') g in
	                 candidate
	               else (distinguish g hm' gbot) in
      let f := fun gbot bn inP  =>
      (* let f := fun gbot bn  => *)
                 (* let candidate := d bn in *)
                 let candidate := d bn inP in
                 if cmp gbot candidate then candidate else gbot in
      (* foldl f gbot p. *)
      foldl_In p f gbot.
      Proof.
        apply /ltP.
        rewrite nat_coq_nat.
        eapply (Order.POrderTheory.le_lt_trans). apply color_refineP.
        by apply : (markP (s,n)).
      Qed.

    Hypothesis init_hash_bnodes : forall (g : seq (triple I B L)), bnodes_of_hash_map (init_hash g) =i get_bts g.
    Hypothesis color_bnodes : forall (g : seq (triple I B L)) hm, bnodes_of_hash_map (color g hm) =i bnodes_of_hash_map hm.

    Variable can : seq (triple I B L).
    Hypothesis ucan : uniq can.

    Notation le_triple := (@le_triple disp I B L).

    Definition template (g : seq (triple I B L)) :=
      let hm := init_hash g in
      let hm' := color g hm in
      let iso_g := if is_fine (gen_partition hm' [::])
                   then (sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g))
                   else distinguish g hm' can in
      iso_g.


    Hypothesis distinguish_choice : forall (g : seq (triple I B L)) (hm: hash_map) (gcan : seq (triple I B L)),
      let f := fun bn =>
	               let hm' := color_refine g (mark bn.1 hm) in
	               if is_fine (gen_partition hm' [::]) then
	                 let candidate := sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g) in
	                 candidate
	               else (distinguish g hm' gcan) in
      distinguish g hm gcan = gcan \/ distinguish g hm gcan \in (map f (chose_part hm)).

    Lemma uniq_distinguish (g : seq (triple I B L)) hm :
      bnodes_hm hm =i get_bts g -> (negb \o is_fine) (gen_partition hm [::]) -> uniq (distinguish g hm can).
    Proof.
      have : M hm < S (M hm) by apply ltnSn.
      move: hm (M hm).+1.
      move=> hm n; move: n hm=> n.
      elim: n => [//| n IHn hm].
      case: (distinguish_choice g hm can); first by move=> ->; rewrite ucan.
      move=> /mapP/= [bn pin ->].
      move=> MH eqbns finePn.
      case : ifP.
      -  move=> isFine. rewrite sort_uniq. apply uniq_label_is_fine=> //. apply color_refine_good_hm. apply good_mark. apply eqbns.
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
           case: ifP=> H. rewrite sort_uniq. by apply fun_of_fine_hash_map_uniq=> //; move=> b; rewrite color_bnodes init_hash_bnodes.
           apply uniq_distinguish.
           apply color_good_hm.
           apply good_init.
           by rewrite /= H.
    Qed.

    Hypothesis piso_sort : forall (g: seq (triple I B L)) (mu : B -> B), is_pre_iso_ts g (sort le_triple (relabeling_seq_triple mu g)) mu <-> is_pre_iso_ts g (relabeling_seq_triple mu g) mu.

    Hypothesis piso_funof : forall (g : seq (triple I B L)) (hm: hash_map),
        bnodes_hm hm =i get_bts g -> is_fine (gen_partition hm [::]) -> is_pre_iso_ts g (relabeling_seq_triple (fun_of_hash_map hm) g) (fun_of_hash_map hm).

    Hypothesis nil_is_nil : forall g hm, distinguish g hm can = can -> g = can.
    Hypothesis sort_can : sort le_triple can = can.

    Lemma distinguish_piso : forall (g : seq (triple I B L)) (ug: uniq g), exists mu : B -> B,
        distinguish g (color g (init_hash g)) can = sort le_triple (relabeling_seq_triple mu g) /\
          is_pre_iso_ts g (distinguish g (color g (init_hash g)) can) mu.
    Proof.
      move=> g ug.
      set hm := (color g (init_hash g)).
      have : M hm < S (M hm) by apply ltnSn.
      have : bnodes_hm hm =i get_bts g by apply color_good_hm; apply good_init.
      (* rewrite /hm. *)
      move: hm (M hm).+1.
      move=> hm n; move: n hm=> n.
      elim: n => [//| n IHn hm' ghm hmM].
      (* set hm := (color g (init_hash g)). *)
      move: (distinguish_choice g hm' can)=> /=[].
      + move=> H. rewrite H. exists id. split. apply nil_is_nil in H. by rewrite H relabeling_seq_triple_id sort_can.
        apply nil_is_nil in H.
        rewrite H.
        rewrite /is_pre_iso_ts /= /bnode_map_bij.
        by rewrite (uniq_get_bts _) /= map_id perm_refl.
      + move=> /mapP/=[bn inp ->].
        case_eq  (is_fine (gen_partition (color_refine g (mark bn.1 hm')) [::]))=> H.
        exists (fun_of_hash_map (color_refine g (mark bn.1 hm'))).
        split=> //.
        (* rewrite H. *)
        (* rewrite H. *)
        apply piso_sort.
        apply piso_funof.
        apply color_refine_good_hm. apply good_mark=> //.
        (* apply color_good_hm. apply good_init. *)
        by apply in_part_in_bnodes.
        by apply H.
      + apply IHn.
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
      by apply distinguish_piso.
    Qed.

    Hypothesis eiso_sort : forall (g: seq (triple I B L)) (mu : B -> B), effective_iso_ts g (relabeling_seq_triple mu g) ->
                                                                         effective_iso_ts g (sort le_triple (relabeling_seq_triple mu g)).

    Lemma eiso_out_template (g : seq (triple I B L)) (ug : uniq g) : effective_iso_ts g (template g).
    Proof.
      rewrite /iso_ts.
      move: (uniq_template g ug).
      suffices [mu  [-> piso utg]]: exists mu, (template g) = sort le_triple (relabeling_seq_triple mu g) /\ is_pre_iso_ts g (template g) mu.
      rewrite sort_uniq in utg.
      apply eiso_sort.
      have {piso}piso : is_pre_iso_ts g (relabeling_seq_triple mu g) mu. apply piso_sort in piso. by apply piso.
      move : (ts_pre_iso_effective_iso utg piso)=> eiso.
      by exists mu.
      by apply preiso_out_template.
    Qed.


  End Distinguish.









