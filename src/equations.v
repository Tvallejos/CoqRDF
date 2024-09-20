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
    @foldl_In _ _ s (fun r t (_ : t \in s) => f r t) z = foldl f z s.
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
	                let hm' := color_refine g (mark bn.1 hm) in
	                if is_fine (gen_partition hm' [::]) then
	                  let candidate := relabeling_seq_triple (fun_of_hash_map hm') g in
	                  candidate
	                else (distinguish g hm' gbot) in
      let f := fun gbot bn inP  =>
                 let candidate := d bn inP in
                 if cmp gbot candidate then candidate else gbot in
      (* foldl f gbot p. *)
      foldl_In p f gbot.
      Proof.
      apply /ltP.
      rewrite nat_coq_nat.
      eapply (Order.POrderTheory.le_lt_trans). apply color_refineP.
      rewrite /p in inP.
      have -> : s = (s,n).1 by [].
      by apply markP.
      Qed.

    Hypothesis init_hash_bnodes : forall (g : seq (triple I B L)), bnodes_of_hash_map (init_hash g) =i get_bts g.
    Hypothesis color_bnodes : forall (g : seq (triple I B L)) hm, bnodes_of_hash_map (color g hm) =i bnodes_of_hash_map hm.

    Variable can : seq (triple I B L).
    Hypothesis ucan : uniq can.

    Definition template (g : seq (triple I B L)) :=
      let hm := init_hash g in
      let hm' := color g hm in
      let iso_g := if is_fine (gen_partition hm' [::])
                   then relabeling_seq_triple (fun_of_hash_map hm') g
                   else distinguish g hm' can in
      iso_g.


    Hypothesis distinguish_choice : forall (g : seq (triple I B L)) (hm: hash_map) (gcan : seq (triple I B L)),
      let f := fun bn =>
	               let hm' := color_refine g (mark bn.1 hm) in
	               if is_fine (gen_partition hm' [::]) then
	                 let candidate := relabeling_seq_triple (fun_of_hash_map hm') g in
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
      -  move=> isFine. apply uniq_label_is_fine=> //. apply color_refine_good_hm. apply good_mark. apply eqbns.
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
           case: ifP=> H. by apply fun_of_fine_hash_map_uniq=> //; move=> b; rewrite color_bnodes init_hash_bnodes.
           apply uniq_distinguish.
           apply color_good_hm.
           apply good_init.
           by rewrite /= H.
    Qed.

    End Distinguish.









