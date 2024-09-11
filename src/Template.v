Require Import Program.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term Util IsoCan.

(******************************************************************************)
(*                                                                            *)
(*            κ-mapping algorithm rewritten in a functional style             *)
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
  Definition inspect {A} (x : A) : { y : A | x = y } := @exist _ _ x (erefl x).

  Lemma size_filter {T : Type} (f : T -> bool) (l : seq T) : size (filter f l ) <= size l.
  Proof. elim: l=> // hd tl IHl /=. case (f hd)=> //.
         have /(_ (size tl)) H : forall n, n < n.+1 by apply ltnSn.
         by apply (Order.POrderTheory.le_le_trans IHl H).
  Qed.

  Lemma nat_coq_nat (n m : nat) :  (n < m)%nat = (n < m). Proof. by []. Qed.

  Program Fixpoint gen_partition (hm : hash_map) (acc : partition) {measure (size hm)} :=
    match hm with
     | nil => acc
     | (_,n)::_ =>
  gen_partition (partitionate n hm).2 ((partitionate n hm).1::acc) end.
  Next Obligation.
    rewrite /= /eq_hash/pred_eq/negb /= eqxx /=.
    have H := size_filter ((fun b : bool => if b then false else true) \o (fun p : B * nat => n == p.2)) wildcard'0.
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

  Program Fixpoint foldl_In {T R : eqType} (s : seq T) (f : R -> forall (y : T), y \in s -> R) z {struct s}: R :=
    match s with
    | [::] => z
    | x :: s' => @foldl_In T R s' f (f z x _) end.
  Next Obligation. by rewrite in_cons x2 orbT. Qed.
  Next Obligation. by rewrite in_cons eqxx. Qed.

  Lemma foldl_foldl_eq {T R : eqType} (s : list T) (f : R -> T -> R) z :
    @foldl_In _ _ s (fun r t (_ : t \in s) => f r t) z = foldl f z s.
  Proof. by elim: s f z => //=. Qed.


  Section Distinguish.
    Hypothesis (color color_refine : seq (triple I B L) -> hash_map -> hash_map).
    Hypothesis (mark : B -> hash_map -> hash_map).
    Hypothesis (cmp : seq (triple I B L) -> seq (triple I B L) -> bool).
    Hypothesis (M : hash_map -> nat).
    Hypothesis (markP : forall (bn : (B * nat)) (hm : hash_map), bn \in chose_part hm -> M (mark bn.1 hm) < M hm).
    Hypothesis (color_refineP : forall (g : seq (triple I B L)) (hm : hash_map) , M (color_refine g hm) <= M hm).

    Program Fixpoint distinguish
      (g : seq (triple I B L))
      (hm : hash_map)
      (gbot : seq (triple I B L))
      {measure (M hm)} : seq (triple I B L) :=
      let p := chose_part hm in
      let f := fun gbot bn (inP : bn \in p) =>
                 let hm' := color_refine g (mark bn.1 hm) in
                 if is_fine (gen_partition hm' [::]) then
                   let candidate := relabeling_seq_triple (fun_of_hash_map hm') g in
                   if cmp gbot candidate
                   then candidate else gbot
                 else (distinguish g hm' gbot) in
      foldl_In f gbot.
    Next Obligation.
      apply /ltP.
      rewrite nat_coq_nat.
      (* Set Printing All. *)
      eapply (Order.POrderTheory.le_lt_trans). apply color_refineP. by apply markP.
    Qed.

    Hypothesis (init_hash : seq (triple I B L) -> hash_map).
    Hypothesis init_hash_bnodes : forall (g : seq (triple I B L)), bnodes_of_hash_map (init_hash g) =i get_bts g.
    Hypothesis color_bnodes : forall (g : seq (triple I B L)) hm, bnodes_of_hash_map (color g hm) =i bnodes_of_hash_map hm.

    Definition template (g : seq (triple I B L)) :=
      let hm := init_hash g in
      let hm' := color g hm in
      let iso_g := if is_fine (gen_partition hm' [::])
                   then relabeling_seq_triple (fun_of_hash_map hm') g
                   else distinguish g hm' [::] in
      iso_g.

    Program Lemma uniq_distinguish g : (negb \o is_fine) (gen_partition (color g (init_hash g)) [::]) -> uniq (distinguish g (color g (init_hash g)) [::]).
    Proof.
      rewrite /distinguish. rewrite /distinguish_func.
      Fail set p := chose_part _.
    Admitted.

    Lemma uniq_template (g : seq (triple I B L)) (ug: uniq g) : uniq (template g).
    Proof. rewrite /template.
           case: ifP=> H. by apply fun_of_fine_hash_map_uniq=> //; move=> b; rewrite color_bnodes init_hash_bnodes.
           by apply uniq_distinguish; rewrite /=H.
    Qed.
    End Distinguish.







