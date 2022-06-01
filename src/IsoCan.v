From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From RDF Require Import Rdf Triple Term.
(* From Coq Require Import List. *)

Section IsoCan.
  (* Axiom todo : forall A,A. *)
  Variable I B L: countType.
  Let rdf_graph:= (rdf_graph I B L).
  Let triple:= (triple I B L).
  Let term:= (term I B L).
  Let term_countType := (term_countType I B L).
  Let is_bnode := (@is_bnode I B L).

  Definition isocanonical_function (M : B -> B) (g : rdf_graph) :=
    iso g (Rdf.relabeling M g) /\
      forall (h : rdf_graph), iso g h <-> (relabeling M g) = (relabeling M h).

  Section IsoCanAlgorithm.
    Variable h : countType.
    Definition hash_eqMixin := PcanEqMixin (@pickleK h).
    Definition hash_canChoiceMixin := PcanChoiceMixin (@pickleK h).
    Definition hash_canCountMixin := PcanCountMixin (@pickleK h).

    Canonical hash_eqType := Eval hnf in EqType h hash_eqMixin.
    Canonical hash_choiceType := Eval hnf in ChoiceType h hash_canChoiceMixin.
    Canonical hash_countType := Eval hnf in CountType h hash_canCountMixin.

    Definition hash_canPOrderMixin := PcanPOrderMixin (@pickleK hash_countType).
    Canonical hash_POrderType := Eval hnf in POrderType tt h hash_canPOrderMixin.
    Variable hashTerm : term -> h.

    Record hi_term :=
      mkHinput {
          input : term;
          output : h ;
          io : hashTerm input == output 
        }.

    Hypothesis perfectHashingSchemeTerm : injective hashTerm.

    Lemma by_perf_hash (i : term) (o : h) (eqb : hashTerm i == o) : hashTerm i = o. apply /eqP. apply eqb. Qed.

    Definition hi_term_inj_o (hin1 hin2: hi_term):
      output hin1 = output hin2 ->
      hin1 = hin2.
    Proof. case: hin1; case: hin2 => [i1 o1 io1] i2 o2 io2 /= oeq. 
           have ieq : i1 = i2.
           apply perfectHashingSchemeTerm; apply /eqP; by rewrite (by_perf_hash io1) (by_perf_hash io2) oeq.
           subst. by f_equal; apply eq_irrelevance.
    Qed.

    Definition hi_term_inj_i (hin1 hin2: hi_term):
      input hin1 = input hin2 ->
      hin1 = hin2.
    Proof. case: hin1; case: hin2 => [i1 o1 io1] i2 o2 io2 /= ieq. subst.
           have io1P: hashTerm i1 = o1. apply /eqP. apply io1.
           have io2P: hashTerm i1 = o2. apply /eqP. apply io2. subst. f_equal. apply eq_irrelevance.
    Qed.

    Definition code_hash (x : hi_term) :=
      let (i,_,_) := x in
      pickle i.

    Definition build_hash (i : term) : option hi_term.
    Proof.
      (* have o: h. exact (hashTerm i). *)
      have E : hashTerm i == hashTerm i. by [].
      - exact (Some (mkHinput E)).
    Defined.

    Definition decode_hash (x : nat) : option hi_term:=
      let ot := (@unpickle term_countType x) in
      match ot with
      | Some t => build_hash t
      | None => None
      end.

    Definition cancel_hin_encode : pcancel code_hash decode_hash.
    Proof. case => i o ioeq. rewrite /code_hash /decode_hash. rewrite pickleK.
           rewrite /build_hash. have ioeqP : hashTerm i = o. by apply /eqP; apply ioeq.
           rewrite /ssr_have /=. f_equal. by apply hi_term_inj_i.
    Qed.

    Definition hin_eqMixin := PcanEqMixin cancel_hin_encode.
    Definition hin_canChoiceMixin := PcanChoiceMixin cancel_hin_encode.
    Definition hin_canCountMixin := PcanCountMixin cancel_hin_encode.

    Canonical hin_eqType := Eval hnf in EqType hi_term hin_eqMixin.
    Canonical hin_choiceType := Eval hnf in ChoiceType hi_term hin_canChoiceMixin.
    Canonical hin_countType := Eval hnf in CountType hi_term hin_canCountMixin.
    Definition hin_canPOrderMixin := PcanPOrderMixin cancel_hin_encode.
    Canonical hin_POrderType := Eval hnf in POrderType tt h hash_canPOrderMixin.
    Definition hash := hi_term.

    (* Definition initTerm (t : term) : hash := *)
    (*   match t with *)
    (*   | Bnode name => None *)
    (*   | otherwise => Some (hi_term t) end. *)

    Definition hashmap := seq hash.

    (* Definition initHashMap (g : rdf_graph) : hashmap := map initTerm (terms g). *)
    (* Variable doHash (g : rdf_graph) (hm : hashmap) (hm : seq hashmap) (n : nat) -> seq hashmap. *)

    Variable hashNodes : (rdf_graph -> seq hashmap).
    Variable lookup_hashmap : (hashmap -> term -> hash).

    Hypothesis hash_dont_get_equal :
      forall (g : rdf_graph) (hms : seq hashmap)
             (ghashh : hashNodes g = hms)
             (i j : nat) (ileqj : i <= j) (lim : j < size hms)
             (x y : term) (bnx : is_bnode x) (bny : is_bnode y)
             (xing : x \in (terms g)) (ying : y \in (terms g)),
        (lookup_hashmap (nth [::] hms i) x != lookup_hashmap (nth [::] hms i) y)
        -> lookup_hashmap (nth [::] hms j) x != lookup_hashmap (nth [::] hms j) y.

    Hypothesis hashNodes_preserves_isomorphism :
      forall (g h: rdf_graph) (isogh : iso g h)
             (hash_g hash_h: hashmap)
             (hashg_hm : hash_g = last [::] (hashNodes g))
             (hashh_hm : hash_h = last [::] (hashNodes h))
             (b : term) (bing : b \in (bnodes (g)))
             (c : term) (cinh : c \in (bnodes (h))),
      exists μ, (relabeling_term μ b) = c -> lookup_hashmap hash_g b = lookup_hashmap hash_h c.

    (* Hypothesis perfectHashingSchemeTriple : injective hashTriple. *)

    Variable hashBag : (seq hash -> hash).
    Hypothesis hashBag_assoc : forall (l l1 l2 l3: seq hash) (perm : l = l1 ++ l2 ++ l3),
        hashBag ([:: hashBag (l1 ++ l2)] ++ l3) = hashBag (l1 ++ [:: hashBag (l2 ++ l3)]).
    Hypothesis hashBag_comm : forall (l l1 l2: seq hash) (perm : l = l1 ++ l2),
        hashBag l = hashBag (l2 ++ l1).

    Section Partition.

      Definition eq_rel (g : rdf_graph) (hm : hashmap) (b1 b2 : term) : bool :=
        (b1 \in (bnodes g)) && (b2 \in (bnodes g)) && (lookup_hashmap hm b1 == lookup_hashmap hm b2).

      Check partition.

      Fixpoint partitionate {A : Type} (f : A -> bool) (s:seq A) : list A * list A :=
        match s with
        | nil => (nil, nil)
        | x :: tl => let (g,d) := partitionate f tl in
                     if f x then (x::g,d) else (g,x::d)
        end.

      Definition part := seq hash.
      Definition partition := seq part.

      Definition mkPartition (g : rdf_graph) (hm : hashmap) : partition :=
        let bns := (bnodes g) in
        let equiv := (fun b => (fun t=> eq_rel g hm b t)) in
        let P := undup (map (fun b=> (partitionate (equiv b) bns).1 ) bns) in
        map (fun bs => map (lookup_hashmap hm) bs) P.

      Record Partition := mkPartition_ {
                             P : partition ;
                             g : rdf_graph ;
                             hm : hashmap ;
                             p_wf : P == mkPartition g hm ;
                             has_b : all (fun p=> ~~ (nilp p)) P ;
                             diff_hashes : uniq P 

                           }.

      (* Error: Cannot guess decreasing argument of fix. *)
      (* Definition mkPartition (g : rdf_graph) (hm : hashmap) := *)
      (*   let fix part (bnodes : seq term) (acc : seq (seq term)) := *)
      (*                match bnodes with *)
      (*                | nil => acc *)
      (*                | b :: bs => *)
      (*                    let equiv := (fun t=> eq_rel g hm b t) in *)
      (*                    let (a_part,rest) := partition equiv bs in *)
      (*                    part rest (a_part::acc) *)
      (*                end in *)
      (*   part (bnodes g) hm [::]. *)

      (* Definition mkPartition (g : rdf_graph) (hm : hashmap) := *)
      (*   let fix aux (bnodes : seq term) (acc : seq (seq term)) := *)
      (*                match bnodes with *)
      (*                | nil => acc *)
      (*                | b :: bs => *)
      (*                    let equiv := (fun t=> eq_rel g hm b t) in *)
      (*                    let part := filter equiv bs in *)
      (*                    let rest := foldr (@rem (term_eqType I B L)) bs part in *)
      (*                    aux rest (part::acc) *)
      (*                    (* aux (filter (fun t=>(~~ (equiv t))) bs) (part::acc) *) *)
      (*                end in *)
      (*   aux (bnodes g) hm [::]. *)

      (* Record partition := mkPartition { *)
      (*                        bnodes : seq term ; *)
      (*                        bnodes_r_bnodes : all is_bnode bnodes ; *)
      (*                        hm : hashmap ; *)


      (*                      }. *)

      Definition is_trivial (part : part) : bool :=
        size part == 1.

      Definition is_non_trivial (part : part) : bool :=
        ~~ is_trivial part.

      Definition is_fine (p : partition) : bool :=
        all is_trivial p.

      Definition is_coarse (p : partition) : bool :=
        size p == 1.

      Definition is_intermediate (p : partition) :=
        ~~ is_fine p && ~~ is_coarse p.



      (* Definition lt_part (part1 part2 : part) : bool := *)
      (*   if size part1 < size part2 then *)
      (*     true *)
      (*   else if size part1 == size part2 then *)


      (*          Definition le_partition (p1 p2 : partition) : bool :=  *)
      (*          fun T : Type => T -> pred T *)
      (*                                eq_refl. *)
      (*          . *)
      (*          Definition partition_LePOrderMixin := LePOrderMixin partition. *)
      (*          forall (T : eqType) (le lt : rel T), *)
      (*   (forall x y : T, lt x y = (y != x) && le x y) -> *)
      (*   reflexive le -> antisymmetric le -> transitive le -> lePOrderMixin T *)

      
    End Partition.

  End IsoCanAlgorithm.
  (* Hypothesis rdf_total_order   *)

End IsoCan.

