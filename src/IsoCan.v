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

  Definition isocanonical_function (M : B -> B) (g : rdf_graph) :=
    iso g (Rdf.relabeling M g) /\
      forall (h : rdf_graph), iso g h <-> (relabeling M g) = (relabeling M h).

  Section IsoCanAlgorithm.
    Variable h : eqType.
    Variable hashTerm : term -> h.

    (* Record hinput := mkHinput { *)
    (*                     A : Type; *)
    (*                     input : A ; *)
    (*                     output : h ; *)
    (*                     f : A -> h; *)
    (*                     (* heqin : f input == output *) *)
    (*                   }. *)

    Record hi_term :=
      mkHinput {
          input : term;
          output : h ;
          io : hashTerm input == output 
        }.

    (* Definition hi_triple (t : triple) := *)
    (*   {| *)
    (*       A := triple; *)
    (*       input := t; *)
    (*       output := hashTriple t; *)
    (*       f := hashTriple; *)
    (*   |}. *)

    Hypothesis perfectHashingSchemeTerm : injective hashTerm.

    Lemma by_perf_hash (i : term) (o : h) (eqb : hashTerm i == o) : hashTerm i = o. apply /eqP. apply eqb. Qed.

    Definition hi_term_inj (hin1 hin2: hi_term):
      output hin1 = output hin2 ->
      hin1 = hin2.
    Proof. case: hin1; case: hin2 => [i1 o1 io1] i2 o2 io2 /= oeq. 
           have ieq : i1 = i2.
           apply perfectHashingSchemeTerm; apply /eqP; by rewrite (by_perf_hash io1) (by_perf_hash io2) oeq.
           subst. by f_equal; apply eq_irrelevance.
    Qed.

    Definition eqb_hi_term (hin1 hin2: hi_term) : bool :=
      output hin1 == output hin2.

    Lemma hi_term_eqP : Equality.axiom eqb_hi_term.
    Proof.
      rewrite /Equality.axiom => x y.
      apply: (iffP idP) => //= [| ->]; rewrite /eqb_hi_term.
      case: x; case: y => [ix ox iox] iy oy ioy /= eq. apply hi_term_inj. rewrite /=. apply /eqP. apply eq.
      by [].
    Qed.

    Canonical hi_term_eqType := EqType hi_term (EqMixin hi_term_eqP).
    (* Inductive hit (t : term) : h -> Type := *)
    (* | ha : hit t (hashTerm t). *)

    (* Definition hit_eq (t : term) : (hit t (hashTerm t)) := *)
    (*   (ha t).  *)

    Definition hash := option hi_term.

    (* Definition eqb_hash (h1 h2: hash) := *)
    (*   match h1, h2 with *)
    (*   | None,None => true *)
    (*   | Some hin1,Some hin2 => hin1 == hin2 *)
    (*   | _,_ => false *)
    (*   end. *)

    Canonical hash_eqType := EqType hash [eqMixin of hash].


    (* Definition initTerm (t : term) : hash := *)
    (*   match t with *)
    (*   | Bnode name => None *)
    (*   | otherwise => Some (hi_term t) end. *)

    Definition hashmap := seq hash.

    (* Definition initHashMap (g : rdf_graph) : hashmap := map initTerm (terms g). *)
    (* Variable doHash (g : rdf_graph) (hm : hashmap) (hm : seq hashmap) (n : nat) -> seq hashmap. *)

    Variable hashNodes : (rdf_graph -> seq hashmap).
    Variable lookup_hashmap : (hashmap -> term -> hash).

    (* Let nth := nth hashmap [::]. *)

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

  End IsoCanAlgorithm.
  (* Hypothesis rdf_total_order   *)

End IsoCan.
