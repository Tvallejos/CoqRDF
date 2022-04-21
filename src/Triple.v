From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Term.

Section Triple.
  Variable I B L: eqType.
  Let term:= (term I B L).
  Let is_iri:= (@is_iri I B L).
  Let is_bnode:= (@is_bnode I B L).
  Let is_lit:= (@is_lit I B L).

  Record triple := mkTriple { subject : term
                            ; predicate : term
                            ; object: term
                            ; subject_in_IB: is_in_ib subject == true
                            ; predicate_in_I: is_in_i predicate == true
                            ; object_in_IBL: is_in_ibl object == true
                    }. 

  Lemma triple_inj : forall (t1 t2: triple),
      subject t1 == subject t2 ->
      predicate t1 == predicate t2 ->
      object t1 == object t2 ->
      t1 = t2.
  Proof. move=> [s1 p1 o1 sin1 pin1 oin1] [s2 p2 o2 sin2 pin2 oin2] /= seq peq oeq.
         (* apply seq in sin1. apply (eq_irrelevance sin1 sin2). *)
         (* congr sin1 sin2. *)
         (* elim: s1 s2=> [i1 b1 l1] [i2 b2 l2]. *)
         (* rewrite (bool_irrelevance sin1 sin2). *)
         (* rewrite /subject /predicate /object /=. *)
         (* rewrite seq. *)
         (* apply: val. rewrite seq. (eq_irrelevance bool). *)
  Admitted.

  Definition eqb_triple  (t1 t2 : triple) : bool :=
    ((subject t1) == (subject t2)) &&
      ((predicate t1) == (predicate t2)) &&
      ((object t1) == (object t2)).

  Lemma triple_eqP : Equality.axiom eqb_triple.
  Proof.
    rewrite /Equality.axiom => x y.
    apply: (iffP idP) => //= [| ->]; rewrite /eqb_triple; case: x y=> [s1 p1 o1 sin1 pin1 oin1] [s2 p2 o2 sin2 pin2 oin2] //=.
    case/andP; case/andP=> /eqP eq_s/eqP eq_p/eqP eq_o.
    apply: triple_inj; move=> //= {sin1 sin2 pin1 pin2 oin1 oin2}; apply /eqP; by [].
    rewrite !eq_refl //.
  Qed.


  (* Canonical triple_eqType := EqType term (EqMixin triple_inj). *)

  (* alias for triple of terms type *)
  (* Definition triple := (node * term * term)%type.  *)

(*
    Inductive rdf : Type :=
    | graph (triples : list triple).
 *)

  (* Definition image (t : triple) (μ : B -> B) : triple := *)
  (*   let (s,p,o,sin,pin,oin) := t in *)
  (*   {μ s,μ p,μ o,sin,pin,oin}. *)




  (* Definition eqb_triple (t1 t2:trpl) : bool := *)
  (*   (match t1,t2 with *)
  (*   | (triple s p o),(triple s2 p2 o2) => (eqb_term s s2) && (eqb_term p p2) && (eqb_term o o2) *)
  (*   end). *)

  (* Theorem eqb_eq_triple: forall (t1 t2 : trpl), *)
  (*   eqb_triple t1 t2 = true <-> t1 = t2. *)
  (* Proof. intros. split; intros H. *)
  (*   - destruct t1,t2 as [s2 p2 o2]; f_equal; *)
  (*     simpl in H; apply andb_true_iff in H; destruct H as [H0 H2]; apply andb_true_iff in H0; destruct H0 as [H H1]; apply eqb_eq_term.  *)
  (*     + apply H. *)
  (*     + apply H1. *)
  (*     + apply H2. *)
  (*   - destruct t1,t2 as [s2 p2 o2]. injection H as H1 H2 H3. simpl. rewrite H1. rewrite H2. rewrite H3. *)
  (*     rewrite (eqb_term_refl s2). rewrite (eqb_term_refl p2). rewrite (eqb_term_refl o2). reflexivity. *)
  (* Qed. *)

  (* Theorem eqb_triple_refl : forall (t1: trpl), *)
  (*   eqb_triple t1 t1 = true. *)
  (* Proof. intros. destruct t1. simpl. rewrite (eqb_term_refl s). rewrite (eqb_term_refl p). rewrite (eqb_term_refl o). reflexivity. *)
  (* Qed. *)

  (* Theorem eqb_neq_triple : forall (t1 t2: trpl), *)
  (*   eqb_triple t1 t2 = false <-> t1 <> t2. *)
  (* Proof. intros. split. *)
  (*   - intros H contra. rewrite contra in H. rewrite eqb_triple_refl in H. discriminate H. *)
  (*   - intros H. unfold not in H. rewrite <- eqb_eq_triple in H. destruct (eqb_triple t1 t2). *)
  (*     + exfalso. apply H. reflexivity. *)
  (*     + reflexivity. *)
  (* Qed. *)

  (* Theorem eq_dec_triple : forall (t1 t2: trpl), *)
  (*   {t1 = t2} + {t1 <> t2}. *)
  (* Proof. decide equality; try decide equality; try apply string_dec; decide equality. Qed. *)

End Triple.
