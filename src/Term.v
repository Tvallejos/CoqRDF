From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Term.

  (* literals should be of Datatype type, is not important for the moment*)
  Variable I B L: eqType.

  (* Definition eqb_i (i1 i2 : I) : bool := *)
  (*   bool_of_sumbool (Ieq_dec i1 i2). *)

  Inductive term : Type :=
  | Iri (id: I) 
  | Lit (l : L) 
  | Bnode (name : B).


  Definition is_lit (t : term ): bool :=
    (match t with
     | Lit _ => true
     | _ => false
     end).

  Definition is_iri (t : term ) : bool :=
    (match t with
     | Iri _ => true
     | _ => false
     end).

  Definition is_bnode (t : term ) : bool :=
    (match t with
     | Bnode _ => true
     | _ => false
     end).

  Definition eqb_term (t1 t2 : term) : bool :=
    (match t1, t2 with
     | (Iri id1), (Iri id2) => id1 == id2
     | (Lit l1),(Lit l2) => l1 == l2
     | (Bnode b1),(Bnode b2) => b1 == b2
     | _,_ => false
     end).

  Theorem eq_l_eq_lit : forall (l1 l2:L),
      (l1 = l2) <-> (Lit l1)  = (Lit l2).
  Proof. split; intros H.
         - rewrite H. reflexivity.
         - injection H as H2. apply H2.
  Qed.

  Theorem eq_i_eq_iri : forall (i1 i2:I) ,
      (i1 = i2) <-> (Iri i1) = (Iri i2).
  Proof. split; intros H.
         - rewrite H. reflexivity.
         - injection H as H2. apply H2.
  Qed.

  Theorem eq_b_eq_bnode : forall (b1 b2:B) ,
      (b1 = b2) <-> (Bnode b1) = (Bnode b2).
  Proof. split; intros H.
         - rewrite H. reflexivity.
         - injection H as H2. apply H2.
  Qed.

  Definition is_in_ib (t : term) : bool :=
    is_iri t || is_bnode t.

  Definition is_in_i (t : term) : bool :=
    is_iri t.

  Definition is_in_ibl (t : term) : bool :=
    is_iri t || is_bnode t || is_lit t.

  Lemma term_eqP : Equality.axiom eqb_term.
  Proof.
    rewrite /Equality.axiom => x y.
    apply: (iffP idP) => //= [| ->]; rewrite /eqb_term; last by case y.
    case: x y=> [i1|l1|b1] [i2|l2|b2]=> //.
    rewrite -eq_i_eq_iri. by apply /eqP.
    rewrite -eq_l_eq_lit. by apply /eqP.
    rewrite -eq_b_eq_bnode. by apply /eqP.
  Qed.

  Canonical term_eqType := EqType term (EqMixin term_eqP).

  Definition relabeling (μ : B -> B) (t : term) : term :=
    match t with
    | Bnode name => Bnode (μ name)
    | _ => t
    end.

  Lemma relabel_id (t: term) : relabeling id t = t.
  Proof. by case t. Qed.

  Lemma relabel_comp (t: term) (μ1 μ2 : B -> B) : relabeling (μ2 \o μ1) t = (relabeling μ2 \o (relabeling μ1)) t.
  Proof. by case t. Qed.

  Lemma relabel_id_p_I (t : term) (p: is_iri t) : is_iri (relabeling id t).
  Proof. by rewrite relabel_id p. Qed.

  Lemma relabel_id_p_L (t : term) (p: is_lit t) : is_lit (relabeling id t).
  Proof. by rewrite relabel_id p. Qed.

  Lemma relabel_id_p_B (t : term) (p: is_iri t) : is_iri (relabeling id t).
  Proof. by rewrite relabel_id p. Qed.

End Term.
