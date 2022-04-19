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

(* Theorem eq_nat_in_set : forall (n1 n2:nat) (p: n1 = n2), (set_In n1 L) -> set_In n2 L. *)
(* Proof. intros. symmetry in p. rewrite p. apply H. *)
(* Qed. *)

(* Theorem eq_nat_eq_in_set : forall (n1 n2:nat) (H: n1 = n2), set_In n1 L = set_In n2 L. *)
(* Proof. intros. rewrite H. reflexivity. Qed. *)

(* Theorem eq_p_eq_in_set : forall (n : nat) (p1 : set_In n L) (p2 : set_In n L), p1 = p2. *)
(*   Proof. intros. revert n p1 p2. induction L ; cbn. intros _ []. *)

(* Theorem eq_nat_eq_lit : forall (n1 n2:nat), *)
(*     (n1 = n2) <-> (@Lit n1 (set_mem Nat.eq_dec) n1 L) = (@Lit n2 (set_mem Nat.eq_dec n2 L)). *)
(* Proof. split; intros H. *)
(*   - rewrite H. reflexivity. *)
(*   - injection H as H2. apply H2. *)
(* Qed. *)

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

(* Theorem eq_dec_term : forall (t1 t2: term), *)
(*   {t1 = t2} + {t1 <> t2}. *)
(* Proof. decide equality. *)
(*        - apply eqVneq. *)

(*   (try decide equality); (try apply string_dec); (try decide equality). Qed. *)

(* Theorem eqb_term_refl : forall (t1 : term), *)
(*   eqb_term t1 t1 = true. *)
(* Proof. destruct t1 as []; simpl. *)
(*   - apply eqb_refl. *)
(*   - symmetry. apply beq_nat_refl. *)
(*   - apply eqb_refl. *)
(* Qed. *)

(* Definition term_eqType : eqType := @Equality.Pack term eqb_term. *)

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

(* Theorem eqb_eq_term : forall (t1 t2 : term), *)
(*   eqb_term t1 t2 <-> t1 = t2. *)
(* Proof. split; intros H. *)
(*   - destruct t1,t2 as [] ;  *)
(*     try reflexivity ; *)
(*     try discriminate; simpl in H. *)
(*     + apply eq_i_eq_iri. apply H. apply eqb_eq in H. rewrite H. reflexivity. apply eq_string_eq_iri. reflexivity. *)
(*     + apply beq_nat_true in H. rewrite H. apply eq_nat_eq_lit. reflexivity. *)
(*     + apply eqb_eq in H. apply eq_string_eq_bnode. apply H. *)
(*   - rewrite H. apply eqb_term_refl. *)
(* Qed. *)


(* Theorem eqb_neq_term : forall (t1 t2 : term), *)
(*   eqb_term t1 t2 = false <-> t1 <> t2. *)
(* Proof. split. *)
(*   - intros H contra. rewrite contra in H. rewrite eqb_term_refl in H. discriminate H. *)
(*   - intros H. unfold not in H. rewrite <- eqb_eq_term in H. destruct (eqb_term t1 t2) as []. *)
(*     + exfalso. apply H. reflexivity. *)
(*     + reflexivity. *)
(* Qed. *)

End Term.
