From RDF Require Import Term.
From Coq Require Import Lists.ListSet.
From Coq Require Import Init.Nat.
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.

Inductive trpl : Type :=
  | triple (s p o : term).

Record tripl_r : Set := mkTrpl
                       { the_triple : trpl
                      }. 


Definition proj_subject (t : trpl) : term :=
  match t with
  | triple s _ _ => s
  end.
Definition proj_predicate (t : trpl) : term :=
  match t with
  | triple _ p _ => p
  end.

Definition proj_object (t : trpl) : term :=
  match t with
  | triple _ _ o => o
  end.

(* alias for triple of terms type *)
(* Definition triple := (node * term * term)%type.  *)

(*
   Inductive rdf : Type :=
  | graph (triples : list triple).
 *)

Definition app_μ_to_triple (μ : term -> term) (t : trpl) : trpl:=
  (match t with
   | (triple n1 n2 n3) => triple (μ n1) n2 (μ n3)
   end).

Definition eqb_triple (t1 t2:trpl) : bool :=
  (match t1,t2 with
   | (triple s p o),(triple s2 p2 o2) => (eqb_term s s2) && (eqb_term p p2) && (eqb_term o o2)
   end).

Theorem eqb_eq_triple: forall (t1 t2 : trpl),
  eqb_triple t1 t2 = true <-> t1 = t2.
Proof. intros. split; intros H.
  - destruct t1,t2 as [s2 p2 o2]; f_equal;
    simpl in H; apply andb_true_iff in H; destruct H as [H0 H2]; apply andb_true_iff in H0; destruct H0 as [H H1]; apply eqb_eq_term. 
    + apply H.
    + apply H1.
    + apply H2.
  - destruct t1,t2 as [s2 p2 o2]. injection H as H1 H2 H3. simpl. rewrite H1. rewrite H2. rewrite H3.
    rewrite (eqb_term_refl s2). rewrite (eqb_term_refl p2). rewrite (eqb_term_refl o2). reflexivity.
Qed.

Theorem eqb_triple_refl : forall (t1: trpl),
  eqb_triple t1 t1 = true.
Proof. intros. destruct t1. simpl. rewrite (eqb_term_refl s). rewrite (eqb_term_refl p). rewrite (eqb_term_refl o). reflexivity.
Qed.

Theorem eqb_neq_triple : forall (t1 t2: trpl),
  eqb_triple t1 t2 = false <-> t1 <> t2.
Proof. intros. split.
  - intros H contra. rewrite contra in H. rewrite eqb_triple_refl in H. discriminate H.
  - intros H. unfold not in H. rewrite <- eqb_eq_triple in H. destruct (eqb_triple t1 t2).
    + exfalso. apply H. reflexivity.
    + reflexivity.
Qed.

Theorem eq_dec_triple : forall (t1 t2: trpl),
  {t1 = t2} + {t1 <> t2}.
Proof. decide equality; try decide equality; try apply string_dec; decide equality. Qed.

(* Notation "t.s" := ( f α) (at level 20, α at next level) : selection_scope. *)
