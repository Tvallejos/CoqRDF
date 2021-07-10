From Coq Require Import Strings.String.
From Coq Require Import Lists.ListSet.
From Coq Require Import Bool.Bool.
From RDF Require Import Node.

Inductive trpl : Type :=
  | triple (s p o : node).

Check (triple (Null) (Const 1) (Var "foo")): trpl.

Definition app_μ_to_triple (μ : node -> node) (t : trpl) : trpl:=
  (match t with
   | (triple n1 n2 n3) => triple (μ n1) n2 (μ n3)
   end).


Check set_In.
Check (set_add eq_dec_node (Var "x") (set_add eq_dec_node (Const 5) (empty_set node))).
Example example_in_set_of_node : set_In (Const 12) (set_add eq_dec_node (Const 12) (set_add eq_dec_node (Const 5) (empty_set node))).
Proof. simpl. destruct (eq_dec_node (Const 12) (Const 5)) eqn:E.
  - simpl. left. symmetry. apply e.
  - simpl. right. left. reflexivity.
Qed.

Definition eqb_triple (t1 t2:trpl) : bool :=
  (match t1,t2 with
   | (triple s p o),(triple s2 p2 o2) => (eqb_node s s2) && (eqb_node p p2) && (eqb_node o o2)
   end).

Theorem eqb_eq_triple: forall (t1 t2 : trpl),
  eqb_triple t1 t2 = true <-> t1 = t2.
Proof. intros. split.
  - intros H. destruct t1,t2 as [s2 p2 o2]; f_equal;
    simpl in H; apply andb_true_iff in H; destruct H as [H0 H2]; apply andb_true_iff in H0; destruct H0 as [H H1]; apply eqb_eq_node. 
    + apply H.
    + apply H1.
    + apply H2.
  - intros H. destruct t1,t2 as [s2 p2 o2]. injection H as H1 H2 H3. simpl. rewrite H1. rewrite H2. rewrite H3.
    rewrite <- (eqb_node_refl s2). rewrite <- (eqb_node_refl p2). rewrite <- (eqb_node_refl o2). reflexivity.
Qed.

Theorem eqb_triple_refl : forall (t1: trpl),
  eqb_triple t1 t1 = true.
Proof. intros. destruct t1. simpl. rewrite <- (eqb_node_refl s). rewrite <- (eqb_node_refl p). rewrite <- (eqb_node_refl o). reflexivity.
Qed.

Theorem eqb_neq_triple : forall (t1 t2: trpl),
  eqb_triple t1 t2 = false <-> t1 <> t2.
Proof. intros. split.
  - intros H contra. rewrite contra in H. rewrite eqb_triple_refl in H. discriminate H.
  - intros H. unfold not in H. rewrite <- eqb_eq_triple in H. destruct (eqb_triple t1 t2).
    + exfalso. apply H. reflexivity.
    + reflexivity.
Qed.

(* POC: this WILL be refactored *)
Theorem eq_dec_triple : forall (t1 t2: trpl),
  {t1 = t2} + {t1 <> t2}.
Proof. intros t1 t2. destruct t1, t2. destruct (eq_dec_node s s0,eq_dec_node p p0,eq_dec_node o o0) as [[[H|H] [H2|H2]] [H3|H3]] eqn:E.
- try (left; try f_equal;
      try apply H;
      try apply H2;
      try apply H3).
- (try (right; 
      try rewrite <- eqb_neq_triple; simpl;
      try rewrite H;
      try rewrite H2;
      try rewrite H3;
      try rewrite <- (eqb_node_refl s0);
      try rewrite <- (eqb_node_refl p0);
      try rewrite <- (eqb_node_refl o0));
    try reflexivity;
    try simpl; 
    rewrite eqb_neq_node;
      try apply H;
      try apply H2;
      try apply H3).
- try right. 
  try rewrite <- eqb_neq_triple. simpl.
      try rewrite H.
      try rewrite H2.
      try rewrite H3.
      try rewrite <- (eqb_node_refl s0).
      try rewrite <- (eqb_node_refl p0).
      try rewrite <- (eqb_node_refl o0).
    try reflexivity.
    try simpl.
    try (rewrite andb_comm;simpl).
    rewrite eqb_neq_node;
      try apply H;
      try apply H2;
      try apply H3.
- try right. 
  try rewrite <- eqb_neq_triple. simpl.
      try rewrite H.
      try rewrite H2.
      try rewrite H3.
      try rewrite <- (eqb_node_refl s0).
      try rewrite <- (eqb_node_refl p0).
      try rewrite <- (eqb_node_refl o0).
    try reflexivity.
    try simpl.
    try (rewrite andb_comm;simpl). 
    apply andb_false_iff. left.
    rewrite eqb_neq_node;
      try apply H;
      try apply H2;
      try apply H3.
- try right. 
  try rewrite <- eqb_neq_triple. simpl.
      try rewrite H.
      try rewrite H2.
      try rewrite H3.
      try rewrite <- (eqb_node_refl s0).
      try rewrite <- (eqb_node_refl p0).
      try rewrite <- (eqb_node_refl o0).
    try reflexivity.
    try simpl.
    try (rewrite andb_comm;simpl).
    apply andb_false_iff. left.
    rewrite eqb_neq_node;
      try apply H;
      try apply H2;
      try apply H3.
- try right. 
  try rewrite <- eqb_neq_triple. simpl.
      try rewrite H.
      try rewrite H2.
      try rewrite H3.
      try rewrite <- (eqb_node_refl s0).
      try rewrite <- (eqb_node_refl p0).
      try rewrite <- (eqb_node_refl o0).
    try reflexivity.
    try simpl.
    try (rewrite andb_comm;simpl).
    apply andb_false_iff. left.
    rewrite eqb_neq_node;
      try apply H;
      try apply H2;
      try apply H3.
- try right. 
  try rewrite <- eqb_neq_triple. simpl.
      try rewrite H.
      try rewrite H2.
      try rewrite H3.
      try rewrite <- (eqb_node_refl s0).
      try rewrite <- (eqb_node_refl p0).
      try rewrite <- (eqb_node_refl o0).
    try reflexivity.
    try simpl.
    try (rewrite andb_comm;simpl).
    apply andb_false_iff. left.
    rewrite eqb_neq_node;
      try apply H;
      try apply H2;
      try apply H3.
- try right. 
  try rewrite <- eqb_neq_triple. simpl.
      try rewrite H.
      try rewrite H2.
      try rewrite H3.
      try rewrite <- (eqb_node_refl s0).
      try rewrite <- (eqb_node_refl p0).
      try rewrite <- (eqb_node_refl o0).
    try reflexivity.
    try simpl.
    try (rewrite andb_comm;simpl).
    apply andb_false_iff. left.
    rewrite eqb_neq_node;
      try apply H;
      try apply H2;
      try apply H3.
Qed.

