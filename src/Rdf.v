From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Term.
(* From RDF Require Import Maps. *)
From RDF Require Import Triple.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.ExtensionalityFacts.

(* Inductive existT (P: A -> Prop) : Type := ex : forall x: A, P x -> existT P. *)
Definition Bijective {A B : Type} (f : A->B) :=
  {g : B -> A & cancel f g /\ cancel g f}.

Section rdf.
  Variable I B L: eqType.
  Let term:= (term I B L).
  Let triple:= (triple I B L).

  Record rdf_graph := mkRdfGraph {
                         graph : seq triple
                       ; subject_in_IB : all (fun t => is_in_ib (subject t)) graph
                       ; predicate_in_I : all (fun t => is_in_i (predicate t)) graph
                       ; object_in_IBL : all (fun t => is_in_ibl (object t)) graph
                       }.

  Definition eqb_rdf (g1 g2 : rdf_graph) : bool :=
    (graph g1) == (graph g2).

  Lemma eqb_rdf_refl (g : rdf_graph) : eqb_rdf g g.
  Proof. by rewrite /eqb_rdf. Qed.

  Lemma eqb_rdf_symm (g1 g2 : rdf_graph) : eqb_rdf g1 g2 = eqb_rdf g2 g1.
  Proof. by rewrite /eqb_rdf. Qed.

  Lemma eq_ir : forall (g1 g2: seq triple)
                  (geq : g1 = g2)
                  (p : triple -> bool)
                  (fallt : all p g1),
      all p g2.
  Proof. move=> g1 g2 eqg p fallt. by [rewrite -eqg].
  Qed.

  Lemma graph_inj : forall (g1 g2: rdf_graph),
      eqb_rdf g1 g2 ->
      g1 = g2.
  Proof.
    move=> [g1 sib1 pi1 oibl1] [g2 sib2 pi2 oibl2] /= /eqP /= geq.
    have eqsib: sib2 = (eq_ir geq sib1);
      have eqpi : pi2 = (eq_ir geq pi1);
      have eqoibl: oibl2 = (eq_ir geq oibl1); try apply eq_irrelevance.
    rewrite eqsib eqpi eqoibl. erewrite <-geq. f_equal; apply eq_irrelevance. 
  Qed.
  
  Definition rdf_eqP : Equality.axiom eqb_rdf.
  Proof. rewrite /Equality.axiom => x y.
         apply: (iffP idP) => //= [| ->]; case: x y=> [g1 sib1 pi1 oibl1] [g2 sib2 pi2 oibl2]. apply graph_inj. apply eqb_rdf_refl. 
  Qed.

  Definition relabelingG (μ : B -> B) (g : seq triple) : seq triple :=
    map (relabeling μ) g.

  Lemma relabelingG_id (g : seq triple) : relabelingG id g = g.
  Proof. rewrite /relabelingG. apply /eqP. elim g => [//|h t /eqP iht] /=. rewrite relabeling_id. by rewrite iht. Qed.

  Lemma inv_bij {T U : Type} (f : T -> U) (bij: bijective f) :
    (exists g: U->T, exists f:T->U, (forall x, g (f x) = x) /\ (forall y, f (g y) = y)).
  Proof.
    case: bij=> g cL cR. exists g. exists f. split. apply cL. apply cR. Qed.

  Definition inv {T U : Type} (f : T->U) (bij: Bijective f) : (U->T).
  Proof. destruct bij. apply x. Defined.

  Lemma relabelingG_comp_simpl (g : seq triple) (μ12 μ23 : B -> B) :
    relabelingG (μ23 \o μ12) g = (relabelingG μ23 \o (relabelingG μ12)) g.
  Proof. rewrite /relabelingG /=. elim g => [//|h t iht] /=. rewrite relabeling_comp /=. f_equal; apply iht.
  Qed.

  Lemma relabeling_comp_P (g1 g2 : seq triple) (eqb : g1 = g2) (μ : B->B) :
    relabelingG μ g1 = relabelingG μ g2. by rewrite eqb. Qed.

  Lemma relabelingG_comp (μ1 μ2 : B -> B) (g : seq triple) : relabelingG μ1 (relabelingG μ2 g) = (relabelingG μ1 \o (relabelingG μ2)) g.
    Proof. by []. Qed. 
  (* move to relabel? *)
  Lemma relabelingG_bij (g1 g2: seq triple) (μ : B->B) (bij: Bijective μ) (eqb : g1 = (relabelingG μ g2)) : relabelingG (inv bij) g1 = g2.
  Proof. case bij=> μ1 [cL cR]. rewrite /inv /=. rewrite eqb.
         rewrite relabelingG_comp_simpl -relabelingG_comp.
         elim g2=> [//| h t IHt] /=. rewrite IHt. f_equal. case h=> s p o sin pin oin. rewrite /relabeling /Term.relabeling /=. apply triple_inj;
           rewrite /=; case s; case p; case o => s1 p1 o1 ;repeat try by []; repeat try by rewrite cL. Qed.

  Lemma relabelingG_preserves_subject_in_IB (g : seq triple) (μ : B -> B) :
    all (fun t => is_in_ib (subject t)) g ->
    all (fun t => is_in_ib (subject t)) (relabelingG μ g).
  Proof. move=> /allP sin. apply /allP => [[s p o /= sint pint oint]] => tg. apply sint. 
  Qed.

  Lemma relabelingG_preserves_predicate_in_I (g : seq triple) (μ : B -> B) :
    all (fun t => is_in_i (predicate t)) g ->
    all (fun t => is_in_i (predicate t)) (relabelingG μ g).
  Proof. move=> /allP pin. apply /allP => [[s p o /= sint pint oint]] => tg . apply pint.
  Qed.

  Lemma relabelingG_preserves_object_in_IBL (g : seq triple) (μ : B -> B) :
    all (fun t => is_in_ibl (object t)) g ->
    all (fun t => is_in_ibl (object t)) (relabelingG μ g).
  Proof. move=> /allP oin. apply /allP => [[s p o /= sibt pibt oint]] => tg . apply oint.
  Qed.

  Definition relabeling (μ : B -> B) (g : rdf_graph): rdf_graph :=
    let (g',siib,pii,oiibl) := g in
    {|
      graph := relabelingG μ g';
      subject_in_IB :=  relabelingG_preserves_subject_in_IB μ siib;
      predicate_in_I := relabelingG_preserves_predicate_in_I μ pii;
      object_in_IBL := relabelingG_preserves_object_in_IBL μ oiibl
    |}.

  Lemma relabeling_id (g : rdf_graph) : relabeling id g = g.
  Proof. apply graph_inj. case g=> g' sin pin oin. rewrite /relabeling /= /eqP /eqb_rdf /=. by rewrite /eqP relabelingG_id.
  Qed.

  Lemma relabeling_comp (g : rdf_graph) (μ12 μ23: B -> B) :
    (relabeling μ23 \o (relabeling μ12)) g = relabeling (μ23 \o μ12) g.
  Proof. apply graph_inj. rewrite /eqb_rdf. apply /eqP.
         case g=> g' sin pin oin /=. by rewrite relabelingG_comp_simpl.
  Qed.

  Definition is_iso (g1 g2 : rdf_graph) (μ : B -> B) :=
    (bijective μ) /\ eqb_rdf g1 (relabeling μ g2).

  Definition iso (g1 g2 : rdf_graph):= exists (μ : B -> B),
      is_iso g1 g2 μ.


  Lemma iso_refl (g : rdf_graph) : iso g g.
  Proof. rewrite /iso /is_iso; exists id; split.
         exists id => //.
         by rewrite relabeling_id eqb_rdf_refl.
  Qed.

  (* Definition inv (bij : Type) : bijective : bijective f := *)

  (*    Inductive ubn_geq_spec m : nat -> Type := *)
  (*   UbnGeq n of n <= m : ubn_geq_spec m n. *)
  (* Lemma ubnPgeq m : ubn_geq_spec m m. *)
  (* Proof. by []. Qed. *)

  Lemma relabeling_comp_simpl (μ1 μ2 : B -> B) (g : rdf_graph) : relabeling μ1 (relabeling μ2 g) = relabeling (μ1 \o μ2) g.
    Proof. by rewrite -relabeling_comp. Qed.

    Lemma iso_symm (g1 g2 : rdf_graph) :
      iso g1 g2 <-> iso g2 g1.
    Proof. rewrite /iso /is_iso.
           split=>
                  [[μ [[μ1 cL cR] eqb]] | [μ [[μ1 cL cR] eqb]]]; 
                  have bij: bijective μ; exists μ1; try apply cL; try apply cR;
                  split; try (exists μ; try apply cR; try apply cL);
                  rewrite eqb_rdf_symm; apply graph_inj in eqb; subst; rewrite relabeling_comp_simpl;
                  apply /eqP;
                  try (case g2=> [ gs1 _ _ _ ] /=); try (case g1=> [gs1 _ _ _] /=);
                  elim gs1=> [ // | h t IHt] /=; rewrite IHt; f_equal; case h=> s p o sin pin oin; apply triple_inj; rewrite /=;
                  case s=> id /=; case p=> pred; case o=> obj /=; try by []; try by rewrite cL.
    Qed.

  Lemma iso_trans (g1 g2 g3: rdf_graph) : iso g1 g2 -> iso g2 g3 -> iso g1 g3.
  Proof. rewrite /iso /is_iso=> [[μ1 [bij1 /graph_inj eqb1]] [μ2 [bij2 /graph_inj eqb2]]].
         exists (μ1 \o μ2). split. 
         rewrite /=. apply bij_comp. apply bij1. apply bij2.
         rewrite -relabeling_comp /= -eqb2 -eqb1. by apply eqb_rdf_refl.
 Qed.

End rdf.

