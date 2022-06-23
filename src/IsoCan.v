From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term.

Section IsoCan.
  Variable I B L: countType.

  (*   Definition isocanonical_function (M : B -> B) (g : rdf_graph_) :=
    iso g (Rdf.relabeling M g) /\
      forall (h : rdf_graph_), iso g h <-> (relabeling M g) = (relabeling M h). *)

  Section IsoCanAlgorithm.
    Variable h : countType.
    Variables h0 hfwd hbwd hmark : h.
    Definition hash_eqMixin := PcanEqMixin (@pickleK h).
    Definition hash_canChoiceMixin := PcanChoiceMixin (@pickleK h).
    Definition hash_canCountMixin := PcanCountMixin (@pickleK h).

    Canonical hash_eqType := Eval hnf in EqType h hash_eqMixin.
    Canonical hash_choiceType := Eval hnf in ChoiceType h hash_canChoiceMixin.
    Canonical hash_countType := Eval hnf in CountType h hash_canCountMixin.

    Definition hash_canPOrderMixin := PcanPOrderMixin (@pickleK hash_countType).
    Canonical hash_POrderType := Eval hnf in POrderType tt h hash_canPOrderMixin.
    Variable hashTerm : @term I B L -> h.
    Section Hash.

      Record hi_term (T : Type) := mkHinput {
                                      input : T ;
                                      current_hash : h
                                    }.

      Hypothesis perfectHashingSchemeTerm : injective hashTerm.

      Lemma by_perf_hash (i : @term I B L) (o : h) (eqb : hashTerm i == o) : hashTerm i = o.
      Proof. apply /eqP. apply eqb. Qed.

      Variable T : countType.
      Definition code_hash (x : hi_term T) : GenTree.tree nat :=
        let (i,o) := x in
        GenTree.Node 0 [:: GenTree.Leaf (pickle i); GenTree.Leaf (pickle o)].

      Definition decode_hash (x : GenTree.tree nat) : option (hi_term T) :=
        match x with
        | GenTree.Node 0 [:: GenTree.Leaf n; GenTree.Leaf m] =>
            match (@unpickle T n, @unpickle hash_countType m) with
            | (Some i, Some o) => Some (mkHinput i o)
            | (_, _) => None
            end
        | _ => None
        end.

      Definition cancel_hin_encode : pcancel code_hash decode_hash.
      Proof. case => i o; by rewrite /code_hash /decode_hash !pickleK. Qed.

      Definition hin_eqMixin := PcanEqMixin cancel_hin_encode.
      Definition hin_canChoiceMixin := PcanChoiceMixin cancel_hin_encode.
      Definition hin_canCountMixin := PcanCountMixin cancel_hin_encode.

      Canonical hin_eqType := Eval hnf in EqType (hi_term T) hin_eqMixin.
      Canonical hin_choiceType := Eval hnf in ChoiceType (hi_term T) hin_canChoiceMixin.
      Canonical hin_ct := Eval hnf in CountType (hi_term T) hin_canCountMixin.
      Definition hin_canPOrderMixin := PcanPOrderMixin (@pickleK hin_ct).
      Canonical hin_POrderType := Eval hnf in POrderType tt (hi_term T) hin_canPOrderMixin.

      Definition hash := hi_term.
    End Hash.
    Definition hash_term := @term I (hash B) L.

    Let is_bnode := (@is_bnode I (hash B) L).

    Definition eqb_t_hi (t : @term I B L) (ht : hash_term) : bool :=
      match t, ht with
      | Iri i, Iri i' => i == i'
      | Bnode b,Bnode hin => b == (input hin)
      | Lit l, Lit l' => l == l'
      | _,_ => false
      end.

    Section typeRelabel.
      Variable T : countType.

      Definition app_term (t : @term I B L) (f : B -> T) : @term I T L :=
        match t with
        | Bnode b => Bnode (f b)
        | Iri i => Iri i
        | Lit l => Lit l
        end.

      Definition app_p_sib (s : @term I B L) (f : B -> T) : (is_in_ib s) -> (is_in_ib (app_term s f)).
      Proof. rewrite /app_term; by case s. Qed.

      Definition app_p_pii (p : @term I B L) (f : B -> T) : (is_in_i p) -> (is_in_i (app_term p f)).
      Proof. rewrite /app_term; by case p. Qed.

      Definition app_p_ibl (o : @term I B L) (f : B -> T) : (is_in_ibl o) -> (is_in_ibl (app_term o f)).
      Proof. rewrite /app_term; by case o. Qed.

      Definition MoveTriple (f : B -> T) (t : @triple I B L) : @triple I T L :=
        let (s,p,o,sin,pin,oin) := t in
        {| subject := app_term s f ;
          predicate := app_term p f ;
          object := app_term o f ;
          subject_in_IB:= app_p_sib f sin ; 
          predicate_in_I:= app_p_pii f pin ;
          object_in_IBL:= app_p_ibl f oin ;
        |}.

      Definition map_graph (g : seq (@triple _ B _)) (f : B -> T): seq (@triple I T L) :=
        map (MoveTriple f) g.

      Lemma app_st_p_sin (g : seq (@triple _ B _) ) (f : B -> T) :
        all (fun t => is_in_ib (subject t)) g ->
        all (fun t => is_in_ib (subject t)) (map_graph g f).
      Proof. move=> /allP sin; apply /allP => [[s p o /= sint pint oint]] => tg; by apply sint. 
      Qed.

      Lemma app_st_p_pin (g : seq (@triple I B L)) (μ : B -> T) :
        all (fun t => is_in_i (predicate t)) g ->
        all (fun t => is_in_i (predicate t)) (map_graph g μ).
      Proof. move=> /allP pin; apply /allP => [[s p o /= sint pint oint]] => tg; by apply pint.
      Qed.

      Lemma app_st_p_oin (g : seq (@triple I B L)) (μ : B -> T) :
        all (fun t => is_in_ibl (object t)) g ->
        all (fun t => is_in_ibl (object t)) (map_graph g μ).
      Proof. move=> /allP oin; apply /allP => [[s p o /= sibt pibt oint]] => tg; by apply oint.
      Qed.

      Definition graph_map (f : B -> T) (g : rdf_graph): @rdf_graph I T L:=
        let (g',sin,pin,oin) := g in
        mkRdfGraph (app_st_p_sin f sin)(app_st_p_pin f pin) (app_st_p_oin f oin).

    End typeRelabel.
    Definition hash_triple := @triple I (hash B) L.

    Definition get_triple (t : @term I B L) (trpl : hash_triple) : option hash_term :=
      let (s,p,o,_,_,_) := trpl in
      if eqb_t_hi t s then Some s
      else if eqb_t_hi t p then Some p
           else if eqb_t_hi t o then Some o
                else None.
    
    Definition is_some {T : Type} (ot : option T) : bool := 
      match ot with Some _ => true | None => false end.

    Definition hash_graph := @rdf_graph I (hash B) L.

    Definition get (t : @term I B L) (g : hash_graph) : option hash_term :=
      let otrs := (map (get_triple t) (graph g)) in
      head None (filter is_some otrs).

    (*     Definition lookup_hash (g : rdf_graph I (hash B) L) (b : term I B L): option (hash B) :=
      let ot := get b g in
      match ot with 
      | Some (Bnode hin) => Some hin
      | _ => None
      end. *)

    Definition lookup_hash (b : hash_term): option (hash B) :=
      match b with 
      | Bnode hin => Some hin
      | _ => None
      end.


    Section Partition.

      (*     Definition eq_rel (g : rdf_graph I (hash B) L) (b1 b2 : term I B L ) : bool :=
      match (lookup_hash b1), (lookup_hash b2) with
      | Some hin1, Some hin2 => current_hash hin1 == current_hash hin2
      | _,_ => false
      end. *)

      Definition eq_rel (b1 b2 : hash_term) : bool :=
        match (lookup_hash b1), (lookup_hash b2) with
        | Some hin1, Some hin2 => current_hash hin1 == current_hash hin2
        | _,_ => false
        end.

      Fixpoint partitionate (f : hash_term -> bool) (s:seq hash_term) : seq hash_term * seq hash_term :=
        match s with
        | nil => (nil, nil)
        | x :: tl => let (g,d) := partitionate f tl in
                   if f x then (x::g,d) else (g,x::d)
        end.

      Definition part := seq (hash B).
      Definition partition := seq part.

      Fixpoint unwrap {T : Type} (os : seq (option T)) : seq T :=
        match os with
        | nil => nil
        | Some t :: oss => t :: unwrap oss
        | None :: oss => unwrap oss
        end.

      Definition mkPartition (g : hash_graph) : partition :=
        let bns := (bnodes g) in
        let equiv := (fun b => (fun t=> eq_rel b t)) in
        let P := undup (map (fun b=> (partitionate (equiv b) bns).1 ) bns) in
        let ohs := map (fun bs => map lookup_hash bs) P in
        map unwrap ohs.

      Record Partition := mkPartition_ {
                             P : partition ;
                             g : hash_graph ;
                             p_wf : P == mkPartition g  ;
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



    Definition init_bnode (b : B) : (hash B) :=
      mkHinput b h0.

    Definition init_hash (g : rdf_graph) : hash_graph :=
      graph_map init_bnode g.

    Definition cmp_part (p1 p2 : part) : bool :=
      all2 (fun b1 b2 => input b1 == input b2) p1 p2.

    Definition partition_didnt_change (g h: hash_graph) : bool :=
      let pg := mkPartition g in 
      let ph := mkPartition h in
      all2 (fun p1 p2 => cmp_part p1 p2) pg ph.

    Variable update_bnodes : hash_graph -> hash_graph.

    Fixpoint iterate (g : hash_graph) (fuel : nat) : hash_graph :=
      match fuel with
      | O => g
      | S n' =>
          let h := update_bnodes g in
          if partition_didnt_change g h then h else
            iterate h n'
      end.

    Definition hashNodes (g : rdf_graph) : hash_graph :=
      let ini := init_hash g in
      iterate ini (size (graph g)).
    


    (*   Definition cmp_bnode (b : B) (t : hash_term) : bool :=
    match t with
    | Bnode hin => b == hin
    | _ => false
    end. *)
    Definition lookup_bnode_in_triple (t : hash_triple) (b : B) : hash_term :=
      let (s,p,o,_,_,_) := t in 
      let is_b := (fun t : hash_term => match t with
                                     | Bnode hin => b == (input hin)
                                     | _ => false
                                     end) in
      if is_b s then s 
      else if is_b p then p
           else o.
    
    (* Definition lookup_bnode (b : B) (g : hash_graph) : option h := *)
    (*   filter (fun t => match t with *)
    (*                    | Bnode hin => b == hin *)
    (*                    | _ => false *)
    (*                    end) (graph g). *)

    (* Lemma hash_dont_get_equal (g : hash_graph) (b1 b2: B) : True. *)
    
    
    (* { hash_term | is_true is_bnode }) : forall n, n+1. *)
    
    (* () *)
    (*     forall (g : rdf_graph) (hms : seq hashmap) *)
    (*            (ghashh : hashNodes g = hms) *)
    (*            (i j : nat) (ileqj : i <= j) (lim : j < size hms) *)
    (*            (x y : term) (bnx : is_bnode x) (bny : is_bnode y) *)
    (*            (xing : x \in (terms g)) (ying : y \in (terms g)), *)
    (*       (lookup_hashmap (nth [::] hms i) x != lookup_hashmap (nth [::] hms i) y) *)
    (*       -> lookup_hashmap (nth [::] hms j) x != lookup_hashmap (nth [::] hms j) y. *)

    (* 
    Hypothesis hashNodes_preserves_isomorphism :
      forall (g h: rdf_graph) (isogh : iso g h)
             (hash_g hash_h: hashmap)
             (hashg_hm : hash_g = last [::] (hashNodes g))
             (hashh_hm : hash_h = last [::] (hashNodes h))
             (b : term) (bing : b \in (bnodes (g)))
             (c : term) (cinh : c \in (bnodes (h))),
      exists μ, (relabeling_term μ b) = c -> lookup_hashmap hash_g b = lookup_hashmap hash_h c. *)
    
    (* Hypothesis perfectHashingSchemeTriple : injective hashTriple. *)

    Variable hashBag : (seq (hash B) -> (hash B)).
    Hypothesis hashBag_assoc : forall (l l1 l2 l3: seq (hash B)) (perm : l = l1 ++ l2 ++ l3),
        hashBag ([:: hashBag (l1 ++ l2)] ++ l3) = hashBag (l1 ++ [:: hashBag (l2 ++ l3)]).
    Hypothesis hashBag_comm : forall (l l1 l2: seq (hash B)) (perm : l = l1 ++ l2),
        hashBag l = hashBag (l2 ++ l1).

  End IsoCanAlgorithm.
  (* Hypothesis rdf_total_order   *)

End IsoCan.

