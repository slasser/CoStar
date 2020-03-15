Require Import FMaps List MSets Program.Wf.
Require Import GallStar.Lex.
Require Import GallStar.Prediction_complete.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

Module SllPredictionFn (Import D : Defs.T).

  Module Export PC := PredictionCompleteFn D.

  Module SLL.

    (* First, some static analysis over a grammar *)
    Inductive pos : Type :=
    | Pos : option nonterminal -> list symbol -> pos.

    Definition sll_stack := (pos * list pos)%type.

    Lemma pos_eq_dec :
      forall p p' : pos, {p = p'} + {p <> p'}.
    Proof.
      repeat decide equality; try apply t_eq_dec; try apply nt_eq_dec.
    Qed.

    Module MDT_Pos.
      Definition t := pos.
      Definition eq_dec := pos_eq_dec.
    End MDT_Pos.
    Module Pos_as_DT   := Make_UDT(MDT_Pos).
    Module Pset  := MSetWeakList.Make Pos_as_DT.
    Module PsetF := WFactsOn Pos_as_DT Pset.
    Module Pmap  := FMapWeakList.Make Pos_as_DT.

    Definition edge := (pos * pos)%type.

    Definition src (e : edge) : pos := fst e.

    Definition dst (e : edge) : pos := snd e.

    Lemma edge_eq_dec :
      forall e e' : edge, {e = e'} + {e <> e'}.
    Proof.
      repeat decide equality; try apply t_eq_dec; try apply nt_eq_dec.
    Qed.

    Module MDT_Edge.
      Definition t := edge.
      Definition eq_dec := edge_eq_dec.
    End MDT_Edge.
    Module Edge_as_DT   := Make_UDT(MDT_Edge).
    Module E  := MSetWeakList.Make Edge_as_DT.
    Module EF := WFactsOn Edge_as_DT E.

    Definition oneToMany {A B : Type} (s : A) (ds : list B) : list (A * B) :=
      map (pair s) ds.

    Definition beqNt x x' : bool :=
      match nt_eq_dec x' x with
      | left _ => true
      | right _ => false
      end.

    Fixpoint prodsOf (x : nonterminal) (ps : list production) := 
      filter (fun p => beqNt x (lhs p)) ps.

    Fixpoint pushEdges' (g : grammar) (x : nonterminal) (ys : list symbol) : list edge :=
      match ys with 
      | []          => []
      | T _ :: ys'  => pushEdges' g x ys'
      | NT y :: ys' =>
        let es := map (fun rhs => (Pos (Some x) ys, Pos (Some y) rhs))
                      (rhssForNt g y)
        in  es ++ pushEdges' g x ys'
      end.

    Definition pushEdges (g : grammar) : list edge :=
      flat_map (fun p => pushEdges' g (lhs p) (rhs p)) g.

    Fixpoint returnEdges' (x : nonterminal) (ys : list symbol) : list edge :=
      match ys with
      | []          => []
      | T _ :: ys'  => returnEdges' x ys'
      | NT y :: ys' =>
        (Pos (Some y) [], Pos (Some x) ys') :: returnEdges' x ys'
      end.

    Definition returnEdges (g : grammar) : list edge :=
      flat_map (fun p => returnEdges' (lhs p) (rhs p)) g.

    Definition finalEdges g : list edge :=
      map (fun x => (Pos (Some x) [], Pos None [])) (lhss g).

    Definition fromEdgelist (es : list edge) : E.t :=
      fold_right E.add E.empty es.

    Definition epsilonEdges g : list edge :=
      pushEdges g ++ returnEdges g ++ finalEdges g.

    Fixpoint dsts (es : list edge) (s : pos) : list pos :=
      match es with
      | []             => []
      | (s', d) :: es' =>
        if pos_eq_dec s' s then d :: dsts es' s else dsts es' s
      end.

    Definition mem (e : edge) (es : list edge) : bool :=
      if in_dec edge_eq_dec e es then true else false.

    Definition newEdges' (es : list edge) (e : edge) : list edge :=
      let (a, b) := e in
      let cs     := filter (fun c => negb (mem (a, c) es)) (dsts es b)
      in  oneToMany a cs.

    Definition newEdges (es : list edge) : list edge :=
      flat_map (newEdges' es) es.

    Definition sources es := map src es.
    Definition dests   es := map dst es.

    Definition allEdges es := 
      let ss := sources es in
      let ds := dests   es in
      flat_map (fun s => oneToMany s ds) ss.

    Definition stable (p : pos) : bool :=
      match p with
      | Pos None []             => true
      | Pos (Some x) (T _ :: _) => true
      | _                       => false
      end.

    Fixpoint stablePositions' x ys : list pos :=
      match ys with
      | []          => []
      | T a :: ys'  => Pos (Some x) ys :: stablePositions' x ys'
      | NT _ :: ys' => stablePositions' x ys'
      end.

    Definition stablePositions (g : grammar) : list pos :=
      Pos None [] :: flat_map (fun p => stablePositions' (lhs p) (rhs p)) g.

    Definition reflEdges (g : grammar) : list edge :=
      map (fun p => (p, p)) (stablePositions g).

    Definition m (es : list edge) : nat :=
      E.cardinal (E.diff (fromEdgelist (allEdges es)) (fromEdgelist es)).

    Axiom magic : forall A, A.

    Program Fixpoint transClosure (es : list edge)
            { measure (m es) } : list edge :=
      let es' := newEdges es in
      match es' as es'' return es' = es'' -> _ with
      | []     => fun _   => es
      | _ :: _ => fun heq => transClosure (es' ++ es)
      end eq_refl.
    Next Obligation.
      rewrite heq; simpl.
      unfold m.
      apply magic.
    Defined.

    Definition destStable (e : edge) : bool :=
      let (_, b) := e in stable b.

    Definition stableEdges (es : list edge) : list edge :=
      filter destStable es.

    Definition mkGraphEdges (g : grammar) : list edge :=
      stableEdges (transClosure (epsilonEdges g)) ++ (reflEdges g).

    (* A closure graph is a map where each key K is a grammar position
     and each value V is a set of positions that are epsilon-reachable from K *)
    Definition closure_map := Pmap.t Pset.t.

    Definition addEdge (e : edge) (m : closure_map) : closure_map :=
      let (k, v) := e in
      match Pmap.find k m with
      | Some vs => Pmap.add k (Pset.add v vs) m
      | None    => Pmap.add k (Pset.singleton v) m
      end.

    Definition fromEdges (es : list edge) : closure_map :=
      fold_right addEdge (Pmap.empty Pset.t) es.

    Definition mkGraph (g : grammar) : closure_map :=
      fromEdges (mkGraphEdges g).

    Definition callSites (p : pos) (cm : closure_map) : list sll_stack :=
      match Pmap.find p cm with
      | Some ps => map (fun p' => (p', [])) (Pset.elements ps)
      | None    => []
      end.

    (* Now for the parts that correspond to the LL prediction module *)
    
    Record subparser := Sp { prediction : list symbol
                             ; stack      : sll_stack }.

    (* "move" operation *)

    Inductive subparser_move_result :=
    | SpMoveSucc   : subparser -> subparser_move_result
    | SpMoveReject : subparser_move_result
    | SpMoveError  : prediction_error -> subparser_move_result.

    Definition moveSp (tok : token) (sp : subparser) : subparser_move_result :=
      match sp with
      | Sp pred stk =>
        match stk with
        | (Pos _ [], [])            => SpMoveReject
        | (Pos _ [], _ :: _)        => SpMoveError SpInvalidState
        | (Pos _ (NT _ :: _), _)    => SpMoveError SpInvalidState
        | (Pos o (T a :: suf), frs) =>
          match tok with
          | (a', _) =>
            if t_eq_dec a' a then
              SpMoveSucc (Sp pred (Pos o suf, frs))
            else
              SpMoveReject
          end
        end
      end.

    Definition move_result := sum prediction_error (list subparser).

    Fixpoint aggrMoveResults (rs : list subparser_move_result) : move_result :=
      match rs with
      | []       => inr []
      | r :: rs' =>
        match (r, aggrMoveResults rs') with
        | (SpMoveError e, _)       => inl e
        | (_, inl e)               => inl e
        | (SpMoveSucc sp, inr sps) => inr (sp :: sps)
        | (SpMoveReject, inr sps)  => inr sps
        end
      end.

    Definition move (tok : token) (sps : list subparser) : move_result :=
      aggrMoveResults (map (moveSp tok) sps).

    (* "closure" operation *)

    Inductive subparser_closure_step_result :=
    | SpClosureStepDone  : list subparser -> subparser_closure_step_result
    | SpClosureStepK     : NtSet.t -> list subparser -> subparser_closure_step_result
    | SpClosureStepError : prediction_error -> subparser_closure_step_result.

    Definition spClosureStep (g : grammar) (cm : closure_map) (av : NtSet.t) (sp : subparser) : 
      subparser_closure_step_result :=
      match sp with
      | Sp pred (fr, frs) =>
        match fr with
        | Pos o [] =>
          match frs with
          | []                 =>
            (* SLL-specific part -- simulate a return to all call sites *)
            match o with
            | None   => SpClosureStepDone [sp]
            | Some x =>
              let sps' := map (Sp pred) (callSites fr cm)
              in  SpClosureStepDone sps'
            end
          | Pos _ [] :: _         => SpClosureStepError SpInvalidState
          | Pos _ (T _ :: _) :: _ => SpClosureStepError SpInvalidState
          | Pos o_cr (NT x :: suf_cr) :: frs_tl =>
            let stk':= (Pos o_cr suf_cr, frs_tl) 
            in  SpClosureStepK (NtSet.add x av) [Sp pred stk'] 
          end
        | Pos _ (T _ :: _)    => SpClosureStepDone [sp]
        | Pos _ (NT x :: suf) =>
          if NtSet.mem x av then
            let sps' := map (fun rhs => Sp pred 
                                           (Pos (Some x) rhs, fr :: frs))
                            (rhssForNt g x)
            in  SpClosureStepK (NtSet.remove x av) sps' 
          else if NtSet.mem x (allNts g) then
                 SpClosureStepError (SpLeftRecursion x)
               else
                 SpClosureStepK NtSet.empty [] 
        end
      end.

    Definition closure_result := sum prediction_error (list subparser).

    (* consider refactoring to short-circuit in case of error *)
    Fixpoint aggrClosureResults (crs : list closure_result) : closure_result :=
      match crs with
      | [] => inr []
      | cr :: crs' =>
        match (cr, aggrClosureResults crs') with
        | (inl e, _)          => inl e
        | (inr _, inl e)      => inl e
        | (inr sps, inr sps') => inr (sps ++ sps')
        end
      end.

    Definition suffixFrameOf (p : pos) :=
      match p with
      | Pos _ ys => SF ys
      end.

    Definition suffixStackOf (stk : sll_stack) :=
      let (fr, frs) := stk
      in  (suffixFrameOf fr, map suffixFrameOf frs).
    
    Definition meas (g : grammar) (av : NtSet.t) (sp : subparser) : nat * nat :=
      match sp with
      | Sp _ stk =>
        let stk' := suffixStackOf stk in
        let m := maxRhsLength g in
        let e := NtSet.cardinal av               
        in  (stackScore stk' (1 + m) e, stackHeight stk')
      end.

    (*
  Lemma meas_lt_after_return :
    forall g sp sp' av av' pred suf' x frs,
      sp = Sp pred (SF [], SF (NT x :: suf') :: frs)
      -> sp' = Sp pred (SF suf', frs)
      -> av' = NtSet.add x av
      -> lex_nat_pair (meas g av' sp') (meas g av sp).
  Proof.
    intros g sp sp' av av' pred suf' x frs ? ? ?; subst.
    pose proof (stackScore_le_after_return' suf' x) as hle.
    eapply le_lt_or_eq in hle; eauto.
    destruct hle as [hlt | heq]; sis.
    - apply pair_fst_lt; eauto.
    - rewrite heq; apply pair_snd_lt; auto.
  Defined.

  Lemma meas_lt_after_push :
    forall g sp sp' fr fr' av av' pred suf x rhs frs,
      sp     = Sp pred (fr, frs)
      -> sp' = Sp pred (fr', fr :: frs)
      -> fr  = SF (NT x :: suf)
      -> fr' = SF rhs
      -> av' = NtSet.remove x av
      -> NtSet.In x av
      -> In (x, rhs) g
      -> lex_nat_pair (meas g av' sp') (meas g av sp).
  Proof.
    intros g sp sp' fr fr' av av' pred suf x rhs frs ? ? ? ? ? hi hi'; subst.
    apply pair_fst_lt.
    eapply stackScore_lt_after_push; sis; eauto.
  Defined.

  Lemma spClosureStep_meas_lt :
    forall (g      : grammar)
           (sp sp' : subparser)
           (sps'   : list subparser)
           (av av' : NtSet.t),
      spClosureStep g av sp = SpClosureStepK av' sps'
      -> In sp' sps'
      -> lex_nat_pair (meas g av' sp') (meas g av sp).
  Proof.
    intros g sp sp' sps' av av' hs hi. 
    unfold spClosureStep in hs; dmeqs h; tc; inv hs; try solve [inv hi].
    - apply in_singleton_eq in hi; subst.
      eapply meas_lt_after_return; eauto.
    - apply in_map_iff in hi.
      destruct hi as [rhs [heq hi]]; subst.
      eapply meas_lt_after_push; eauto.
      + apply NtSet.mem_spec; auto.
      + apply rhssForNt_in_iff; auto.
  Defined.
     *)
    Lemma acc_after_step :
      forall g cm sp sp' sps' av av',
        spClosureStep g cm av sp = SpClosureStepK av' sps'
        -> In sp' sps'
        -> Acc lex_nat_pair (meas g av sp)
        -> Acc lex_nat_pair (meas g av' sp').
    Proof.
      intros g cm sp sp' sps' av av' heq hi ha.
      eapply Acc_inv; eauto.
      apply magic.
    Defined.

    Fixpoint spClosure (g  : grammar)
             (cm : closure_map)
             (av : NtSet.t)
             (sp : subparser)
             (a  : Acc lex_nat_pair (meas g av sp)) : closure_result :=
      match spClosureStep g cm av sp as r return spClosureStep g cm av sp = r -> _ with
      | SpClosureStepDone sps'  => fun _  => inr sps'
      | SpClosureStepError e    => fun _  => inl e
      | SpClosureStepK av' sps' => 
        fun hs => 
          let crs := dmap sps' (fun sp' hin =>
                                  spClosure g cm av' sp'
                                            (acc_after_step _ _ _ _ _ _ _ hs hin a))
          in  aggrClosureResults crs
      end eq_refl.

    Definition closure (g : grammar) (cm : closure_map) (sps : list subparser) :
      sum prediction_error (list subparser) :=
      aggrClosureResults (map (fun sp => spClosure g cm (allNts g) sp (lex_nat_pair_wf _)) sps).

    (* SLL prediction *)

    Definition finalConfig (sp : subparser) : bool :=
      match sp with
      | Sp _ (Pos None [], []) => true
      | _                      => false
      end.

    Definition allPredictionsEqual (sp : subparser) (sps : list subparser) : bool :=
      allEqual _ beqGamma sp.(prediction) (map prediction sps).

    Definition handleFinalSubparsers (sps : list subparser) : prediction_result :=
      match filter finalConfig sps with
      | []         => PredReject
      | sp :: sps' => 
        if allPredictionsEqual sp sps' then
          PredSucc sp.(prediction)
        else
          PredAmbig sp.(prediction)
      end.

    Definition cache_key := (list subparser * terminal)%type.

    Lemma cache_key_eq_dec : 
      forall k k' : cache_key,
        {k = k'} + {k <> k'}.
    Proof.
      repeat decide equality; try apply t_eq_dec; try apply nt_eq_dec.
    Defined.

    Module MDT_CacheKey.
      Definition t := cache_key.
      Definition eq_dec := cache_key_eq_dec.
    End MDT_CacheKey.
    Module CacheKey_as_DT := Make_UDT(MDT_CacheKey).
    Module Cache := FMapWeakList.Make CacheKey_as_DT.
    Module CacheFacts := WFacts_fun CacheKey_as_DT Cache.

    (* A cache is a finite map with (list subparser * terminal) keys 
     and (list subparser) values *)
    Definition cache : Type := Cache.t (list subparser).

    Definition empty_cache : cache := Cache.empty (list subparser).

    (* To do: maybe only PredSucc and PredAmbig should carry an updated cache *)
    Fixpoint sllPredict' (g : grammar) (cm : closure_map) (sps : list subparser) (ts : list token) (c : cache) : prediction_result * cache :=
      match sps with
      | []         => (PredReject, c)
      | sp :: sps' =>
        if allPredictionsEqual sp sps' then
          (PredSucc sp.(prediction), c)
        else
          match ts with
          | []            => (handleFinalSubparsers sps, c)
          | (a, l) :: ts' =>
            match Cache.find (sps, a) c with 
            | Some sps' => sllPredict' g cm sps' ts' c
            | None      => 
              match move (a, l) sps with
              | inl msg => (PredError msg, c)
              | inr mv  =>
                match closure g cm mv with
                | inl msg => (PredError msg, c)
                | inr cl  =>
                  let c' := Cache.add (sps, a) cl c
                  in  sllPredict' g cm cl ts' c'
                end
              end
            end
          end
      end.

    Definition initSps (g : grammar) (x : nonterminal) : list subparser :=
      map (fun rhs => Sp rhs (Pos (Some x) rhs, []))
          (rhssForNt g x).

    Definition startState (g : grammar) (cm : closure_map)
               (x : nonterminal) : sum prediction_error (list subparser) :=
      closure g cm (initSps g x).

    Definition sllPredict (g : grammar) (cm : closure_map) (x : nonterminal)
               (ts : list token) (c : cache) : prediction_result * cache :=
      match startState g cm x with
      | inl msg => (PredError msg, c)
      | inr sps => sllPredict' g cm sps ts c
      end.

  Definition adaptivePredict g cm x stk ts c : prediction_result * SLL.cache :=
    let sll_res := sllPredict g cm x ts c in
    match sll_res with
    | (PredAmbig _, _) => (llPredict g x stk ts, c)
    | _ => sll_res
    end.

  End SLL.

  (* Equivalence of LL and SLL *)

  Lemma sll'_ll'_equiv_succ :
    forall g cm sps sps' ts c c' ys,
      SLL.sllPredict' g cm sps ts c = (PredSucc ys, c')
      -> llPredict' g sps' ts = PredReject
         \/llPredict' g sps' ts = PredSucc ys.
  Proof.
    intros g cm sps sps' ts c c' ys hs.
    unfold SLL.sllPredict' in hs.
    induction ts as [| t ts IH].
    - destruct sps as [| sp sps]; tc.
      destruct (SLL.allPredictionsEqual sp sps) eqn:ha.
      + (* SLL all equal *)
        destruct sps' as [| sp' sps']; auto.
        right.
  Abort.
  
  Lemma sll_ll_equiv_succ :
    forall g cm fr frs x suf ts c c' ys,
      no_left_recursion g
      -> suffix_stack_wf g (fr, frs)
      -> fr = SF (NT x :: suf)
      -> SLL.sllPredict g cm x ts c = (PredSucc ys, c')
      -> llPredict g x (fr, frs) ts = PredSucc ys.
  Proof.
    intros g cm fr frs x suf ts c c' ys hn hw ? hs; subst.
    unfold SLL.sllPredict in hs.
    destruct (SLL.startState g cm x) as [e | sps] eqn:hss; tc.
    unfold llPredict.
    destruct (startState g x _) as [e | sps'] eqn:hss'.
    - (* lemma *)
      destruct e as [ | x'].
      + exfalso; eapply startState_never_returns_SpInvalidState; eauto.
      + exfalso; eapply closure_never_finds_left_recursion; eauto.
    - (* what do we know at this point?
         - sllPredict' succeeded, so there must be an sp in sps with label ys
         - there must also be an sp' in sps' with label ys *)
     admit.
  Abort.

  Lemma adaptivePredict_equiv_llPredict :
    forall g cm x stk ts c c' r,
      SLL.adaptivePredict g cm x stk ts c = (r, c')
      -> llPredict g x stk ts = r.
  Proof.
    intros g cm x stk ts c c' r ha.
    unfold SLL.adaptivePredict in ha.
    destruct (SLL.sllPredict _ _ _ _ _) as (r', c'') eqn:hs.
    destruct r' as [ys | ys | | e]; inv ha; auto.
    - (* PredSucc *)
      admit.
    - admit.
    - admit.
  Admitted.
      
  

End SllPredictionFn.
