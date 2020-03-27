Require Import List MSets.
Require Import GallStar.LLPrediction_complete.
Require Import GallStar.Utils.
Import ListNotations.

Module GrammarAnalysisFn (Import D : Defs.T).

  Module Export LLPC := LLPredictionCompleteFn D.

  Definition edge := (suffix_frame * suffix_frame)%type.

  Lemma edge_eq_dec :
    forall e e' : edge, {e = e'} + {e <> e'}.
  Proof.
    repeat decide equality; try apply t_eq_dec; try apply nt_eq_dec.
  Qed.

  Module MDT_Edge.
    Definition t      := edge.
    Definition eq_dec := edge_eq_dec.
  End MDT_Edge.
  Module Edge_as_DT   := Make_UDT(MDT_Edge).
  Module EdgeSet      := MSetWeakList.Make Edge_as_DT.
  Module EdgeSetFacts := WFactsOn Edge_as_DT EdgeSet.
  Module ES           := EdgeSet.

  Definition setOf (es : list edge) : ES.t :=
    fold_right ES.add ES.empty es.

  Definition bin (e : edge) (es : list edge) : bool :=
    if in_dec edge_eq_dec e es then true else false.

  Definition src (e : edge) : suffix_frame := fst e.
  Definition dst (e : edge) : suffix_frame := snd e.

  Fixpoint pushEdges' (g : grammar) (x : nonterminal) (ys : list symbol) : list edge :=
    match ys with 
    | []          => []
    | T _ :: ys'  => pushEdges' g x ys'
    | NT y :: ys' =>
      let es := map (fun rhs => (SF (Some x) ys, SF (Some y) rhs))
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
      (SF (Some y) [], SF (Some x) ys') :: returnEdges' x ys'
    end.

  Definition returnEdges (g : grammar) : list edge :=
    flat_map (fun p => returnEdges' (lhs p) (rhs p)) g.

  Definition finalReturnEdges g : list edge :=
    map (fun x => (SF (Some x) [], SF None [])) (lhss g).

  Definition epsilonEdges g : list edge :=
    pushEdges g ++ returnEdges g ++ finalReturnEdges g.

  Fixpoint dsts (es : list edge) (s : suffix_frame) : list suffix_frame :=
    match es with
    | []             => []
    | (s', d) :: es' =>
      if suffix_frame_eq_dec s' s then d :: dsts es' s else dsts es' s
    end.

  Definition newEdges' (es : list edge) (e : edge) : list edge :=
    let (a, b) := e in
    let cs     := filter (fun c => negb (bin (a, c) es)) (dsts es b)
    in  oneToMany a cs.

  Definition newEdges (es : list edge) : list edge :=
    flat_map (newEdges' es) es.

  Definition allSrcs es : list suffix_frame := map src es.
  Definition allDsts es : list suffix_frame := map dst es.

  Definition allEdges es : list edge := 
    let ss := allSrcs es in
    let ds := allDsts es in
    flat_map (fun s => oneToMany s ds) ss.

  Definition stable (fr : suffix_frame) : bool :=
    match fr with
    | SF None []             => true
    | SF (Some x) (T _ :: _) => true
    | _                      => false
    end.

  Fixpoint stablePositions' x ys : list suffix_frame :=
    match ys with
    | []          => []
    | T a :: ys'  => SF (Some x) ys :: stablePositions' x ys'
    | NT _ :: ys' => stablePositions' x ys'
    end.

  Definition stablePositions (g : grammar) : list suffix_frame :=
    SF None [] :: flat_map (fun p => stablePositions' (lhs p) (rhs p)) g.

  (* might not be necessary *)
  Definition reflEdges (g : grammar) : list edge :=
    map (fun p => (p, p)) (stablePositions g).

  Definition m (es : list edge) : nat :=
    ES.cardinal (ES.diff (setOf (allEdges es)) (setOf es)).

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

  Definition dstStable (e : edge) : bool :=
    let (_, b) := e in stable b.

  Definition stableEdges (es : list edge) : list edge :=
    filter dstStable es.

  (* Maybe we don't need the refl edges *)
  Definition mkGraphEdges (g : grammar) : list edge :=
    stableEdges (transClosure (epsilonEdges g)) ++ (reflEdges g).

  (* A closure graph is a map where each key K is a suffix frame 
     (i.e., grammar location), and each value V is a list of frames 
     that are epsilon-reachable from K *)
  (* Maybe the value should be a set *)
  Definition closure_map := FM.t (list suffix_frame).

  Definition addEdge (e : edge) (m : closure_map) : closure_map :=
    let (k, v) := e in
    match FM.find k m with
    | Some vs => FM.add k (v :: vs) m
    | None    => FM.add k [v] m
    end.

  Definition fromEdges (es : list edge) : closure_map :=
    fold_right addEdge (FM.empty (list suffix_frame)) es.

  Definition mkClosureMap (g : grammar) : closure_map :=
    fromEdges (mkGraphEdges g).

  Definition destFrames (cm : closure_map) (fr : suffix_frame) : list suffix_frame :=
    match FM.find fr cm with
    | Some frs => frs
    | None     => []
    end.

End GrammarAnalysisFn.
