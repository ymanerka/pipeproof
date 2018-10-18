Require Import Arith.
Require Import List.
Require Import String.
Require Import Ascii.
Require Import PipeGraph.Debug.
Require Import PipeGraph.Util.
Require Import PipeGraph.StringUtil.
Require Import PipeGraph.Instruction.
Require Import PipeGraph.Graph.
Require Import PipeGraph.FOLPredicate.
Require Import PipeGraph.GraphvizCompressed.

Open Scope string_scope.

Import ListNotations.

Inductive ISAPattern : Set :=
| Rel : ISAEdge -> ISAPattern
| Chain : ISAPattern -> ISAPattern -> ISAPattern
| Union : ISAPattern -> ISAPattern -> ISAPattern
| Intersection : ISAPattern -> ISAPattern -> ISAPattern (* currently unsupported *)
| TranClos : ISAPattern -> ISAPattern
| ReflClos : ISAPattern -> ISAPattern
| ReflTranClos : ISAPattern -> ISAPattern.

(* Restrict ourselves to irr(x) and irr(tranclosure(x)) i.e. acyclic for now. *)
Inductive ISAAxiom : Set :=
| Irr : ISAPattern -> ISAAxiom.

Definition Acyclic
  (a : ISAPattern)
  : ISAAxiom :=
  Irr (TranClos a).

Definition beq_isa_edge
  (a b : ISAEdge)
  : bool :=
  match (a, b) with
  | (EdgePO, EdgePO)
  | (EdgeCO, EdgeCO)
  | (EdgeRF, EdgeRF)
  | (EdgeFR, EdgeFR)
  | (EdgeRFE, EdgeRFE)
  | (EdgeFRE, EdgeFRE)
  | (EdgePO_loc, EdgePO_loc)
  | (EdgePO_plus, EdgePO_plus)
  | (EdgePO_loc_plus, EdgePO_loc_plus)
  | (EdgeFence, EdgeFence)
  | (EdgeToFence, EdgeToFence)
  | (EdgeFromFence, EdgeFromFence)
  | (EdgeFence_plus, EdgeFence_plus)
  | (EdgeFencePO_plus, EdgeFencePO_plus)
  | (EdgePOFence_plus, EdgePOFence_plus)
  | (EdgePPO, EdgePPO)
  | (EdgePPO_plus, EdgePPO_plus)
  | (EdgePPOFence_plus, EdgePPOFence_plus)
  | (EdgeFencePPO_plus, EdgeFencePPO_plus) =>
      true
  | _ => false
  end.

Definition PrintISAEdge
  (a : ISAEdge)
  : string :=
  match a with
  | EdgePO => "po"
  | EdgeCO => "co"
  | EdgeRF => "rf"
  | EdgeFR => "fr"
  | EdgeRFE => "rfe"
  | EdgeFRE => "fre"
  | EdgePO_loc => "po_loc"
  | EdgePO_plus => "po+"
  | EdgePO_loc_plus => "po_loc+"
  | EdgeFence => "fence"
  | EdgeToFence => "to_fence"
  | EdgeFromFence => "from_fence"
  | EdgeFence_plus => "fence+"
  | EdgeFencePO_plus => "fence_po+"
  | EdgePOFence_plus => "po_fence+"
  | EdgePPO => "ppo"
  | EdgePPO_plus => "ppo+"
  | EdgePPOFence_plus => "ppo_fence+"
  | EdgeFencePPO_plus => "fence_ppo+"
  end.

(* What is the ISA edge in uspec land? *)
Definition GetISAEdgeString
  (a : ISAEdge)
  : string :=
  match a with
  | EdgePO => "po"
  | EdgeCO => "co"
  | EdgeRF => "rf"
  | EdgeFR => "fr"
  | EdgeRFE => "rfe"
  | EdgeFRE => "fre"
  | EdgePO_loc => "po_loc"
  | EdgePO_plus => "po_plus"
  | EdgePO_loc_plus => "po_loc_plus"
  | EdgeFence => "fence"
  | EdgeToFence => "to_fence"
  | EdgeFromFence => "from_fence"
  | EdgeFence_plus => "fence_plus"
  | EdgeFencePO_plus => "fence_po_plus"
  | EdgePOFence_plus => "po_fence_plus"
  | EdgePPO => "ppo"
  | EdgePPO_plus => "ppo_plus"
  | EdgePPOFence_plus => "PPOFence_plus"
  | EdgeFencePPO_plus => "FencePPO_plus"
  end.

Fixpoint ContainsEmptyChoice
  (l : list ((list ISAEdge) * option ISAPattern))
  : bool :=
  match l with
  | [] => false
  | h::t => match h with
            | ([], None) => true
            | _ => ContainsEmptyChoice t
            end
  end.

Definition IncludeEmptyChoice
  (l : list (list ISAEdge * option ISAPattern))
  : list (list ISAEdge * option ISAPattern) :=
  if ContainsEmptyChoice l then l else (([], None)::l).

(* ([], None) represents an empty choice. *)
(* Note: I'm assuming that (x?)+ will always be provided to me as x*. *)
Fixpoint GetInitialEdge
  (truncate : bool)
  (n : nat)
  (pat : ISAPattern)
  : list ((list ISAEdge) * option ISAPattern) :=
  let addChainHalfInitial (n'' : nat) (half : ISAPattern) (left : list ISAEdge * option ISAPattern)
    : list (list ISAEdge * option ISAPattern) :=
    match left with
    | ([], None) =>
        (* An empty choice. We need to replace it with GetInitialEdge (half). *)
        GetInitialEdge truncate n'' half
    | (a, None) => [(a, Some half)]
    | (a, Some left') => [(a, Some (Chain left' half))]
    end
  in
  match n with
  | S n' =>
    match pat with
    | Rel edge => [([edge], None)]
    | Chain x y => let a := GetInitialEdge truncate n' x in
                   let b := Map (addChainHalfInitial n' y) a in
                   fold_left app_rev b []
    | Union x y => app_tail (GetInitialEdge truncate n' x) (GetInitialEdge truncate n' y)
    | Intersection x y => Warning [] ["Intersection currently unsupported!"]
    | TranClos x => let a := GetInitialEdge truncate n' x in
                    let b := 
                      if truncate then
                        [a]
                      else
                        Map (addChainHalfInitial n' (ReflTranClos x)) a
                    in
                    fold_left app_rev b []
    | ReflClos x => IncludeEmptyChoice (GetInitialEdge truncate n' x)
    (* Either we provide x's choices with nothing after them except the rest of x,
       or x's choices with another (ReflTranClos x) after whatever's left of x,
       or nothing at all (the reflexive closure kicking in). *)
    | ReflTranClos x => let a := GetInitialEdge truncate n' x in
                        let b :=
                          if truncate then
                            []
                          else
                            Map (addChainHalfInitial n' (ReflTranClos x)) a
                        in
                        let c := fold_left app_rev b [] in
                        IncludeEmptyChoice (app_tail c a)
    end
  | O => Warning [] ["Recursed too deep in GetInitialEdge!"]
  end.

Fixpoint GetFinalEdge
  (n : nat)
  (pat : ISAPattern)
  : list ((list ISAEdge) * option ISAPattern) :=
  let addChainHalfFinal (n'' : nat) (half : ISAPattern) (left : list ISAEdge * option ISAPattern)
    : list (list ISAEdge * option ISAPattern) :=
    match left with
    | ([], None) =>
        (* An empty choice. We need to replace it with GetFinalEdge(half). *)
        GetFinalEdge n'' half
    | (a, None) => [(a, Some half)]
    | (a, Some left') => [(a, Some (Chain half left'))]
    end
  in
  match n with
  | S n' =>
    match pat with
    | Rel edge => [([edge], None)]
    | Chain x y => let a := GetFinalEdge n' y in
                   let b := Map (addChainHalfFinal n' x) a in
                   fold_left app_rev b []
    | Union x y => app_tail (GetFinalEdge n' x) (GetFinalEdge n' y)
    | Intersection x y => Warning [] ["Intersection currently unsupported!"]
    | TranClos x => let a := GetFinalEdge n' x in
                    let b := Map (addChainHalfFinal n' (ReflTranClos x)) a in
                    fold_left app_rev b []
    | ReflClos x => IncludeEmptyChoice (GetFinalEdge n' x)
    (* Either we provide x's choices with nothing before them except the rest of x,
       or x's choices with another (ReflTranClos x) before whatever's left of x,
       or nothing at all (the reflexive closure kicking in). *)
    | ReflTranClos x => let a := GetFinalEdge n' x in
                        let b := Map (addChainHalfFinal n' (ReflTranClos x)) a in
                        let c := fold_left app_rev b [] in
                        IncludeEmptyChoice (app_tail c a)
    end
  | O => Warning [] ["Recursed too deep in GetFinalEdge!"]
  end.

Fixpoint beq_pattern
  (a b : ISAPattern)
  : bool :=
  match (a, b) with
  | (Rel x, Rel x') => beq_isa_edge x x'
  | (Chain x y, Chain x' y')
  | (Union x y, Union x' y')
  | (Intersection x y, Intersection x' y') =>
      andb (beq_pattern x x') (beq_pattern y y')
  | (TranClos x, TranClos x')
  | (ReflClos x, ReflClos x')
  | (ReflTranClos x, ReflTranClos x') =>
      beq_pattern x x'
  | _ => false
  end.

Definition GetISAEdges
  (tups : list (list ISAEdge * option ISAPattern))
  : list (list ISAEdge) :=
  let f x :=
    match x with
    | (y, z) => y
    end
  in
  Map f tups.

Definition GetISAChains
  (tups : list (list ISAEdge * option ISAPattern))
  : list ISAPattern :=
  let f x :=
    match x with
    | (y, z) => z
    end
  in
  let g x y :=
    match y with
    | None => x
    | Some y' => (y'::x)
    end
  in
  let chains := Map f tups in
  fold_left g chains [].

Definition FilterDups
  (l : list ISAPattern)
  : list ISAPattern :=
  let f x y :=
    if find (beq_pattern y) x then x else (y::x)
  in
  fold_left f l [].

Fixpoint GetAllSubchains
  (n : nat)
  (ret : list ISAPattern)
  (pat : ISAPattern)
  : list ISAPattern :=
  let h x y :=
    if find (beq_pattern y) x then false else true
  in
  match n with
  | S n' =>
      (* Add the current chain. *)
      let ret := (pat::ret) in
      (* Find all subchains that you can get by hacking one chunk off the end of the chain. *)
      let subchains := FilterDups (GetISAChains (GetFinalEdge 100 pat)) in
      (* Filter them so we're left with just new subchains. *)
      let subchains := filter (h ret) subchains in
      (* Fold over all the new subchains. *)
      fold_left (GetAllSubchains n') subchains ret
  | O => Warning [] ["Recursed too deep in GetAllSubchains!"]
  end.

Definition GetAllTranChains
  (pat : ISAPattern)
  : list ISAPattern :=
  (* Rip off the last step of the pattern in all possible ways. *)
  GetISAChains (GetFinalEdge 100 pat).

Definition FoldISAChains
  (pat pat' : list ISAPattern)
  : list ISAPattern :=
  let h x y :=
    if find (beq_pattern y) x then false else true
  in
  app_tail pat (filter (h pat) pat').

Fixpoint CanBeNull
  (pat : ISAPattern)
  : bool :=
  match pat with
  | Rel edge => false
  | Chain x y =>
      andb (CanBeNull x) (CanBeNull y)
  | Union x y => orb (CanBeNull x) (CanBeNull y)
  | Intersection x y => Warning false ["Intersection currently unsupported!"]
  | TranClos x => false
  | ReflClos x => true
  | ReflTranClos x => true
  end.

Fixpoint GetSingleEdgeChoices
  (pat : ISAPattern)
  : list (list ISAEdge) :=
  match pat with
  | Rel edge => [[edge]]
  | Chain x y =>
      let result := [] in
      let result :=
        if CanBeNull x then
          app_tail result (GetSingleEdgeChoices y)
        else
          result
      in
      let result :=
        if CanBeNull y then
          app_tail result (GetSingleEdgeChoices x)
        else
          result
      in
      result
  | Union x y => app_tail (GetSingleEdgeChoices x) (GetSingleEdgeChoices y)
  | Intersection x y => Warning [] ["Intersection currently unsupported!"]
  | TranClos x
  | ReflClos x
  | ReflTranClos x => GetSingleEdgeChoices x
  end.

Fixpoint PrintISAPattern
  (pat : ISAPattern)
  : list string :=
  match pat with
  | Rel edge => [PrintISAEdge edge]
  | Chain x y => app_tail (PrintISAPattern x) (" ; "::(PrintISAPattern y))
  | Union x y => app_tail (PrintISAPattern x) (" U "::(PrintISAPattern y))
  | Intersection x y => Warning (app_tail (PrintISAPattern x) (" /\ "::(PrintISAPattern y))) ["Intersection currently unsupported!"]
  | TranClos x => app_tail ("( "::(PrintISAPattern x)) [" )+ "]
  | ReflClos x => app_tail ("( "::(PrintISAPattern x)) [" )? "]
  | ReflTranClos x => app_tail ("( "::(PrintISAPattern x)) [" )* "]
  end.

Definition PrintISAPatterns
  (pats : list ISAPattern)
  : list string :=
  let f x y := app_tail x (newline::"//"::y) in
  let strs := Map PrintISAPattern pats in
  fold_left f strs [].
