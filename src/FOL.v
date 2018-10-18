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
Require Import PipeGraph.ISAEdge.

Open Scope string_scope.

Import ListNotations.

Definition beq_edge
  (a b : GraphEdge)
  : bool :=
  match (a, b) with
  | ((a1, a2, a3, a4), (b1, b2, b3, b4)) =>
      andb (beq_node a1 b1) (beq_node a2 b2)
  end.

Definition GetISAEdge
  (a : string)
  : ISAEdge :=
  if beq_string a "po" then EdgePO
  else if beq_string a "co" then EdgeCO
  else if beq_string a "rf" then EdgeRF
  else if beq_string a "fr" then EdgeFR
  else if beq_string a "rfe" then EdgeRFE
  else if beq_string a "fre" then EdgeFRE
  else if beq_string a "po_loc" then EdgePO_loc
  else if beq_string a "po_plus" then EdgePO_plus
  else if beq_string a "po_loc_plus" then EdgePO_loc_plus
  else if beq_string a "fence" then EdgeFence
  else if beq_string a "to_fence" then EdgeToFence
  else if beq_string a "from_fence" then EdgeFromFence
  else if beq_string a "fence_plus" then EdgeFence_plus
  else if beq_string a "FencePO_plus" then EdgeFencePO_plus
  else if beq_string a "POFence_plus" then EdgePOFence_plus
  else if beq_string a "ppo" then EdgePPO
  else if beq_string a "ppo_plus" then EdgePPO_plus
  else if beq_string a "FencePPO_plus" then EdgeFencePPO_plus
  else if beq_string a "PPOFence_plus" then EdgePPOFence_plus
  else Warning EdgePO ["Got a dependency I can't handle: "; a].

Definition beq_pred
  (a b : FOLSymPred)
  : bool :=
  match (a, b) with
  | (SymPredIsRead a, SymPredIsRead a')
  | (SymPredIsWrite a, SymPredIsWrite a')
  | (SymPredIsFence a, SymPredIsFence a')
  | (SymPredKnownData a, SymPredKnownData a')
  | (SymPredDataFromPAInitial a, SymPredDataFromPAInitial a')
  | (SymPredDataFromPAFinal a, SymPredDataFromPAFinal a') =>
      beq_uop a a'
  | (SymPredIsAPICAccess a b, SymPredIsAPICAccess a' b')
  | (SymPredAccessType a b, SymPredAccessType a' b') =>
      andb (beq_uop a a') (beq_string b b')
  | (SymPredOnCore a b, SymPredOnCore a' b')
  | (SymPredOnThread a b, SymPredOnThread a' b') =>
      andb (beq_uop a a') (beq_nat b b')
  | (SymPredSameCore a b, SymPredSameCore a' b')
  | (SymPredSameIntraInstID a b, SymPredSameIntraInstID a' b')
  | (SymPredSameThread a b, SymPredSameThread a' b')
  | (SymPredSameVirtualAddress a b, SymPredSameVirtualAddress a' b')
  | (SymPredSamePhysicalAddress a b, SymPredSamePhysicalAddress a' b')
  | (SymPredSameVirtualTag a b, SymPredSameVirtualTag a' b')
  | (SymPredSamePhysicalTag a b, SymPredSamePhysicalTag a' b')
  | (SymPredSameIndex a b, SymPredSameIndex a' b')
  | (SymPredSameData a b, SymPredSameData a' b')
  | (SymPredSamePAasPTEforVA a b, SymPredSamePAasPTEforVA a' b') =>
      (* Allow symmetry *)
      orb (andb (beq_uop a a') (beq_uop b b'))
          (andb (beq_uop a b') (beq_uop b a'))
  | (SymPredProgramOrder a b, SymPredProgramOrder a' b')
  | (SymPredConsec a b, SymPredConsec a' b') =>
      (* No symmetry *)
      andb (beq_uop a a') (beq_uop b b')
  | (SymPredHasDependency a b c, SymPredHasDependency a' b' c') =>
      (* No symmetry *)
      andb (andb (beq_uop a a') (beq_uop b b')) (beq_isa_edge c c')
  | _ => false
  end.


Inductive ScenarioTree : Set :=
| ScenarioName : string -> ScenarioTree -> ScenarioTree
| ScenarioConflict : ScenarioTree -> ScenarioTree
| ScenarioAnd : ScenarioTree -> ScenarioTree -> ScenarioTree
| ScenarioOr : ScenarioTree -> ScenarioTree -> ScenarioTree
| ScenarioEdgeLeaf : list GraphEdge -> ScenarioTree
| ScenarioNotEdgeLeaf : list GraphEdge -> ScenarioTree
| ScenarioNodeLeaf : list GraphNode -> ScenarioTree
| ScenarioNotNodeLeaf : list GraphNode -> ScenarioTree
| ScenarioPred : FOLSymPred -> ScenarioTree
| ScenarioNotPred : FOLSymPred -> ScenarioTree
| ScenarioTrue : ScenarioTree
| ScenarioFalse : ScenarioTree.

Fixpoint FlipEdgesHelper
  (l r : list GraphEdge)
  : list GraphEdge :=
  match l with
  | (s, d, label, c) :: t =>
      FlipEdgesHelper t ((d, s, label, c) :: r)
  | [] => r
  end.

Definition FlipEdges
  (l : list GraphEdge)
  : list GraphEdge :=
  FlipEdgesHelper l [].

Fixpoint PrintLabelsHelper
  (l : list string)
  (r : string)
  : string :=
  match l with
  | h::t => PrintLabelsHelper t (StringOf [h; "\n"; r])
  | [] => r
  end.

Definition PrintLabels
  (l : option (list string))
  : string :=
  match l with
  | Some l' => PrintLabelsHelper l' EmptyString
  | None => EmptyString
  end.

Definition PrintEdgeLabels
  (l : list GraphEdge)
  : string :=
  match l with
  | h::t =>
    fold_left (fun a b => StringOf [a; "\n"; ShortStringOfGraphEdge b]) t
      (ShortStringOfGraphEdge h)
  | [] => "-"
  end.

Definition PrintNodeLabels
  (l : list GraphNode)
  : string :=
  match l with
  | h::t =>
    fold_left (fun a b => StringOf [a; "\n"; ShortStringOfGraphNode b]) t
      (ShortStringOfGraphNode h)
  | [] => "-"
  end.

Definition PrintPredicate
  (p : FOLSymPred)
  : list string :=
  match p with
  | SymPredHasDependency a b c => ["HasDependency "; stringOfNat (globalID a); " ";
      stringOfNat (globalID b);  PrintISAEdge c]
  | SymPredIsRead a => ["IsAnyRead "; stringOfNat (globalID a)] 
  | SymPredIsWrite a => ["IsAnyWrite "; stringOfNat (globalID a)]
  | SymPredIsAPICAccess a b => ["IsAPICAccess "; stringOfNat (globalID a); " "; b]
  | SymPredIsFence a => ["IsAnyFence "; stringOfNat (globalID a)]
  | SymPredAccessType a b => ["AccessType "; stringOfNat (globalID a); " "; b]
  | SymPredSameCore a b => ["SameCore "; stringOfNat (globalID a); " "; stringOfNat (globalID b)]
  | SymPredSameIntraInstID a b => ["SameIntraInstID "; stringOfNat (globalID a); " "; stringOfNat (globalID b)]
  | SymPredSameThread a b => ["SameThread "; stringOfNat (globalID a); " "; stringOfNat (globalID b)]
  | SymPredOnCore a b => ["OnCore "; stringOfNat (globalID a); " "; stringOfNat b]
  | SymPredOnThread a b => ["OnThread "; stringOfNat (globalID a); " "; stringOfNat b]
  | SymPredSameVirtualAddress a b => ["SameVirtualAddress "; stringOfNat (globalID a); " "; stringOfNat (globalID b)]
  | SymPredSamePhysicalAddress a b => ["SamePhysicalAddress "; stringOfNat (globalID a); " "; stringOfNat (globalID b)]
  | SymPredSameVirtualTag a b => ["SameVirtualTag "; stringOfNat (globalID a); " "; stringOfNat (globalID b)]
  | SymPredSamePhysicalTag a b => ["SamePhysicalTag "; stringOfNat (globalID a); " "; stringOfNat (globalID b)]
  | SymPredSameIndex a b => ["SameIndex "; stringOfNat (globalID a); " "; stringOfNat (globalID b)]
  | SymPredKnownData a => ["KnownData "; stringOfNat (globalID a)]
  | SymPredSameData a b => ["SameData "; stringOfNat (globalID a); " "; stringOfNat (globalID b)]
  | SymPredDataFromPAInitial a => ["DataFromPAInitial "; stringOfNat (globalID a)]
  | SymPredDataFromPAFinal a => ["DataFromPAFinal "; stringOfNat (globalID a)]
  | SymPredSamePAasPTEforVA a b => ["SamePAasPTEforVA "; stringOfNat (globalID a); " "; stringOfNat (globalID b)]
  | SymPredProgramOrder a b => ["ProgramOrder "; stringOfNat (globalID a); " "; stringOfNat (globalID b)]
  | SymPredConsec a b => ["ConsecutiveMicroops "; stringOfNat (globalID a); " "; stringOfNat (globalID b)]
  end.

Fixpoint ScenarioTreeEdgeCountGraphHelper
  (ac : bool) (* all conjunctions *)
  (t : ScenarioTree)
  (id : nat)
  (n : option (list string))
  : nat * nat :=
  match t with
  | ScenarioName n'' t' =>
     match n with
     | Some n' => ScenarioTreeEdgeCountGraphHelper ac t' id (Some (n'' :: n'))
     | None => ScenarioTreeEdgeCountGraphHelper ac t' id (Some [n''])
     end
  | ScenarioConflict t' =>
     match n with
     | Some n' => ScenarioTreeEdgeCountGraphHelper ac t' id (Some ("Conflict" :: n'))
     | None => ScenarioTreeEdgeCountGraphHelper ac t' id (Some ["Conflict"])
     end
  | ScenarioEdgeLeaf l =>
      let result := (1, id) in
      Println result ["  n"; stringOfNat id; " [shape=";
        if ac then "box" else "oval"; ",label=""";
        PrintLabels n;
        stringOfNat (List.length l); " edges\n";
        PrintEdgeLabels l; """];"]
  | ScenarioNotEdgeLeaf l =>
      let result := (1, id) in
      Println result ["  n"; stringOfNat id; " [shape=";
        if ac then "box" else "oval"; ",label=""";
        PrintLabels n;
        stringOfNat (List.length l); " edges\nNot all of:\n";
        PrintEdgeLabels l; """];"]
  | ScenarioNodeLeaf l =>
      let result := (1, id) in
      Println result ["  n"; stringOfNat id; " [shape=";
        if ac then "box" else "oval"; ",label=""";
        PrintLabels n;
        stringOfNat (List.length l); " nodes";
        PrintNodeLabels l; """];"]
  | ScenarioNotNodeLeaf l =>
      let result := (1, id) in
      Println result ["  n"; stringOfNat id; " [shape=";
        if ac then "box" else "oval"; ",label=""";
        PrintLabels n;
        stringOfNat (List.length l); " nodes\nNot all of:\n";
        PrintNodeLabels l; """];"]
  | ScenarioPred p =>
      let result := (1, id) in
      Println result ["  n"; stringOfNat id; " [shape=";
        if ac then "box" else "oval"; ",label=""";
        StringOf (PrintPredicate p); """];"]
  | ScenarioNotPred p =>
      let result := (1, id) in
      Println result ["  n"; stringOfNat id; " [shape=";
        if ac then "box" else "oval"; ",label=""NOT ";
        StringOf (PrintPredicate p); """];"]
  | ScenarioAnd a b =>
      let (a_count, a_id) := ScenarioTreeEdgeCountGraphHelper ac a id None in
      let (b_count, b_id) := ScenarioTreeEdgeCountGraphHelper ac b (S a_id) None in
      let count := a_count * b_count in
      let color :=
        if andb (blt_nat 1 a_count) (blt_nat 1 b_count)
        then "green"
        else "black" in
      let result := (count, S b_id) in
      let result :=
        Println result ["  n"; stringOfNat (S b_id); " [shape=";
        if ac then "box" else "oval"; ",color=";
          color; ";label=""";
        PrintLabels n;
        "AND""];"] in
      let result := Println result ["  n"; stringOfNat (S b_id); " -> n";
        stringOfNat a_id; ";"] in
      let result := Println result ["  n"; stringOfNat (S b_id); " -> n";
        stringOfNat b_id; ";"] in
      result
  | ScenarioOr a b =>
      let (a_count, a_id) := ScenarioTreeEdgeCountGraphHelper false a id None in
      let (b_count, b_id) := ScenarioTreeEdgeCountGraphHelper false b (S a_id) None in
      let count := a_count + b_count in
      let color :=
        if andb (blt_nat 0 a_count) (blt_nat 0 b_count)
        then "blue"
        else "black" in
      let result := (count, S b_id) in
      let result :=
        Println result ["  n"; stringOfNat (S b_id); " [shape=";
        if ac then "box" else "oval"; ",color=blue;label=""";
        PrintLabels n;
        "OR""];"] in
      let result := Println result ["  n"; stringOfNat (S b_id); " -> n";
        stringOfNat a_id; ";"] in
      let result := Println result ["  n"; stringOfNat (S b_id); " -> n";
        stringOfNat b_id; ";"] in
      result
  | ScenarioTrue =>
      let result := (1, id) in
      Println result ["  n"; stringOfNat id; " [shape=";
        if ac then "box" else "oval"; ",label=""TRUE""];"]
  | ScenarioFalse => 
      let result := (1, id) in
      Println result ["  n"; stringOfNat id; " [shape=";
        if ac then "box" else "oval"; ",color=red,label=""FALSE""];"]
  end.

Definition ScenarioTreeEdgeCountGraphHelper1
  (t : ScenarioTree)
  (n : string)
  : ScenarioTree :=
  let t := Println t ["digraph "; n; " {"] in
  let t := Println t [tab; "label="""; n; """;"] in
  let t := Println t [tab; "layout=dot;"] in
  let t := Println t [tab; "rankdir=LR;"] in
  let (count, _) := ScenarioTreeEdgeCountGraphHelper true t 0 None in
  Println t ["}"; newline; "// "; stringOfNat count; " scenarios"; newline].

Definition ScenarioTreeEdgeCountGraph
  (f : nat)
  (t : ScenarioTree)
  (n : string)
  : ScenarioTree :=
  if PrintFlag f
  then ScenarioTreeEdgeCountGraphHelper1 t n
  else t.

Fixpoint ReducesToTrue
  (t : ScenarioTree)
  : bool :=
  match t with
  | ScenarioName _ t'
  | ScenarioConflict t' => ReducesToTrue t'
  | ScenarioEdgeLeaf [] => true
  | ScenarioEdgeLeaf _ => false
  | ScenarioNotEdgeLeaf [] => true
  | ScenarioNotEdgeLeaf _ => false
  | ScenarioNodeLeaf [] => true
  | ScenarioNodeLeaf _ => false
  | ScenarioNotNodeLeaf [] => true
  | ScenarioNotNodeLeaf _ => false
  | ScenarioPred _ => false
  | ScenarioNotPred _ => false
  | ScenarioAnd a b => andb (ReducesToTrue a) (ReducesToTrue b)
  | ScenarioOr a b => orb (ReducesToTrue a) (ReducesToTrue b)
  | ScenarioTrue => true
  | ScenarioFalse => false
  end.

Fixpoint ReducesToFalse
  (t : ScenarioTree)
  : bool :=
  match t with
  | ScenarioName _ t'
  | ScenarioConflict t' => ReducesToFalse t'
  | ScenarioEdgeLeaf _ => false
  | ScenarioNotEdgeLeaf _ => false
  | ScenarioNodeLeaf _ => false
  | ScenarioNotNodeLeaf _ => false
  | ScenarioPred _ => false
  | ScenarioNotPred _ => false
  | ScenarioAnd a b => orb (ReducesToFalse a) (ReducesToFalse b)
  | ScenarioOr a b => andb (ReducesToFalse a) (ReducesToFalse b)
  | ScenarioTrue => false
  | ScenarioFalse => true
  end.

Fixpoint SimplifyScenarioTree
  (t : ScenarioTree)
  : ScenarioTree :=
  match t with
  | ScenarioName n t' =>
      match SimplifyScenarioTree t' with
      | ScenarioTrue => ScenarioTrue
      | ScenarioFalse => ScenarioFalse
      | t'' => ScenarioName n t''
      end
  | ScenarioConflict t' =>
      match SimplifyScenarioTree t' with
      | ScenarioTrue => ScenarioTrue
      | ScenarioFalse => ScenarioFalse
      | t'' => ScenarioConflict t''
      end
  | ScenarioEdgeLeaf [] => ScenarioTrue
  | ScenarioNotEdgeLeaf [] => ScenarioTrue
  | ScenarioNodeLeaf [] => ScenarioTrue
  | ScenarioNotNodeLeaf [] => ScenarioTrue
  | ScenarioEdgeLeaf l => t
  | ScenarioNotEdgeLeaf l => t
  | ScenarioNodeLeaf l => t
  | ScenarioNotNodeLeaf l => t
  | ScenarioPred _ => t
  | ScenarioNotPred _ => t
  | ScenarioAnd a b =>
      let a' := SimplifyScenarioTree a in
      let b' := SimplifyScenarioTree b in
      if ReducesToFalse a' then ScenarioFalse else
      if ReducesToFalse b' then ScenarioFalse else
      if ReducesToTrue a' then b' else
      if ReducesToTrue b' then a' else
      ScenarioAnd a' b'
  | ScenarioOr a b =>
      let a' := SimplifyScenarioTree a in
      let b' := SimplifyScenarioTree b in
      if ReducesToTrue a' then ScenarioTrue else
      if ReducesToTrue b' then ScenarioTrue else
      if ReducesToFalse a' then b' else
      if ReducesToFalse b' then a' else
      ScenarioOr a' b'
  | ScenarioTrue => t
  | ScenarioFalse => t
  end.

Fixpoint GuaranteedEdges
  (s : ScenarioTree)
  : (list GraphNode * list GraphNode * list GraphEdge * list GraphEdge * list FOLSymPred * list FOLSymPred) :=
  match s with
  | ScenarioName _ s
  | ScenarioConflict s => GuaranteedEdges s
  | ScenarioNodeLeaf l => (l, [], [], [], [], [])
  | ScenarioNotNodeLeaf l => ([], l, [], [], [], [])
  | ScenarioEdgeLeaf l => ([], [], l, [], [], [])
  | ScenarioNotEdgeLeaf l => ([], [], [], l, [], [])
  | ScenarioPred p => ([], [], [], [], [p], [])
  | ScenarioNotPred p => ([], [], [], [], [], [p])
  | ScenarioAnd a b =>
      match (GuaranteedEdges a, GuaranteedEdges b) with
      | ((a1, a2, a3, a4, a5, a6), (b1, b2, b3, b4, b5, b6)) =>
          (app_rev a1 b1, app_rev a2 b2, app_rev a3 b3, app_rev a4 b4, app_rev a5 b5, app_rev a6 b6)
      end
  (* YM: This could maybe be optimized by checking what is common between both branches of the OR... *)
  | ScenarioOr _ _ => ([], [], [], [], [], [])
  | ScenarioTrue => ([], [], [], [], [], [])
  | ScenarioFalse => Warning ([], [], [], [], [], [])
      ["Shouldn't try to calculate the GuaranteedEdges of FALSE"]
  end.

Fixpoint ContainsOnlyEdges
  (t: ScenarioTree)
  : bool :=
  match t with
  | ScenarioName _ s
  | ScenarioConflict s => ContainsOnlyEdges s
  | ScenarioEdgeLeaf _ => true
  | ScenarioNotEdgeLeaf _ => true
  | ScenarioNodeLeaf _ => true
  | ScenarioNotNodeLeaf _ => true
  | ScenarioPred _ => false
  | ScenarioNotPred _ => false
  | ScenarioAnd a b => andb (ContainsOnlyEdges a) (ContainsOnlyEdges b)
  | ScenarioOr a b => andb (ContainsOnlyEdges a) (ContainsOnlyEdges b)
  | ScenarioTrue => true
  | ScenarioFalse => true
  end.

Fixpoint ContainsOnlyPreds
  (t: ScenarioTree)
  : bool :=
  match t with
  | ScenarioName _ s
  | ScenarioConflict s => ContainsOnlyPreds s
  | ScenarioEdgeLeaf _ => false
  | ScenarioNotEdgeLeaf _ => false
  | ScenarioNodeLeaf _ => false
  | ScenarioNotNodeLeaf _ => false
  | ScenarioPred _ => true
  | ScenarioNotPred _ => true
  | ScenarioAnd a b => andb (ContainsOnlyPreds a) (ContainsOnlyPreds b)
  | ScenarioOr a b => andb (ContainsOnlyPreds a) (ContainsOnlyPreds b)
  | ScenarioTrue => true
  | ScenarioFalse => true
  end.

Fixpoint ListContainsOnlyEdges
  (l: list ScenarioTree)
  : bool :=
  match l with
  | [] => true
  | h::t => if ContainsOnlyEdges h then ListContainsOnlyEdges t else false
  end.

Fixpoint ListContainsOnlyPreds
  (l: list ScenarioTree)
  : bool :=
  match l with
  | [] => true
  | h::t => if ContainsOnlyPreds h then ListContainsOnlyPreds t else false
  end.

Fixpoint SortPredsHelper
  (l: list ScenarioTree)
  (l1: list ScenarioTree)
  (l2: list ScenarioTree)
  (l3: list ScenarioTree)
  : list ScenarioTree :=
  match l with
  | [] => app_tail l3 (app_tail l2 l1)
  | h::t => match h with
            | ScenarioPred (SymPredHasDependency _ _ _)
            | ScenarioNotPred (SymPredHasDependency _ _ _) => SortPredsHelper t (h::l1) l2 l3
            | ScenarioPred (SymPredIsRead _ )
            | ScenarioPred (SymPredIsWrite _ )
            | ScenarioPred (SymPredSameCore _ _)
            | ScenarioPred (SymPredSamePhysicalAddress _ _)
            | ScenarioPred (SymPredSameData _ _) => SortPredsHelper t l1 (h::l2) l3
            | _ => SortPredsHelper t l1 l2 (h::l3)
            end
  end.

Fixpoint ScoreOfTree
  (t : ScenarioTree)
  : nat :=
  match t with
  | ScenarioName _ s
  | ScenarioConflict s => ScoreOfTree s
  | ScenarioEdgeLeaf l
  | ScenarioNotEdgeLeaf l
  | ScenarioNodeLeaf l
  | ScenarioNotNodeLeaf l => List.length l
  | ScenarioPred _ => 1
  | ScenarioNotPred _ => 1
  | ScenarioAnd a b => (ScoreOfTree a) + (ScoreOfTree b)
  | ScenarioOr a b => Warning (ScoreOfTree a) ["An OR in ScoreOfTree?"]
  | ScenarioTrue => 0
  | ScenarioFalse => 0
  end.

Fixpoint InsertInto
  (sorted : list (nat * ScenarioTree))
  (elem : nat * ScenarioTree)
  : list (nat * ScenarioTree) :=
  let (score, t) := elem in
  match sorted with
  | [] => [elem]
  | h::t => let (score', t') := h in
            if blt_nat score score' then
              h::(InsertInto t elem)
            else
              elem::sorted
  end.


Fixpoint InsertionSort
  (sorted to_sort : list (nat * ScenarioTree))
  : list (nat * ScenarioTree) :=
  match to_sort with
  | [] => sorted
  | h::t => InsertionSort (InsertInto sorted h) t
  end.

Definition SortPreds
  (l : list ScenarioTree)
  : list ScenarioTree :=
  let f x := (ScoreOfTree x, x) in
  let g x := snd x in
  Map g (InsertionSort [] (Map f l)).

Fixpoint SortChoicesHelper
  (l: list ScenarioTree)
  (l1: list ScenarioTree)
  (l2: list ScenarioTree)
  (l3: list ScenarioTree)
  : list ScenarioTree :=
  match l with
  | [] => app_tail (app_tail (SortPreds l2) l1) l3
  | h::t => if ContainsOnlyEdges h then
              SortChoicesHelper t (h::l1) l2 l3
            else if ContainsOnlyPreds h then
              SortChoicesHelper t l1 (h::l2) l3
            else
              SortChoicesHelper t l1 l2 (h::l3)
  end.

Fixpoint SortChoices
  (l: list ScenarioTree)
  : list ScenarioTree :=
  SortChoicesHelper l [] [] [].

Fixpoint ScenarioTreeCrossProductHelper
  (a : ScenarioTree)
  (b : list ScenarioTree)
  : list ScenarioTree :=
  let f x := ScenarioAnd a x in
  Map f b.

Fixpoint ScenarioTreeCrossProduct
  (a : list ScenarioTree)
  (b : list ScenarioTree)
  (c : list ScenarioTree)
  : list ScenarioTree :=
  match a with
  | [] => c
  | h::t => ScenarioTreeCrossProduct t b (app_rev (ScenarioTreeCrossProductHelper h b) c)
  end.

Definition ListContainsOnlyMatching
  (f : ScenarioTree -> bool)
  (l : list ScenarioTree)
  : bool :=
  fold_left andb (Map f l) true.

Definition ListContainsOnlyHasDeps
  (l : list ScenarioTree)
  : bool :=
  let f x :=
    match x with
    | ScenarioPred (SymPredHasDependency _ _ _) => true
    | ScenarioNotPred (SymPredHasDependency _ _ _) => true
    | _ => false
    end
  in
  ListContainsOnlyMatching f l.

Definition ListContainsOnlyNotEdges
  (l : list ScenarioTree)
  : bool :=
  let f x :=
    match x with
    | ScenarioNotEdgeLeaf _ => true
    | _ => false
    end
  in
  ListContainsOnlyMatching f l.

Definition BelowCPThresholdInternal (n : nat) := false.

Definition BelowCrossThreshold
  (l : list ScenarioTree)
  : bool :=
  BelowCPThresholdInternal (List.length l).

Definition MostCommonPreds
  (p : FOLSymPred)
  : bool :=
  match p with
  | SymPredIsRead _
  | SymPredIsWrite _
  | SymPredSamePhysicalAddress _ _
  | SymPredSameCore _ _
  | SymPredProgramOrder _ _
  | SymPredHasDependency _ _ _ => true
  | _ => false
  end.

Fixpoint PredicateScore
  (f : FOLSymPred -> bool)
  (t : ScenarioTree)
  : nat :=
  match t with
  | ScenarioName _ s => PredicateScore f s
  | ScenarioConflict s => 5 * (PredicateScore f s) (* This better be enough... *)
  | ScenarioEdgeLeaf l
  | ScenarioNotEdgeLeaf l
  | ScenarioNodeLeaf l
  | ScenarioNotNodeLeaf l => 2 * (List.length l)
  | ScenarioPred p
  | ScenarioNotPred p => if (f p) then 1 else 0
  | ScenarioAnd a b => (PredicateScore f a) + (PredicateScore f b)
  | ScenarioOr a b => Warning 0 ["OR in a choice in PredicateScore???"]
  | ScenarioTrue => 0
  | ScenarioFalse => 0
  end.

Definition ListPredicateScore
  (l : list ScenarioTree)
  : nat :=
  fold_left plus (Map (PredicateScore MostCommonPreds) l) 0.

Inductive BranchingStrategy : Set :=
| DefaultStrat : BranchingStrategy
| HasDepStrat : bool -> BranchingStrategy
| NotEdgeStrat : bool -> BranchingStrategy.

Inductive BranchingChoice : Set :=
| RegularChoice : list ScenarioTree -> BranchingChoice
| ConflictChoice : list ScenarioTree -> BranchingChoice.

Fixpoint FindBranchingChoices
  (strat : BranchingStrategy)
  (s : ScenarioTree)
  : option BranchingChoice :=
  match s with
  | ScenarioName _ s => FindBranchingChoices strat s
  | ScenarioConflict s =>
      match FindBranchingChoices strat s with
      | None => Warning None ["No branching choices inside a conflict clause?"]
      | Some (RegularChoice l)
      | Some (ConflictChoice l) => Some (ConflictChoice l)
      end
  | ScenarioEdgeLeaf [] => None
  | ScenarioEdgeLeaf l => Some (RegularChoice [s])
  | ScenarioNotEdgeLeaf [] => None
  | ScenarioNotEdgeLeaf l => Some (RegularChoice [s])
  | ScenarioNodeLeaf [] => None
  | ScenarioNodeLeaf l => Some (RegularChoice [s])
  | ScenarioNotNodeLeaf [] => None
  | ScenarioNotNodeLeaf l => Some (RegularChoice [s])
  | ScenarioPred p => Some (RegularChoice [s])
  | ScenarioNotPred p => Some (RegularChoice [s])
  | ScenarioAnd a b =>
      match FindBranchingChoices strat a with
      | None => FindBranchingChoices strat b
      | Some a' =>
          match a' with
          | RegularChoice a''
          | ConflictChoice a'' =>
              match FindBranchingChoices strat b with
              | None => Some a'
              | Some b' => 
                  match b' with
                  | RegularChoice b''
                  | ConflictChoice b'' =>
                           match strat with
                           | DefaultStrat =>
                              (* Are we dealing with small lists? *)
                              if andb (BelowCrossThreshold a'') (BelowCrossThreshold b'') then
                                (* The lists are already bound to a'' and b'' above, so we don't create new variables here... *)
                                match (a', b') with
                                | (ConflictChoice _, ConflictChoice _) =>
                                    Some (ConflictChoice (ScenarioTreeCrossProduct a'' b'' []))
                                | _ =>
                                    Some (RegularChoice (ScenarioTreeCrossProduct a'' b'' []))
                                end
                              else
                                (* The lists are already bound to a'' and b'' above, so we don't create new variables here... *)
                                match (a', b') with
                                | (RegularChoice _, RegularChoice _)
                                | (ConflictChoice _, ConflictChoice _) =>
                                  (* Just pick the largest of the ORs; try and eliminate as much of the ScenarioTree as possible *)
                                  if bgt_nat (List.length a'') (List.length b'') then
                                    Some a'
                                  else
                                    Some b'
                                | (ConflictChoice _, _) => Some (ConflictChoice a'')
                                | (_, ConflictChoice _) => Some (ConflictChoice b'')
                                end
                           | HasDepStrat first =>
                              if first then
                                if bgt_nat (List.length a'') (List.length b'') then
                                  if ListContainsOnlyHasDeps a'' then Some a'
                                  else if ListContainsOnlyHasDeps b'' then Some b'
                                  else Some a'
                                else
                                  if ListContainsOnlyHasDeps b'' then Some b'
                                  else if ListContainsOnlyHasDeps a'' then Some a'
                                  else Some b'
                              else
                                (* Are we dealing with small lists? *)
                                if andb (BelowCrossThreshold a'') (BelowCrossThreshold b'') then
                                  match (a', b') with
                                  | (ConflictChoice _, ConflictChoice _) =>
                                      Some (ConflictChoice (ScenarioTreeCrossProduct a'' b'' []))
                                  | _ =>
                                      Some (RegularChoice (ScenarioTreeCrossProduct a'' b'' []))
                                  end
                                else
                                  (* The lists are already bound to a'' and b'' above, so we don't create new variables here... *)
                                  match (a', b') with
                                  | (RegularChoice _, RegularChoice _)
                                  | (ConflictChoice _, ConflictChoice _) =>
                                    (* Just pick the largest of the ORs; try and eliminate as much of the ScenarioTree as possible *)
                                    if bgt_nat (List.length a'') (List.length b'') then
                                      Some a'
                                    else
                                      Some b'
                                  | (ConflictChoice _, _) => Some (ConflictChoice a'')
                                  | (_, ConflictChoice _) => Some (ConflictChoice b'')
                                  end
                           | NotEdgeStrat first =>
                              if first then
                                if bgt_nat (List.length a'') (List.length b'') then
                                  if ListContainsOnlyNotEdges a'' then Some a'
                                  else if ListContainsOnlyNotEdges b'' then Some b'
                                  else Some a'
                                else
                                  if ListContainsOnlyNotEdges b'' then Some b'
                                  else if ListContainsOnlyNotEdges a'' then Some a'
                                  else Some b'
                              else
                                (* Are we dealing with small lists? *)
                                if andb (BelowCrossThreshold a'') (BelowCrossThreshold b'') then
                                  match (a', b') with
                                  | (ConflictChoice _, ConflictChoice _) =>
                                      Some (ConflictChoice (ScenarioTreeCrossProduct a'' b'' []))
                                  | _ =>
                                      Some (RegularChoice (ScenarioTreeCrossProduct a'' b'' []))
                                  end
                                else
                                  (* The lists are already bound to a'' and b'' above, so we don't create new variables here... *)
                                  match (a', b') with
                                  | (RegularChoice _, RegularChoice _)
                                  | (ConflictChoice _, ConflictChoice _) =>
                                      if bgt_nat (List.length a'') (List.length b'') then
                                        Some a'
                                      else
                                        Some b'
                                  | (ConflictChoice _, _) => Some (ConflictChoice a'')
                                  | (_, ConflictChoice _) => Some (ConflictChoice b'')
                                  end
                           end
                  end
              end
          end
      end
  | ScenarioOr a b =>
      match FindBranchingChoices strat a with
      | None => FindBranchingChoices strat b
      | Some (RegularChoice l) =>
          match FindBranchingChoices strat b with
          | None => Some (RegularChoice l)
          | Some (RegularChoice l') => Some (RegularChoice (app_rev l l'))
          | Some (ConflictChoice l') => Warning (Some (ConflictChoice (app_rev l l'))) ["Conflict clause ORed with something?"]
          end
      | Some (ConflictChoice l) =>
          let l := Warning l ["Conflict clause ORed with something?"] in
          match FindBranchingChoices strat b with
          | None => Some (ConflictChoice l)
          | Some (RegularChoice l')
          | Some (ConflictChoice l') => Some (ConflictChoice (app_rev l l'))
          end
      end
  | ScenarioTrue => None
  | ScenarioFalse => None
  end.

Inductive FOLTerm : Set :=
| IntTerm : string -> nat -> FOLTerm
| StageNameTerm : string -> nat -> FOLTerm
| MicroopTerm : string -> Microop -> FOLTerm
| NodeTerm : string -> GraphNode -> FOLTerm
| EdgeTerm : string -> GraphEdge -> FOLTerm
| MacroArgTerm : string -> StringOrInt -> FOLTerm.

Definition FOLTermName
  (t : FOLTerm)
  : string :=
  match t with
  | IntTerm n _ => n
  | StageNameTerm n _ => n
  | MicroopTerm n _ => n
  | NodeTerm n _ => n
  | EdgeTerm n _ => n
  | MacroArgTerm n _ => n
  end.

Definition AddTerm
  (l : list FOLTerm)
  (t : FOLTerm)
  : list FOLTerm :=
  match find (fun x => beq_string (FOLTermName x) (FOLTermName t)) l with
  | Some _ => Warning (t::l) ["Shadowing term '"; FOLTermName t; "'"]
  | None => t::l
  end.

Definition stringOfFOLTermValue
  (t : FOLTerm)
  : string :=
  match t with
  | IntTerm _ n => stringOfNat n
  | StageNameTerm _ n => stringOfNat n
  | MicroopTerm _ uop => StringOf ["inst "; stringOfNat (globalID uop); " ";
      stringOfNat (coreID uop); " "; stringOfNat (threadID uop); " ";
      stringOfNat (intraInstructionID uop)]
  | NodeTerm _ n => GraphvizShortStringOfGraphNode n
  | EdgeTerm _ e => StringOfGraphEdge e
  | MacroArgTerm _ n => StringOfSoI n
  end.

Definition stringOfFOLTerm
  (t : FOLTerm)
  : string :=
  StringOf [FOLTermName t; " = ("; stringOfFOLTermValue t; ")"].

Fixpoint GetFOLTermHelper
  (name : string)
  (l : list FOLTerm)
  (depth : nat)
  : option FOLTerm :=
  match (depth, l) with
  | (S d, StageNameTerm s n::t) =>
      if beq_string s name
      then Some (IntTerm s n)
      else GetFOLTermHelper name t d
  | (S d, MacroArgTerm s1 s2::t) =>
      match s2 with
      | SoIString s2' =>
        if beq_string name s1
        then (if beq_string s1 s2'
          then GetFOLTermHelper name t d
          else GetFOLTermHelper s2' t d)
        else GetFOLTermHelper name t d
      | SoIInt n =>
        if beq_string s1 name
        then Some (IntTerm name n)
        else GetFOLTermHelper name t d
      | _ => Warning None ["Unexpected macro argument type"]
      end
  | (S d, h::t) =>
      if beq_string (FOLTermName h) name
      then Some h
      else GetFOLTermHelper name t d
  | (S d, []) => Warning None ["Could not find term "; name]
  | (O, _) => Warning None ["Term search recursion depth exceeded!"]
  end.

Definition GetFOLTerm
  (name : string)
  (l : list FOLTerm)
  : option FOLTerm :=
  let result := GetFOLTermHelper name l 1000 in
  match result with
  | Some r => if PrintFlag 8 then Comment result ["GetFOLTerm "; name; " returned "; stringOfFOLTerm r] else result
  | None => if PrintFlag 8 then Comment result ["GetFOLTerm "; name; " returned None"] else result
  end.

Record FOLState := mkFOLState {
  stateNodes     : list GraphNode;
  stateNotNodes  : list GraphNode;
  stateEdgeNodes : list GraphNode;
  stateEdges     : list GraphEdge;
  stateNotEdges  : list GraphEdge;
  statePreds     : list FOLSymPred;
  stateNotPreds  : list FOLSymPred;
  stateUops      : list Microop;
  stateInitial   : list BoundaryCondition;
  stateFinal     : list BoundaryCondition;
  stateArchEdges : list ArchitectureLevelEdge
}.

Fixpoint UpdateFOLState
  (check_dups : bool)
  (s : FOLState)
  (t : ScenarioTree)
  : FOLState :=
  let f a b :=
    if find (beq_edge b) a
    then a
    else b::a
  in
  let g a b :=
    if find (beq_node b) a
    then a
    else b::a
  in
  match t with
  | ScenarioName n t' => Warning s ["Shouldn't be trying to choose ScenarioName!"]
  | ScenarioConflict t' => UpdateFOLState check_dups s t'
  | ScenarioAnd a b => UpdateFOLState check_dups (UpdateFOLState check_dups s a) b
  | ScenarioOr a b => Warning s ["Shouldn't be trying to choose ScenarioOr!"]
  | ScenarioEdgeLeaf l =>
      let new_edges :=
        if check_dups
        then fold_left f l (stateEdges s)
        else app_rev (stateEdges s) l
      in
      let new_nodes := NodesFromEdges new_edges in
      mkFOLState (stateNodes s) (stateNotNodes s) new_nodes new_edges (stateNotEdges s)
        (statePreds s) (stateNotPreds s)
        (stateUops s) (stateInitial s) (stateFinal s) (stateArchEdges s)
  | ScenarioNotEdgeLeaf l =>
      let new_not_edges :=
        if check_dups
        then fold_left f l (stateNotEdges s)
        else app_rev (stateNotEdges s) l
      in
      mkFOLState (stateNodes s) (stateNotNodes s) (stateEdgeNodes s) (stateEdges s) new_not_edges
        (statePreds s) (stateNotPreds s)
        (stateUops s) (stateInitial s) (stateFinal s) (stateArchEdges s)
  | ScenarioNodeLeaf l =>
      let new_nodes := 
        if check_dups
        then fold_left g l (stateNodes s)
        else app_rev (stateNodes s) l
      in
      mkFOLState new_nodes (stateNotNodes s) (stateEdgeNodes s) (stateEdges s) (stateNotEdges s)
        (statePreds s) (stateNotPreds s)
        (stateUops s) (stateInitial s) (stateFinal s) (stateArchEdges s)
  | ScenarioNotNodeLeaf l =>
      let new_not_nodes := 
        if check_dups
        then fold_left g l (stateNotNodes s)
        else app_rev (stateNotNodes s) l
      in
      mkFOLState (stateNodes s) new_not_nodes (stateEdgeNodes s) (stateEdges s) (stateNotEdges s)
        (statePreds s) (stateNotPreds s)
        (stateUops s) (stateInitial s) (stateFinal s) (stateArchEdges s)
  | ScenarioPred p =>
      let new_preds := 
        if check_dups then
          if find (beq_pred p) (statePreds s) then
            statePreds s
          else
            p::(statePreds s)
        else p::(statePreds s)
      in
      mkFOLState (stateNodes s) (stateNotNodes s) (stateEdgeNodes s) (stateEdges s) (stateNotEdges s)
        new_preds (stateNotPreds s)
        (stateUops s) (stateInitial s) (stateFinal s) (stateArchEdges s)
  | ScenarioNotPred p =>
      let new_not_preds := 
        if check_dups then
          if find (beq_pred p) (stateNotPreds s) then
            stateNotPreds s
          else
            p::(stateNotPreds s)
        else p::(stateNotPreds s)
      in
      mkFOLState (stateNodes s) (stateNotNodes s) (stateEdgeNodes s) (stateEdges s) (stateNotEdges s)
        (statePreds s) new_not_preds
        (stateUops s) (stateInitial s) (stateFinal s) (stateArchEdges s)
  | ScenarioTrue => Warning s ["Shouldn't be trying to choose ScenarioTrue!"]
  | ScenarioFalse => Warning s ["Shouldn't be trying to choose ScenarioFalse!"]
  end.

Fixpoint blt_string
  (a b : string)
  : bool :=
  match (a, b) with
  | (String a1 a2, String b1 b2) =>
      if blt_nat (nat_of_ascii a1) (nat_of_ascii b1)
      then true
      else if beq_nat (nat_of_ascii a1) (nat_of_ascii b1)
      then blt_string a2 b2
      else false
  | (String a1 a2, EmptyString) => false
  | (EmptyString, String b1 b2) => true
  | (EmptyString, EmptyString) => false
  end.

Definition FOLStateReplaceEdges
  (s : FOLState)
  (n n' : list GraphNode)
  (l l': list GraphEdge)
  (p p': list FOLSymPred)
  : FOLState :=
  let nodes := NodesFromEdges l in
  mkFOLState n n' nodes l l' p p' (stateUops s) (stateInitial s)
    (stateFinal s) (stateArchEdges s).

Fixpoint GetSoIFOLTerm
  (t : StringOrInt)
  (l : list FOLTerm)
  : option FOLTerm :=
  let result :=
  match t with
  | SoISum a b =>
      match (GetSoIFOLTerm a l, GetSoIFOLTerm b l) with
      | (Some (IntTerm _ a'), Some (IntTerm _ b')) =>
          Some (IntTerm "" (a' + b'))
      | _ => None
      end
  | SoIString s => GetFOLTerm s l
  | SoIInt n => Some (IntTerm "" n)
  | SoICoreID s =>
      match GetFOLTerm s l with
      | Some (MicroopTerm _ uop) => Some (IntTerm "" (coreID uop))
      | _ => None
      end
  end in
  match result with
  | Some r => if PrintFlag 8 then Comment result ["GetSoIFOLTerm "; StringOfSoI t; " returned "; stringOfFOLTerm r] else result
  | None => if PrintFlag 8 then Comment result ["GetSoIFOLTerm "; StringOfSoI t; " returned None"] else result
  end.

Fixpoint FoldInstantiateGraphEdge
  (s : FOLState)
  (l : list FOLTerm)
  (r : option (list GraphEdge))
  (e : PredGraphEdge)
  : option (list GraphEdge) :=
  match e with
  | ((uop1name, (p1, l1)), (uop2name, (p2, l2)), label, color) =>
      match (GetFOLTerm uop1name l, GetFOLTerm uop2name l,
             GetSoIFOLTerm p1 l, GetSoIFOLTerm p2 l,
             GetSoIFOLTerm l1 l, GetSoIFOLTerm l2 l) with
      | (Some (MicroopTerm _ uop1), Some (MicroopTerm _ uop2),
         Some (IntTerm _ p1'), Some (IntTerm _ p2'),
         Some (IntTerm _ l1'), Some (IntTerm _ l2')) =>
          let e  := ((uop1, (p1', l1')), (uop2, (p2', l2')), label, color) in
          match r with
          | Some r' => Some (e :: r')
          | None => None
          end
      | _ => Warning None ["Could not find microop terms "; uop1name;
          " and/or "; uop2name]
      end
  end.

Fixpoint FoldInstantiateGraphNode
  (s : FOLState)
  (l : list FOLTerm)
  (r : option (list GraphNode))
  (n : PredGraphNode)
  : option (list GraphNode) :=
  match n with
  | (uopname, (p1, l1)) =>
      match (GetFOLTerm uopname l, GetSoIFOLTerm p1 l, GetSoIFOLTerm l1 l) with
      | (Some (MicroopTerm _ uop), Some (IntTerm _ p'), Some (IntTerm _ l')) =>
          let n := (uop, (p', l')) in
          match r with
          | Some r' => Some (n :: r')
          | None => None
          end
      | _ => Warning None ["Could not find term "; uopname]
      end
  end.

Fixpoint GetInitialCondition
  (conditions : list BoundaryCondition)
  (pa : PhysicalAddress)
  : Data :=
  match conditions with
  | (a, d) :: t =>
      if beq_paddr a pa
      then d
      else GetInitialCondition t pa
  | [] =>
      let result := NormalData 0 in
      if PrintFlag 6
      then Comment result
        ["Using implicit initial condition data=0 for PA: ";
        GraphvizStringOfPhysicalAddress pa]
      else result
  end.

Fixpoint GetFinalCondition
  (conditions : list BoundaryCondition)
  (pa : PhysicalAddress)
  : option Data :=
  match conditions with
  | (a, d) :: t =>
      if beq_paddr a pa
      then Some d
      else GetFinalCondition t pa
  | [] => None
  end.

Fixpoint HasDependency
  (l : list ArchitectureLevelEdge)
  (src dst : nat)
  (label : string)
  : bool :=
  match l with
  | (h1, h2, h3)::t =>
      if andb (andb (beq_nat h1 src) (beq_nat h2 dst))
        (beq_string label h3)
      then true
      else HasDependency t src dst label
  | [] => false
  end.

Definition EvaluatePredicate
  (stage_names : list (list string))
  (p : FOLPredicateType)
  (l : list FOLTerm)
  (s : FOLState)
  : option (list GraphNode * list GraphEdge) :=
  let result := match p with
  | PredDebug a => Some ([], [])
  | PredHasDependency a b c =>
      match (GetFOLTerm b l, GetFOLTerm c l) with
      | (Some (MicroopTerm _ b'), Some (MicroopTerm _ c')) =>
          if HasDependency (stateArchEdges s) (globalID b') (globalID c') a
          then Some ([], [])
          else None
      | _ => None
      end
  | PredIsRead t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          match access t' with
          | Read _ _ _ _ => Some ([], [])
          | _ => None
          end
      | _ => None
      end
  | PredIsAPICAccess n t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          match access t' with
          | Read _ _ (PA (APICTag s' _) _) _ =>
              if beq_string n s' then Some ([], []) else None
          | Write _ _ (PA (APICTag s' _) _) _ =>
              if beq_string n s' then Some ([], []) else None
          | _ => None
          end
      | _ => None
      end
  | PredIsWrite t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          match access t' with
          | Write _ _ _ _ => Some ([], [])
          | _ => None
          end
      | _ => None
      end
  | PredIsFence t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          match access t' with
          | Fence _ => Some ([], [])
          | FenceVA _ _ => Some ([], [])
          | _ => None
          end
      | _ => None
      end
  | PredAccessType t1 t2 =>
      match GetFOLTerm t2 l with
      | Some (MicroopTerm _ t2') =>
          match access t2' with
          | Read t1' _ _ _ =>
              if find_string t1 t1'
              then Some ([], [])
              else None
          | Write t1' _ _ _ =>
              if find_string t1 t1'
              then Some ([], [])
              else None
          | Fence t1' =>
              if find_string t1 t1'
              then Some ([], [])
              else None
          | FenceVA t1' _ =>
              if find_string t1 t1'
              then Some ([], [])
              else None
          end
      | _ => None
      end
  | PredSameUop t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_uop t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredSameCore t1 t2 =>
      match (GetSoIFOLTerm t1 l, GetSoIFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_nat (coreID t1') (coreID t2')
          then Some ([], [])
          else None
      | (Some (IntTerm _ t1'), Some (IntTerm _ t2')) =>
          if beq_nat t1' t2'
          then Some ([], [])
          else None
      | _ => None
      end
  | PredOnCore t1 t2 =>
      match (GetSoIFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (IntTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_nat t1' (coreID t2')
          then Some ([], [])
          else None
      | _ => Warning None ["Could not find term "; StringOfSoI t1; " and/or "; t2]
      end
  | PredSameThread t1 t2 =>
      match (GetSoIFOLTerm t1 l, GetSoIFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_nat (coreID t1') (coreID t2')
          then Some ([], [])
          else None
      | (Some (IntTerm _ t1'), Some (IntTerm _ t2')) =>
          if beq_nat t1' t2'
          then Some ([], [])
          else None
      | _ => None
      end
  | PredSmallerGlobalID t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if blt_nat (globalID t1') (globalID t2')
          then Some ([], [])
          else None
      | _ => None
      end
  | PredSameGlobalID t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_nat (globalID t1') (globalID t2')
          then Some ([], [])
          else None
      | _ => None
      end
  | PredSameIntraInstID t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_nat (intraInstructionID t1') (intraInstructionID t2')
          then Some ([], [])
          else None
      | _ => None
      end
  | PredOnThread t1 t2 =>
      match (GetSoIFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (IntTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_nat t1' (threadID t2')
          then Some ([], [])
          else None
      | _ => Warning None ["Could not find term "; StringOfSoI t1; " and/or "; t2]
      end
  | PredSameNode t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (NodeTerm _ t1'), Some (NodeTerm _ t2')) =>
          if beq_node t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredSameVirtualAddress t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if SameVirtualAddress t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredSamePhysicalAddress t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if SamePhysicalAddress t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredSameVirtualTag t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if SameVirtualTag t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredSamePhysicalTag t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if SamePhysicalTag t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredSameIndex t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if SameIndex t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredKnownData t1 =>
      match (GetFOLTerm t1 l) with
      | Some (MicroopTerm _ t1') =>
          match access t1' with
          | Read _ _ _ UnknownData => None
          | _ => Some ([], [])
          end
      | _ => None
      end
  | PredSameData t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if SameData t1' t2' then Some ([], []) else None
      | _ => None
      end
  | PredSamePAasPTEforVA t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          match (GetPhysicalAddress t1', GetVirtualTag t2') with
          | (Some p1, Some v2) =>
              if beq_paddr p1 (PA (PTETag v2) 0)
              then Some ([], [])
              else None
          | _ => None
          end
      | _ => None
      end
  | PredDataIsCorrectTranslation a' d' t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          match (GetData t1', GetVirtualTag t2', GetPhysicalTag t2') with
          | (Some d, Some v, Some p) =>
              if beq_pte d v p a' d'
              then Some ([], [])
              else None
          | _ => None
          end
      | _ => None
      end
  | PredTranslationMatchesInitialState a' d' t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          match (GetVirtualTag t', GetPhysicalTag t') with
          | (Some v, Some p) =>
              let ic :=
                GetInitialCondition (stateInitial s) (PA (PTETag v) 0) in
              if beq_pte ic v p a' d'
              then Some ([], [])
              else None
          | _ => None
          end
      | _ => None
      end
  | PredDataFromPAInitial t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          match (GetData t', GetPhysicalAddress t') with
          | (Some d, Some pa) =>
              if beq_data d (GetInitialCondition (stateInitial s) pa)
              then Some ([], [])
              else None
          | _ => None
          end
      | _ => None
      end
  | PredDataFromPAFinal t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          match (GetData t', GetPhysicalAddress t') with
          | (Some d, Some pa) =>
              match GetFinalCondition (stateFinal s) pa with
              | Some d' =>
                if beq_data d d'
                then Some ([], [])
                else None
              | None => None
              end
          | _ => None
          end
      | _ => None
      end
  | PredConsec t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if andb (beq_nat (S (globalID t1')) (globalID t2'))
            (andb (beq_nat (threadID t1') (threadID t2'))
              (beq_nat (coreID t1') (coreID t2')))
          then Some ([], [])
          else None
      | _ => None
      end
  | PredProgramOrder t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ b'), Some (MicroopTerm _ c')) =>
          if HasDependency (stateArchEdges s) (globalID b') (globalID c') "po"
          then Some ([], [])
          else None
      | _ => None
      end
  | PredAddEdges e
  | PredEdgesExist e =>
      match fold_left (FoldInstantiateGraphEdge s l) e (Some []) with
      | Some l' => Some ([], l')
      | None => None
      end
  | PredNodesExist n =>
      match fold_left (FoldInstantiateGraphNode s l) n (Some []) with
      | Some l' => Some (l', [])
      | None => None
      end
  | PredTrue => Some ([], [])
  | PredFalse => None
  | PredHasID g c t i n =>
      match GetFOLTerm n l with
      | Some (MicroopTerm _ uop) =>
          match uop with
          | mkMicroop g' c' t' i' _ =>
              if andb
                (andb (beq_nat g g') (beq_nat c c'))
                (andb (beq_nat t t') (beq_nat i i'))
              then Some ([], [])
              else None
          end
      | _ => None
      end
  | PredHasGlobalID g n =>
      match GetFOLTerm n l with
      | Some (MicroopTerm _ uop) =>
          match uop with
          | mkMicroop g' _ _ _ _ =>
              if beq_nat g g'
              then Some ([], [])
              else None
          end
      | _ => None
      end
  end in
  if PrintFlag 8
  then Comment result [tab; "// EvaluatePredicate "; stringOfPredicate false p; " returned ";
    match result with
    | Some (l1, l2) => StringOf ["sat("; stringOfNat (List.length l1); " nodes, ";
        stringOfNat (List.length l2); " edges)"]
    | None => "unsat"
    end]
  else result.

Definition FOLQuantifier := FOLState -> list FOLTerm -> (string * list FOLTerm).

Definition MicroopQuantifier
  (name : string)
  : FOLQuantifier :=
  fun (s : FOLState) (l : list FOLTerm) =>
  let uops := stateUops s in
  (name, Map (fun x => MicroopTerm name x) uops).

Definition NodeQuantifier
  (name : string)
  : FOLQuantifier :=
  fun (s : FOLState) (l : list FOLTerm) =>
  let nodes := stateNodes s in
  (name, Map (fun x => NodeTerm name x) nodes).

(* Dummy quantifier for a single uop. *)
Definition DummyQuantifier
  (name : string)
  (a : Microop)
  : FOLQuantifier :=
  fun (s : FOLState) (l : list FOLTerm) =>
    (name, [MicroopTerm name a]).

Fixpoint numCores
  (l : list Microop)
  (n : nat)
  : nat :=
  match l with
  | h::t => numCores t (max n (S (coreID h)))
  | [] => n
  end.

Definition CoreQuantifier
  (name : string)
  : FOLQuantifier :=
  fun (s : FOLState) (l : list FOLTerm) =>
  let cores := numCores (stateUops s) 0 in
  (name, Map (fun x => IntTerm name x) (Range cores)).

Fixpoint numThreads
  (l : list Microop)
  (n : nat)
  : nat :=
  match l with
  | h::t => numThreads t (max n (S (threadID h)))
  | [] => n
  end.

Definition ThreadQuantifier
  (name : string)
  : FOLQuantifier :=
  fun (s : FOLState) (l : list FOLTerm) =>
  let cores := numThreads (stateUops s) 0 in
  (name, Map (fun x => IntTerm name x) (Range cores)).

Inductive FOLFormula :=
| FOLName : string -> FOLFormula -> FOLFormula
| FOLExpandMacro : string -> list StringOrInt -> FOLFormula
| FOLPredicate : FOLPredicateType -> FOLFormula
| FOLNot : FOLFormula -> FOLFormula
| FOLOr : FOLFormula -> FOLFormula -> FOLFormula
| FOLAnd : FOLFormula -> FOLFormula -> FOLFormula
| FOLForAll : FOLQuantifier -> FOLFormula -> FOLFormula
| FOLExists : FOLQuantifier -> FOLFormula -> FOLFormula
| FOLLet : FOLTerm -> FOLFormula -> FOLFormula.

Fixpoint stringOfFOLFormulaHelper
  (n : nat)
  (depth : nat)
  (f : FOLFormula)
  : string :=
  match n with
  | S n' =>
      match f with
      | FOLName s f => StringOf ["("; s; ":(";
          stringOfFOLFormulaHelper n' (S depth) f; "))"]
      | FOLExpandMacro s l => StringOf ["ExpandMacro "; s]
      | FOLPredicate p => stringOfPredicate false p
      | FOLNot f' => StringOf ["~("; stringOfNat depth; ")(";
          stringOfFOLFormulaHelper n' (S depth) f'; ")"]
      | FOLOr a b =>
          StringOf ["("; stringOfFOLFormulaHelper n' (S depth) a; ") \";
            stringOfNat depth ; "/ (";
            stringOfFOLFormulaHelper n' (S depth) b; ")"]
      | FOLAnd a b =>
          StringOf ["("; stringOfFOLFormulaHelper n' (S depth) a; ") /";
            stringOfNat depth; "\ (";
            stringOfFOLFormulaHelper n' (S depth) b; ")"]
      | FOLForAll q f' =>
          StringOf ["forall("; stringOfNat depth; ") (...), (";
            stringOfFOLFormulaHelper n' (S depth) f'; ")"]
      | FOLExists q f' =>
          StringOf ["exists("; stringOfNat depth; ") (...), (";
            stringOfFOLFormulaHelper n' (S depth) f'; ")"]
      | FOLLet t f' =>
          StringOf ["let("; stringOfNat depth; ") "; stringOfFOLTerm t;
            " in ("; stringOfFOLFormulaHelper n' (S depth) f'; ")"]
      end
  | O =>
      match f with
      | FOLName s f' => s
      | FOLExpandMacro s l => StringOf ["ExpandMacro "; s]
      | FOLPredicate p => stringOfPredicate false p
      | FOLNot f' => "~(...)"
      | FOLOr a b => "(...) \/ (...)"
      | FOLAnd a b => "(...) /\ (...)"
      | FOLForAll q f' => "forall (...), (...)"
      | FOLExists q f' => "exists (...), (...)"
      | FOLLet t f' => StringOf ["let "; stringOfFOLTerm t; " in (...)"]
      end
  end.

Definition stringOfFOLFormula
  (depth : nat)
  (f : FOLFormula)
  : string :=
  stringOfFOLFormulaHelper 3 depth f.

Fixpoint PrintGraphvizStringOfFOLFormulaHelper
  (id : nat)
  (f : FOLFormula)
  : nat :=
  match f with
  | FOLName s f' =>
      let id' := PrintGraphvizStringOfFOLFormulaHelper id f' in
      let result := S id' in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat id'; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " [color=red,shape=box,label="""; s; """];"] in
      result
  | FOLExpandMacro s l =>
      Println id ["  n"; stringOfNat id; " [label="""; s; """];"]
  | FOLPredicate p =>
      Println id
        ["  n"; stringOfNat id; " [label="""; stringOfPredicate true p; """];"]
  | FOLNot f' =>
      let id' := PrintGraphvizStringOfFOLFormulaHelper id f' in
      let result := S id' in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat id'; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " [label=""NOT""];"] in
      result
  | FOLOr a b =>
      let a_id := PrintGraphvizStringOfFOLFormulaHelper      id  a in
      let b_id := PrintGraphvizStringOfFOLFormulaHelper (S a_id) b in
      let result := S b_id in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat a_id; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat b_id; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " [label=""OR""];"] in
      result
  | FOLAnd a b =>
      let a_id := PrintGraphvizStringOfFOLFormulaHelper      id  a in
      let b_id := PrintGraphvizStringOfFOLFormulaHelper (S a_id) b in
      let result := S b_id in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat a_id; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat b_id; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " [label=""AND""];"] in
      result
  | FOLForAll q f' =>
      let id' := PrintGraphvizStringOfFOLFormulaHelper id f' in
      let result := S id' in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat id'; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " [label=""forall ...""];"] in
      result
  | FOLExists q f' =>
      let id' := PrintGraphvizStringOfFOLFormulaHelper id f' in
      let result := S id' in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat id'; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " [label=""exists ...""];"] in
      result
  | FOLLet t f' =>
      let id' := PrintGraphvizStringOfFOLFormulaHelper id f' in
      let result := S id' in
      let result := Println result
        ["  n"; stringOfNat result; " -> n"; stringOfNat id'; ";"] in
      let result := Println result
        ["  n"; stringOfNat result; " [color=green,shape=box,label="""; stringOfFOLTerm t; """];"] in
      result
  end.

Definition PrintGraphvizStringOfFOLFormula
  (f : FOLFormula)
  : FOLFormula :=
  if PrintFlag 5
  then
    let f := Println f ["digraph Axioms {"] in
    let f := Println f [tab; "layout=dot;"] in
    let result := PrintGraphvizStringOfFOLFormulaHelper 0 f in
    Println f ["} // "; stringOfNat result; " nodes"; newline]
  else f.

Definition FOLImplies
  (a b : FOLFormula)
  : FOLFormula :=
  FOLOr (FOLNot a) b.

Definition FOLIff
  (a b : FOLFormula)
  : FOLFormula :=
  FOLAnd (FOLImplies a b) (FOLImplies b a).

Definition FoldFlipEdge
  (is_neg : bool)
  (t : ScenarioTree)
  (e : GraphEdge)
  : ScenarioTree :=
  match e with
  | (s, d, l, c) =>
      let l' :=
        if string_prefix "NOT_" l
        then substr 4 l
        else append "NOT_" l in
      if beq_node s d
      then ScenarioOr t ScenarioTrue
      else
        if is_neg then
          ScenarioOr t (ScenarioEdgeLeaf [e])
        else
          ScenarioOr t (ScenarioNotEdgeLeaf [e])
      (* else ScenarioOr t
        (ScenarioOr
          (ScenarioOr (ScenarioNotNodeLeaf [s]) (ScenarioNotNodeLeaf [d]))
          (ScenarioEdgeLeaf [(d, s, l', c)])) *)
  end.

Definition FoldFlipNode
  (is_neg : bool)
  (t : ScenarioTree)
  (n : GraphNode)
  : ScenarioTree :=
  if is_neg then
      ScenarioOr t (ScenarioNodeLeaf [n])
  else
      ScenarioOr t (ScenarioNotNodeLeaf [n]).

Definition CreateSymbolicScenarioTree
  (p : FOLPredicateType)
  (l : list FOLTerm)
  (s : FOLState)
  : ScenarioTree :=
  match p with
  | PredDebug a => ScenarioTrue
  | PredHasDependency a b c =>
      match (GetFOLTerm b l, GetFOLTerm c l) with
      | (Some (MicroopTerm _ b'), Some (MicroopTerm _ c')) =>
            ScenarioPred (SymPredHasDependency b' c' (GetISAEdge a))
      | _ => ScenarioFalse
      end
  | PredIsRead t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          ScenarioPred (SymPredIsRead t')
      | _ => ScenarioFalse
      end
  | PredIsWrite t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          ScenarioPred (SymPredIsWrite t')
      | _ => ScenarioFalse
      end
  | PredIsAPICAccess n t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          ScenarioPred (SymPredIsAPICAccess t' n)
      | _ => ScenarioFalse
      end
  | PredIsFence t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          ScenarioPred (SymPredIsFence t')
      | _ => ScenarioFalse
      end
  | PredAccessType t1 t2 =>
      match GetFOLTerm t2 l with
      | Some (MicroopTerm _ t2') =>
          ScenarioPred (SymPredAccessType t2' t1)
      | _ => ScenarioFalse
      end
  | PredSameUop t1 t2 =>
      (* This one is actually evaluated to true or false...*)
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_uop t1' t2' then ScenarioTrue else ScenarioFalse
      | _ => ScenarioFalse
      end
      (* as is this one... *)
  | PredSameNode t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (NodeTerm _ t1'), Some (NodeTerm _ t2')) =>
          if beq_node t1' t2' then ScenarioTrue else ScenarioFalse
      | _ => ScenarioFalse
      end
      (* I've never seen SameCore used with ints, so I'm not covering that case...*)
  | PredSameCore t1 t2 =>
      match (GetSoIFOLTerm t1 l, GetSoIFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          ScenarioPred (SymPredSameCore t1' t2')
      | _ => ScenarioFalse
      end
  (* These next two can be evaluated to true/false as well, since
     they only use the global ID of the microops. *)
  | PredSmallerGlobalID t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if blt_nat (globalID t1') (globalID t2')
          then ScenarioTrue
          else ScenarioFalse
      | _ => ScenarioFalse
      end
  | PredSameGlobalID t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          if beq_nat (globalID t1') (globalID t2')
          then ScenarioTrue
          else ScenarioFalse
      | _ => ScenarioFalse
      end
  | PredSameIntraInstID t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          ScenarioPred (SymPredSameIntraInstID t1' t2')
      | _ => ScenarioFalse
      end
      (* SameThread with int terms is also not covered. *)
  | PredSameThread t1 t2 =>
      match (GetSoIFOLTerm t1 l, GetSoIFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          ScenarioPred (SymPredSameThread t1' t2')
      | _ => ScenarioFalse
      end
  | PredOnCore t1 t2 =>
      match (GetSoIFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (IntTerm _ t1'), Some (MicroopTerm _ t2')) =>
          ScenarioPred (SymPredOnCore t2' t1')
      | _ => Warning ScenarioFalse ["Could not find term "; StringOfSoI t1; " and/or "; t2]
      end
  | PredOnThread t1 t2 =>
      match (GetSoIFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (IntTerm _ t1'), Some (MicroopTerm _ t2')) =>
          ScenarioPred (SymPredOnThread t2' t1')
      | _ => Warning ScenarioFalse ["Could not find term "; StringOfSoI t1; " and/or "; t2]
      end
  | PredSameVirtualAddress t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          ScenarioPred (SymPredSameVirtualAddress t1' t2')
      | _ => ScenarioFalse
      end
  | PredSamePhysicalAddress t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          ScenarioPred (SymPredSamePhysicalAddress t1' t2')
      | _ => ScenarioFalse
      end
  | PredSameVirtualTag t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          ScenarioPred (SymPredSameVirtualTag t1' t2')
      | _ => ScenarioFalse
      end
  | PredSamePhysicalTag t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          ScenarioPred (SymPredSamePhysicalTag t1' t2')
      | _ => ScenarioFalse
      end
  | PredSameIndex t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          ScenarioPred (SymPredSameIndex t1' t2')
      | _ => ScenarioFalse
      end
  (* KnownData doesn't need to be used, but it could be useful.
     We can set it to true for anything with an rf, and false otherwise. *)
  | PredKnownData t1 =>
      match (GetFOLTerm t1 l) with
      | Some (MicroopTerm _ t1') =>
          ScenarioPred (SymPredKnownData t1')
      | _ => ScenarioFalse
      end
  | PredSameData t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          ScenarioPred (SymPredSameData t1' t2')
      | _ => ScenarioFalse
      end
  | PredDataFromPAInitial t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          ScenarioPred (SymPredDataFromPAInitial t')
      | _ => ScenarioFalse
      end
  | PredDataFromPAFinal t =>
      match GetFOLTerm t l with
      | Some (MicroopTerm _ t') =>
          ScenarioPred (SymPredDataFromPAFinal t')
      | _ => ScenarioFalse
      end
  | PredSamePAasPTEforVA t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          ScenarioPred (SymPredSamePAasPTEforVA t1' t2')
      | _ => ScenarioFalse
      end
  | PredProgramOrder t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ b'), Some (MicroopTerm _ c')) =>
          ScenarioPred (SymPredProgramOrder b' c')
      | _ => ScenarioFalse
      end
  | PredConsec t1 t2 =>
      match (GetFOLTerm t1 l, GetFOLTerm t2 l) with
      | (Some (MicroopTerm _ t1'), Some (MicroopTerm _ t2')) =>
          ScenarioPred (SymPredConsec t1' t2')
      | _ => ScenarioFalse
      end
  | PredTrue => ScenarioTrue
  | PredFalse => ScenarioFalse
  | PredDataIsCorrectTranslation _ _ _ _ => Warning ScenarioFalse ["Symbolic DataIsCorrectTranslation is unsupported"]
  | PredTranslationMatchesInitialState _ _ _ => Warning ScenarioFalse ["Symbolic TranslationMatchesInitialState is unsupported"]
  | PredAddEdges _ => Warning ScenarioFalse ["Symbolic AddEdges is unsupported"]
  | PredEdgesExist _ => Warning ScenarioFalse ["Symbolic EdgesExist is unsupported"]
  | PredNodesExist _ => Warning ScenarioFalse ["Symbolic NodesExist is unsupported"]
  | PredHasID _ _ _ _ _ => Warning ScenarioFalse ["Symbolic HasID is unsupported"]
  | PredHasGlobalID _ _ => Warning ScenarioFalse ["Symbolic HasGlobalID is unsupported"]
  end.

Fixpoint EliminateQuantifiersHelper
  (symbolic : bool)
  (over_approx : bool)
  (demorgan : bool)
  (stage_names : list (list string))
  (s : FOLState)
  (f : FOLFormula)
  (l : list FOLTerm)
  : ScenarioTree :=
  match f with
  | FOLName n f =>
      ScenarioName n (EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s f l)
  | FOLExpandMacro m _ => Warning ScenarioFalse
      ["Internal error: macro "; m; " should have been expanded!"]
  | FOLPredicate p  =>
    if symbolic then
      match p with
      | PredAddEdges p'
      | PredEdgesExist p'
      | PredNodesExist p' =>
        match (demorgan, EvaluatePredicate stage_names p l s) with
        | (false, Some (l1, l2)) =>
            ScenarioAnd (ScenarioNodeLeaf l1) (ScenarioEdgeLeaf l2)
        | (false, None) => ScenarioFalse
        | (true, Some (l1, l2)) =>
            let n := fold_left (FoldFlipNode false) l1 ScenarioFalse in
            let e := fold_left (FoldFlipEdge false) l2 ScenarioFalse in
            ScenarioOr n e
        | (true, None) => ScenarioTrue
        end
      | _ => let t := CreateSymbolicScenarioTree p l s in
             match t with
             | ScenarioPred p' => if demorgan then ScenarioNotPred p' else t
             | ScenarioTrue => if demorgan then ScenarioFalse else t
             | ScenarioFalse => if demorgan then ScenarioTrue else t
             | _ => Warning ScenarioFalse ["Symbolic scenario tree returned something other than pred/true/false!"]
             end
      end
    else
      match (demorgan, EvaluatePredicate stage_names p l s) with
      | (false, Some (l1, l2)) =>
          ScenarioAnd (ScenarioNodeLeaf l1) (ScenarioEdgeLeaf l2)
      | (false, None) => ScenarioFalse
      | (true, Some (l1, l2)) =>
          let n := fold_left (FoldFlipNode false) l1 ScenarioFalse in
          let e := fold_left (FoldFlipEdge false) l2 ScenarioFalse in
          ScenarioOr n e
      | (true, None) => ScenarioTrue
      end
  | FOLNot f' =>
      EliminateQuantifiersHelper symbolic over_approx (negb demorgan) stage_names s f' l
  | FOLOr a b =>
      if demorgan
      then
        match (EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s a l) with
        | ScenarioFalse => ScenarioFalse
        | ScenarioTrue =>
          (EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s b l)
        | a' =>
          match (EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s b l) with
          | ScenarioFalse => ScenarioFalse
          | ScenarioTrue => a'
          | b' => ScenarioAnd a' b'
          end
        end
      else
        match (EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s a l) with
        | ScenarioTrue => ScenarioTrue
        | ScenarioFalse =>
          (EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s b l)
        | a' =>
          match (EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s b l) with
          | ScenarioTrue => ScenarioTrue
          | ScenarioFalse => a'
          | b' => ScenarioOr a' b'
          end
        end
  | FOLAnd a b =>
      if negb demorgan
      then
        match (EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s a l) with
        | ScenarioFalse => ScenarioFalse
        | ScenarioTrue =>
          (EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s b l)
        | a' =>
          match (EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s b l) with
          | ScenarioFalse => ScenarioFalse
          | ScenarioTrue => a'
          | b' => ScenarioAnd a' b'
          end
        end
      else
        match (EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s a l) with
        | ScenarioTrue => ScenarioTrue
        | ScenarioFalse =>
          (EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s b l)
        | a' =>
          match (EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s b l) with
          | ScenarioTrue => ScenarioTrue
          | ScenarioFalse => a'
          | b' => ScenarioOr a' b'
          end
        end
  | FOLForAll t f'  =>
    if andb (over_approx) (demorgan) then
      ScenarioTrue
    else
      let (term_name, terms) := t s l in
      let case x y :=
        if demorgan
        then
          match x with
          | ScenarioTrue => ScenarioTrue
          | ScenarioFalse =>
            let y' := EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s f' (AddTerm l y) in
            ScenarioName (stringOfFOLTerm y) y'
          | _ =>
            match EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s f' (AddTerm l y) with
            | ScenarioTrue => ScenarioTrue
            | ScenarioFalse => x
            | y' => ScenarioOr x (ScenarioName (stringOfFOLTerm y) y')
            end
          end
        else
          match x with
          | ScenarioFalse => ScenarioFalse
          | ScenarioTrue =>
            let y' := EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s f' (AddTerm l y) in
            ScenarioName (stringOfFOLTerm y) y'
          | _ =>
            match EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s f' (AddTerm l y) with
            | ScenarioFalse => ScenarioFalse
            | ScenarioTrue => x
            | y' => ScenarioAnd x (ScenarioName (stringOfFOLTerm y) y')
            end
          end in
      fold_left case terms (if demorgan then ScenarioFalse else ScenarioTrue)
  | FOLExists t f'  =>
    if andb (over_approx) (negb demorgan) then
      ScenarioTrue
    else
      let (term_name, terms) := t s l in
      let case x y :=
        if negb demorgan
        then
          match x with
          | ScenarioTrue => ScenarioTrue
          | ScenarioFalse =>
            let y' := EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s f' (AddTerm l y) in
            ScenarioName (stringOfFOLTerm y) y'
          | _ =>
            match EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s f' (AddTerm l y) with
            | ScenarioTrue => ScenarioTrue
            | ScenarioFalse => x
            | y' => ScenarioOr x (ScenarioName (stringOfFOLTerm y) y')
            end
          end
        else
          match x with
          | ScenarioFalse => ScenarioFalse
          | ScenarioTrue =>
            let y' := EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s f' (AddTerm l y) in
            ScenarioName (stringOfFOLTerm y) y'
          | _ =>
            match EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s f' (AddTerm l y) with
            | ScenarioFalse => ScenarioFalse
            | ScenarioTrue => x
            | y' => ScenarioAnd x (ScenarioName (stringOfFOLTerm y) y')
            end
          end in
      fold_left case terms (if demorgan then ScenarioTrue else ScenarioFalse)
  | FOLLet t f' =>
      let t' := EliminateQuantifiersHelper symbolic over_approx demorgan stage_names s f' (AddTerm l t) in
      ScenarioName (stringOfFOLTerm t) t'
  end.

Fixpoint SetIntersectionIsEmpty
  (a b : list GraphEdge)
  : bool :=
  match a with
  | h::t =>
      if find (beq_edge h) b
      then false
      else SetIntersectionIsEmpty t b
  | [] => true
  end.

Fixpoint PredSetIntersectionIsEmpty
  (a b : list FOLSymPred)
  : bool :=
  match a with
  | h::t =>
      if find (beq_pred h) b
      then false
      else PredSetIntersectionIsEmpty t b
  | [] => true
  end.

Fixpoint SetIntersectionHelper
  (a b : list GraphEdge)
  (r : list GraphEdge)
  : list GraphEdge :=
  match a with
  | h::t =>
      if find (beq_edge h) b
      then SetIntersectionHelper t b (h::r)
      else SetIntersectionHelper t b r
  | [] => r
  end.

Definition SetIntersection
  (a b : list GraphEdge)
  : list GraphEdge :=
  SetIntersectionHelper a b [].

(** If a match is found, then pick which to keep according to the following
list of priorities:
1) Labeled edges
2) TC
3) Flipped edges
*)
Fixpoint SDFindEdge
  (e : GraphEdge)
  (l : list GraphEdge)
  : option GraphEdge :=
  match l with
  | h::t =>
      if beq_edge h e
      then
        match (h, e) with
        | ((hs, hd, hl, hc), (es, ed, el, ec)) =>
          match (beq_string "TC" hl, string_prefix "NOT_" hl,
            beq_string "TC" el, string_prefix "NOT_" el) with
          | (true, true, _, _) => Warning None
              ["TC and NOT_ simultaneously?"]
          | (_, _, true, true) => Warning None
              ["TC and NOT_ simultaneously?"]
          | (false, false, _, _) => None
          | (true, _, false, false) => Some e
          | (true, _, _, _) => None
          | (_, true, false, true) => None
          | (_, true, _, false) => Some e
          end
        end
      else SDFindEdge e t
  | [] => Some e
  end.

Fixpoint SetDifferenceHelper
  (a b r : list GraphEdge)
  : list GraphEdge :=
  match a with
  | h::t =>
      match SDFindEdge h b with
      | Some e => SetDifferenceHelper t b (e::r)
      | None => SetDifferenceHelper t b r
      end
  | [] => r
  end.

Definition SetDifference
  (a b : list GraphEdge)
  : list GraphEdge :=
  SetDifferenceHelper a b [].

Fixpoint NodeSetIntersectionIsEmpty
  (a b : list GraphNode)
  : bool :=
  match a with
  | h::t =>
      if find (beq_node h) b
      then false
      else NodeSetIntersectionIsEmpty t b
  | [] => true
  end.

Fixpoint NodeSetIntersectionHelper
  (a b : list GraphNode)
  (r : list GraphNode)
  : list GraphNode :=
  match a with
  | h::t =>
      if find (beq_node h) b
      then NodeSetIntersectionHelper t b (h::r)
      else NodeSetIntersectionHelper t b r
  | [] => r
  end.

Fixpoint NodeSetIntersection
  (a b : list GraphNode)
  : list GraphNode :=
  NodeSetIntersectionHelper a b [].

Fixpoint NodeSetDifferenceHelper
  (a b r : list GraphNode)
  : list GraphNode :=
  match a with
  | h::t =>
      if find (beq_node h) b
      then NodeSetDifferenceHelper t b r
      else NodeSetDifferenceHelper t b (h::r)
  | [] => r
  end.

Definition NodeSetDifference
  (a b : list GraphNode)
  : list GraphNode :=
  NodeSetDifferenceHelper a b [].

Fixpoint ScenarioTreeKeepIfFalse
  (s : FOLState)
  (t : ScenarioTree)
  : option ScenarioTree :=
  match t with
  | ScenarioName n t' =>
      match ScenarioTreeKeepIfFalse s t' with
      | Some t'' => Some (ScenarioName n t'')
      | None => None
      end
  | ScenarioConflict t' =>
      match ScenarioTreeKeepIfFalse s t' with
      | Some t'' => Some (ScenarioConflict t'')
      | None => None
      end
  | ScenarioEdgeLeaf l =>
      match (SetIntersection (FlipEdges l) (stateEdges s), SetIntersection l (stateNotEdges s)) with
      | ([], []) => None
      | (l', []) => Some (ScenarioEdgeLeaf (FlipEdges l'))
      | ([], l') => Some (ScenarioEdgeLeaf l')
      | (l1, l2) => Some (ScenarioEdgeLeaf (app_rev (FlipEdges l1) l2))
      end
  | ScenarioNotEdgeLeaf l =>
      match SetIntersection l (stateEdges s) with
      | [] => None
      | l' => Some (ScenarioNotEdgeLeaf l')
      end
  | ScenarioNodeLeaf l =>
      match NodeSetIntersection l (stateNotNodes s) with
      | [] => None
      | l' => Some (ScenarioNodeLeaf l')
      end
  | ScenarioNotNodeLeaf l =>
      match (NodeSetIntersection l (stateNodes s),
        NodeSetIntersection l (stateEdgeNodes s)) with
      | ([], []) => None
      | (l', []) => Some (ScenarioNotNodeLeaf l')
      | ([], l') => Some (ScenarioNotNodeLeaf l')
      | (l1, l2) => Some (ScenarioNotNodeLeaf (app_rev l1 l2))
      end
  | ScenarioPred p => None
  | ScenarioNotPred p => None
  | ScenarioAnd a b =>
      match (ScenarioTreeKeepIfFalse s a, ScenarioTreeKeepIfFalse s b) with
      | (Some a', Some b') => Some (ScenarioAnd a' b')
      | (None, Some b') => Some b'
      | (Some a', None) => Some a'
      | (None, None) => None
      end
  | ScenarioOr a b =>
      match (ScenarioTreeKeepIfFalse s a, ScenarioTreeKeepIfFalse s b) with
      | (Some a', Some b') => Some (ScenarioOr a' b')
      | (None, Some b') => None
      | (Some a', None) => None
      | (None, None) => None
      end
  | ScenarioTrue => None
  | ScenarioFalse => Some ScenarioFalse
  end.

Definition EliminateQuantifiers
  (symbolic : bool)
  (over_approx : bool)
  (stage_names : list (list string))
  (s : FOLState)
  (f : FOLFormula)
  (l : list FOLTerm)
  : ScenarioTree :=
  let t := EliminateQuantifiersHelper symbolic over_approx false stage_names s f l in
  let t' := SimplifyScenarioTree t in
  let t' := ScenarioTreeEdgeCountGraph 5 t' "QuantifiersRemovedAndSimplified" in
  if PrintFlag 0
  then
    if ReducesToFalse t'
    then
      let t'' :=
        match (ScenarioTreeKeepIfFalse s t) with
        | Some t''' => ScenarioTreeEdgeCountGraph 0 t''' "TriviallyFalse"
        | None => Warning ScenarioFalse ["Doesn't reduce to false? (EQ)"]
        end in
      match t'' with
      | ScenarioTrue => Comment t' ["ScenarioTree unsatisfiable?"]
      | _ => Comment t' ["ScenarioTree unsatisfiable"]
      end
    else t'
  else t'.

Module STBFwdExample.

Definition STBFwdPartial : FOLFormula :=
  FOLAnd (FOLNot (FOLPredicate (PredSameUop "i" "uop")))
   (FOLAnd (FOLPredicate (PredSameVirtualAddress "i" "uop"))
     (FOLAnd (FOLPredicate (PredSameData "i" "uop"))
       (FOLPredicate (PredAddEdges [
         (("i", (SoIInt 0, SoIInt 3)), ("uop", (SoIInt 0, SoIInt 3)), "STBFwd", "red");
         (("uop", (SoIInt 0, SoIInt 3)), ("i", (SoIInt 0, SoIInt 7)), "STBFwd", "red")])
       )
     )
   ).

Definition STBFwd : FOLFormula :=
  FOLExists (MicroopQuantifier "i") STBFwdPartial.

Definition i0 := mkMicroop 0 0 0 0 (Write [] (VA 0 0) (PA (PTag 0) 0) (NormalData 1)).
Definition i1 := mkMicroop 1 0 0 0 (Write [] (VA 0 0) (PA (PTag 0) 0) (NormalData 1)).
Definition i2 := mkMicroop 2 0 0 0 (Read  [] (VA 0 0) (PA (PTag 0) 0) (NormalData 1)).
Definition eState : FOLState := mkFOLState
  [] [] [(i0, (0, 0)); (i1, (0, 0)); (i2, (0, 0))]
  [((i0, (0, 0)), (i1, (0, 0)), "PO", "blue");
   ((i1, (0, 0)), (i2, (0, 0)), "PO", "blue")]
  [] [] [] [i0; i1; i2] [] [] [].
Definition eTerms := [MicroopTerm "uop" i2].

Example e0 : EliminateQuantifiers false false [] eState
  (FOLPredicate (PredAddEdges [(("uop", (SoIInt 0, SoIInt 0)), ("uop", (SoIInt 0, SoIInt 1)), "label", "red")]))
  eTerms =
  ScenarioEdgeLeaf ([((i2, (0, 0)), (i2, (0, 1)), "label", "red")]).
Proof.
  auto.
Qed.

Example e1 : EliminateQuantifiers false false [] eState STBFwdPartial
    [MicroopTerm "uop" i2; MicroopTerm "i" i1] =
    ScenarioEdgeLeaf [
      ((i2, (0, 3)), (i1, (0, 7)), "STBFwd", "red");
      ((i1, (0, 3)), (i2, (0, 3)), "STBFwd", "red")].
Proof.
  auto.
Qed.

Example e2 : stateUops eState = [i0; i1; i2].
Proof.
  auto.
Qed.

Example e3 : EliminateQuantifiers false false [] eState STBFwd eTerms =
  ScenarioOr
    (ScenarioName "i = (inst 0 0 0 0)"
      (ScenarioEdgeLeaf [
        ((i2, (0, 3)), (i0, (0, 7)), "STBFwd", "red");
        ((i0, (0, 3)), (i2, (0, 3)), "STBFwd", "red")]))
    (ScenarioName "i = (inst 1 0 0 0)"
      (ScenarioEdgeLeaf [
        ((i2, (0, 3)), (i1, (0, 7)), "STBFwd", "red");
        ((i1, (0, 3)), (i2, (0, 3)), "STBFwd", "red")])).
Proof.
  auto.
Qed.

End STBFwdExample.

Module BeforeOrAfterExample.

Definition BeforeOrAfter : FOLFormula :=
  FOLForAll (MicroopQuantifier "i1")
    (FOLForAll (MicroopQuantifier "i2")
      (FOLImplies (FOLNot (FOLPredicate (PredSameUop "i1" "i2")))
        (FOLOr
          (FOLPredicate (PredAddEdges [(("i1", (SoIInt 0, SoIInt 0)), ("i2", (SoIInt 0, SoIInt 0)), "x", "red")]))
          (FOLPredicate (PredAddEdges [(("i2", (SoIInt 0, SoIInt 0)), ("i1", (SoIInt 0, SoIInt 0)), "x", "red")]))
        )
      )
    ).

Definition i0 := mkMicroop 0 0 0 0 (Write [] (VA 0 0) (PA (PTag 0) 0) (NormalData 1)).
Definition i1 := mkMicroop 1 0 0 0 (Write [] (VA 0 0) (PA (PTag 0) 0) (NormalData 1)).
Definition i2 := mkMicroop 2 0 0 0 (Read  [] (VA 0 0) (PA (PTag 0) 0) (NormalData 1)).
Definition eState : FOLState := mkFOLState
  [] [] [(i0, (0, 0)); (i1, (0, 0)); (i2, (0, 0))]
  [((i0, (0, 0)), (i1, (0, 0)), "x", "red");
   ((i0, (0, 0)), (i2, (0, 0)), "x", "red")]
  [] [] [] [i0; i1; i2] [] [] [].
Definition eTerms : list FOLTerm := [].

Example e0 :
  EliminateQuantifiers false false [] eState BeforeOrAfter eTerms =
  ScenarioAnd
    (ScenarioName "i1 = (inst 1 0 0 0)"
      (ScenarioName "i2 = (inst 2 0 0 0)"
        (ScenarioOr (ScenarioEdgeLeaf [(i1, (0, 0), (i2, (0, 0)), "x", "red")])
           (ScenarioEdgeLeaf [(i2, (0, 0), (i1, (0, 0)), "x", "red")]))))
    (ScenarioName "i1 = (inst 2 0 0 0)"
      (ScenarioName "i2 = (inst 1 0 0 0)"
        (ScenarioOr (ScenarioEdgeLeaf [(i2, (0, 0), (i1, (0, 0)), "x", "red")])
           (ScenarioEdgeLeaf [(i1, (0, 0), (i2, (0, 0)), "x", "red")])))).
Proof.
Abort.

End BeforeOrAfterExample.

Fixpoint ReevaluateScenarioTree
  (s : FOLState)
  (t : ScenarioTree)
  : ScenarioTree :=
  match t with
  | ScenarioName n t' => ScenarioName n (ReevaluateScenarioTree s t')
  | ScenarioConflict t' => ScenarioConflict (ReevaluateScenarioTree s t')
  | ScenarioEdgeLeaf l =>
      (* If there's nothing that would cause a cycle by its addition (first branch of the and),
         and none of the edges being added are required to not exist (second branch of the and),
         and if none of the nodes used by these edges are required to not exist (third branch of and),
         then add the difference of the two sets. Otherwise it's just false. *)
      if andb (andb
        (SetIntersectionIsEmpty (FlipEdges l) (stateEdges s))
        (SetIntersectionIsEmpty l (stateNotEdges s)))
        (NodeSetIntersectionIsEmpty (NodesFromEdges l) (stateNotNodes s))
      then ScenarioEdgeLeaf (SetDifference l (stateEdges s))
      else ScenarioFalse
  | ScenarioNotEdgeLeaf l =>
      (* If the edges here clash with any of the edges we're already required
         to have, then this is just false. Otherwise, if the forbidding of the edges
         is subsumed by the nodes we are already forbidding (since edges require their
         source and dest nodes), then this is just true. Otherwise, just add any new
         edges that must be forbidden. *)
      (* NotEdgeLeaf l means that *everything* in l must not exist. This is correct because
         NotEdgeLeaf instances come about from DeMorganing EdgesExist sets, so the proper
         ORs will already have been inserted at a higher level of the hierarchy.
         (NotEdgeLeaf instances will probably all be sets of single forbidden edges as a result.) *)
      if (SetIntersectionIsEmpty l (stateEdges s))
      then
        if (NodeSetIntersectionIsEmpty (NodesFromEdges l) (stateNotNodes s))
        then
          ScenarioNotEdgeLeaf (SetDifference l (stateNotEdges s))
        else
          ScenarioTrue
      else ScenarioFalse
  | ScenarioNodeLeaf l =>
      (* If we're not adding nodes that are required to not exist,
         then go ahead and add them. It's ok if the nodes we're adding intersect with the nodes
         of edges that must not exist; those nodes can exist. As long as those edges don't exist,
         we're fine. *)
      if NodeSetIntersectionIsEmpty l (stateNotNodes s)
      then ScenarioNodeLeaf (NodeSetDifference l (stateNodes s))
      else ScenarioFalse
  | ScenarioNotNodeLeaf l =>
      if andb
        (NodeSetIntersectionIsEmpty l (stateNodes s))
        (NodeSetIntersectionIsEmpty l (stateEdgeNodes s))
      then
        match NodeSetDifference l (stateNotNodes s) with
        | [] =>
          (* all nodes in l are already added to the list of forbidden nodes,
           * so we can eliminate this leaf safely *)
          ScenarioTrue
        | l' => ScenarioNotNodeLeaf l'
        end
      else ScenarioFalse
  | ScenarioPred p =>
      if (find (beq_pred p) (statePreds s)) then ScenarioTrue
      else if (find (beq_pred p) (stateNotPreds s)) then ScenarioFalse
      else t
  | ScenarioNotPred p =>
      if (find (beq_pred p) (statePreds s)) then ScenarioFalse
      else if (find (beq_pred p) (stateNotPreds s)) then ScenarioTrue
      else t
  | ScenarioAnd a b =>
      ScenarioAnd (ReevaluateScenarioTree s a) (ReevaluateScenarioTree s b)
  | ScenarioOr a b =>
      ScenarioOr (ReevaluateScenarioTree s a) (ReevaluateScenarioTree s b)
  | ScenarioTrue => t
  | ScenarioFalse => t
  end.

Fixpoint ScenarioTreeAssignLeaves
  (s : FOLState)
  (t : ScenarioTree)
  : ScenarioTree :=
  match t with
  | ScenarioName n t' => ScenarioName n (ScenarioTreeAssignLeaves s t')
  | ScenarioConflict t' => ScenarioConflict (ScenarioTreeAssignLeaves s t')
  | ScenarioEdgeLeaf l =>
      if andb
      (SetIntersectionIsEmpty (FlipEdges l) (stateEdges s))
      (SetIntersectionIsEmpty l (stateNotEdges s))
      then ScenarioTrue
      else ScenarioFalse
  | ScenarioNotEdgeLeaf l =>
      if SetIntersectionIsEmpty l (stateEdges s)
      then ScenarioTrue
      else ScenarioFalse
  | ScenarioNodeLeaf l =>
      if NodeSetIntersectionIsEmpty l (stateNotNodes s)
      then ScenarioTrue
      else ScenarioFalse
  | ScenarioNotNodeLeaf l =>
      if andb (NodeSetIntersectionIsEmpty l (stateNodes s))
        (NodeSetIntersectionIsEmpty l (stateEdgeNodes s))
      then ScenarioTrue
      else ScenarioFalse
  | ScenarioPred p =>
      if find (beq_pred p) (stateNotPreds s)
      then ScenarioFalse
      else ScenarioTrue
  | ScenarioNotPred p =>
      if find (beq_pred p) (statePreds s)
      then ScenarioFalse
      else ScenarioTrue
  | ScenarioAnd a b =>
      ScenarioAnd (ScenarioTreeAssignLeaves s a) (ScenarioTreeAssignLeaves s b)
  | ScenarioOr a b =>
      ScenarioOr (ScenarioTreeAssignLeaves s a) (ScenarioTreeAssignLeaves s b)
  | ScenarioTrue => ScenarioTrue
  | ScenarioFalse => ScenarioFalse
  end.

Definition FOLMacro := (string * list string * FOLFormula) % type.

Fixpoint FindMacro
  (name : string)
  (l : list FOLMacro)
  : option (list string * FOLFormula) :=
  match l with
  | (h_name, h_args, h_formula)::t =>
      if beq_string name h_name
      then Some (h_args, h_formula)
      else FindMacro name t
  | [] => Warning None ["Could not find macro "; name]
  end.

Fixpoint ArgsZipHelper
  {A B : Type}
  (a : list A)
  (b : list B)
  (r : list (A * B))
  : list (A * B) :=
  match (a, b) with
  | (h_a::t_a, h_b::t_b) => ArgsZipHelper t_a t_b ((h_a, h_b) :: r)
  | ([], []) => r
  | _ => Warning r ["Macro argument length mismatch!"]
  end.

Definition ArgsZip
  {A B : Type}
  (a : list A)
  (b : list B)
  : list (A * B) :=
  ArgsZipHelper a b [].

Fixpoint FOLExpandMacros
  (d : nat) (* depth *)
  (l : list FOLMacro)
  (f : FOLFormula)
  : FOLFormula :=
  match d with
  | S d' =>
      match f with
      | FOLName s f' => FOLName s (FOLExpandMacros d' l f')
      | FOLExpandMacro s given_args =>
          match FindMacro s l with
          | Some (old_args, m) =>
              let f' := fold_left
                (fun x y => FOLLet (MacroArgTerm (fst y) (snd y)) x)
                (ArgsZip old_args given_args) m in
              FOLName s (FOLExpandMacros d' l f')
          | None => Warning (FOLPredicate PredFalse) ["Macro "; s; " not found!"]
          end
      | FOLPredicate p => FOLPredicate p
      | FOLNot f' => FOLNot (FOLExpandMacros d' l f')
      | FOLOr a b => FOLOr (FOLExpandMacros d' l a) (FOLExpandMacros d' l b)
      | FOLAnd a b => FOLAnd (FOLExpandMacros d' l a) (FOLExpandMacros d' l b)
      | FOLForAll q f' => FOLForAll q (FOLExpandMacros d' l f')
      | FOLExists q f' => FOLExists q (FOLExpandMacros d' l f')
      | FOLLet t f' => FOLLet t (FOLExpandMacros d' l f')
      end
  | O => Warning (FOLPredicate PredFalse) ["Recursion depth exceeded!"]
  end.

Fixpoint SubsetOf
  (l l' : list GraphEdge)
  : bool :=
  match l with
  | [] => true
  | h::t => if find (beq_edge h) l' then SubsetOf t l' else false
  end.

Fixpoint ISASubsetOf
  (l l' : list ISAEdge)
  : bool :=
  match l with
  | [] => true
  | h::t => if find (beq_isa_edge h) l' then ISASubsetOf t l' else false
  end.

Definition CheckFinalState
  (stage_names : list (list string))
  (arch_edges : list ArchitectureLevelEdge)
  (req_edges : list GraphEdge)
  (check_nodes : bool)
  (s : FOLState)
  : bool :=
  match Topsort (stateEdges s) with
  | ReverseTotalOrder _ =>
    let nodes := NodesFromEdges (stateEdges s) in
    if negb (NodeSetIntersectionIsEmpty (stateNotNodes s) nodes)
    then
      let result := false in
      if PrintFlag 3
      then Comment result ["ScenarioTree converged, but forbidden nodes were used"]
      else result
    else
    if negb (SetIntersectionIsEmpty (stateNotEdges s) (stateEdges s))
    then
      let result := false in
      if PrintFlag 3
      then Comment result ["ScenarioTree converged, but forbidden edges were used"]
      else result
    else
    if negb (SubsetOf req_edges (stateEdges s))
    then
      let result := false in
      if PrintFlag 3
      then Comment result ["ScenarioTree converged, but required edges were missing"]
      else result
    else
    if check_nodes
    then
      match NodeSetDifference (stateNodes s) (NodesFromEdges (stateEdges s)) with
      | _::_  =>
          let result := false in
          if PrintFlag 3
          then Comment result ["ScenarioTree converged, but required nodes were missing"]
          else result
      | [] =>
          let result := true in
          if PrintFlag 3
          then Comment result ["ScenarioTree converged"]
          else result
      end
    else
      let result := true in
      if PrintFlag 3
      then Comment result ["ScenarioTree converged"]
      else result
  | _ =>
    let result := false in
    if PrintFlag 3
    then Comment result
      ("ScenarioTree converged, but graph is cyclic" :: newline ::
        (GraphvizCompressedGraph "DeadEnd" stage_names (stateEdges s) [] arch_edges))
    else result
  end.

(* YM: I don't like this function. I don't use it anymore either...
   apart from its use in error debugging. *)
Fixpoint ScenarioTreeCheckNodes
  (s : FOLState)
  (t : ScenarioTree)
  : ScenarioTree :=
  match t with
  | ScenarioName n t' =>
      match ScenarioTreeCheckNodes s t' with
      | ScenarioTrue => ScenarioTrue
      | ScenarioFalse => ScenarioFalse
      | t'' => ScenarioName n (t'')
      end
  | ScenarioConflict t' =>
      match ScenarioTreeCheckNodes s t' with
      | ScenarioTrue => ScenarioTrue
      | ScenarioFalse => ScenarioFalse
      | t'' => ScenarioConflict (t'')
      end
  | ScenarioEdgeLeaf [] => ScenarioTrue
  | ScenarioNotEdgeLeaf [] => ScenarioTrue
  | ScenarioNodeLeaf [] => ScenarioTrue
  | ScenarioNotNodeLeaf [] => ScenarioTrue
  | ScenarioEdgeLeaf l => t
  | ScenarioNotEdgeLeaf l => t
  | ScenarioNodeLeaf l => ScenarioTrue
  | ScenarioNotNodeLeaf l => ScenarioTrue
  | ScenarioPred _ => ScenarioTrue
  | ScenarioNotPred _ => ScenarioTrue
  | ScenarioAnd a b =>
      ScenarioAnd (ScenarioTreeCheckNodes s a) (ScenarioTreeCheckNodes s b)
  | ScenarioOr a b =>
      ScenarioOr (ScenarioTreeCheckNodes s a) (ScenarioTreeCheckNodes s b)
  | ScenarioTrue => ScenarioTrue
  | ScenarioFalse => ScenarioFalse
  end.

Definition FOLStateIsConsistent
  (s : FOLState)
  : bool :=
  if andb (andb (andb
    (NodeSetIntersectionIsEmpty (stateNodes s) (stateNotNodes s))
    (NodeSetIntersectionIsEmpty (stateEdgeNodes s) (stateNotNodes s)))
    (SetIntersectionIsEmpty (stateEdges s) (stateNotEdges s)))
    (PredSetIntersectionIsEmpty (statePreds s) (stateNotPreds s))
  then true else false.

Fixpoint ReevaluateScenarioTreeIterator
  (n : nat)
  (stage_names : list (list string))
  (arch_edges : list ArchitectureLevelEdge)
  (req_edges : list GraphEdge)
  (s : FOLState)
  (t : ScenarioTree)
  (strat : BranchingStrategy)
  : FOLState * ScenarioTree :=
  (* Re-evaluate the constraints given the current graph, and prune out
   * any which are no longer valid *)
  let t'' := ReevaluateScenarioTree s t in
  let t'' := ScenarioTreeEdgeCountGraph 5 t'' "ScenarioCounts_StillIterating_NotSimplified" in
  (* Simplify the remaining tree *)
  let t' := SimplifyScenarioTree t'' in
  let t' := ScenarioTreeEdgeCountGraph 3 t' "ScenarioCounts_StillIterating_Simplified" in
  (* Check if this is a dead end *)
  if ReducesToFalse t'
  then
    let result := (s, ScenarioFalse) in
    if PrintFlag 3
    then
      let t'' :=
        match (ScenarioTreeKeepIfFalse s t) with
        | Some t''' =>
          let t''' :=
            if PrintFlag 3
            then
              let t''' := Comment t''' ("Reached dead end" :: newline ::
              (GraphvizCompressedGraph "DeadEnd" stage_names (stateEdges s) [] arch_edges)) in
              match FindBranchingChoices strat t''' with
              | Some (RegularChoice cases)
              | Some (ConflictChoice cases) =>
                let f a b :=
                  match b with
                  | ScenarioEdgeLeaf b' =>
                      let g' := app_rev (stateEdges s) b' in
                      Printf a (StringOf
                        (GraphvizCompressedGraph "DeadEndBranch" stage_names g' [] arch_edges))
                  | _ => Printf a (StringOf [newline; "//DeadEndBranch had a branching choice other than an edge"; newline])
                  end in
                fold_left f cases t'''
              | None => Comment t''' ["No branching edges at dead end?"]
              end
            else t''' in
            ScenarioTreeEdgeCountGraph 1 t''' "ReducesToFalse"
        | None => Warning ScenarioFalse ["Doesn't reduce to false?"]
        end in
      match t'' with
      | ScenarioTrue => Comment result ["ScenarioTree unsatisfiable?"]
      | _ => Comment result ["ScenarioTree unsatisfiable"]
      end
    else result
  else
  (* Not FALSE; need to keep evaluating *)
  match GuaranteedEdges t' with
  | (n1, n2, e1, e2, p1, p2) =>
    (* Take transitive closure and add any new edges that may have arisen. *)
    match TransitiveClosure (app_rev (stateEdges s) e1) with
    | TC x =>
        (* Still no cycle; so recurse to continue unit propagation *)
        let e1' := EdgesFromAdjacencyList x in
        let e2' := app_rev (stateNotEdges s) e2 in
        let n1' := app_rev (stateNodes s) n1 in
        let n2' := app_rev (stateNotNodes s) n2 in
        let p1' := app_rev (statePreds s) p1 in
        let p2' := app_rev (stateNotPreds s) p2 in
        let s' := FOLStateReplaceEdges s n1' n2' e1' e2' p1' p2' in
        if negb (FOLStateIsConsistent s')
        then
          let result := (s', ScenarioFalse) in
          if PrintFlag 3
          then Comment result ["FOL state inconsistent during ScenarioTree convergence"]
          else result
        else
        let s' :=
          if PrintFlag 6
          then Comment s' [stringOfNat (List.length n1'); " required nodes"]
          else s' in
        let s' :=
          if PrintFlag 6
          then Comment s' [stringOfNat (List.length n2'); " forbidden nodes"]
        else s' in
        (* Check if the unit propagation has converged *)
        match (n1, n2, e1, e2) with
        | ([], [], [], []) =>
          (* Re-evaluate and simplify one last time. *)
          let t' := ReevaluateScenarioTree s' t' in
          let t' := ScenarioTreeEdgeCountGraph 5 t' "ScenarioCounts_StillIterating_NotSimplified" in
          (* Simplify the remaining tree *)
          let t' := SimplifyScenarioTree t' in
          let t' := ScenarioTreeEdgeCountGraph 3 t' "ScenarioCounts_StillIterating_Simplified" in
          (* Check if this is a valid solution *)
            if ReducesToTrue t' then
              if CheckFinalState stage_names arch_edges req_edges true s'
              then
                let result := (s', ScenarioTrue) in
                if PrintFlag 3
                then Comment result ["ScenarioTree converged and completed"]
                else result
              else
                let result := (s', ScenarioFalse) in
                if PrintFlag 3
                then Comment result ["ReevaluateScenarioTree converged, but graph is invalid"]
                else result
            else
              let result := (s', t') in
              if PrintFlag 3
              then Comment result ["ReevaluateScenarioTree converged but not completed"]
              else result
        | _ =>
          (* Recurse *)
          match n with
          | S n' =>
              let s' :=
                if PrintFlag 3
                then Comment s'
                  ("ReevaluateScenarioTreeIterator iterating" :: newline ::
                  (GraphvizCompressedGraph "Iterating" stage_names
                    (stateEdges s') (SetDifference (stateEdges s') (stateEdges s'))
                    arch_edges))
                else s' in
              ReevaluateScenarioTreeIterator n' stage_names arch_edges req_edges s' t' strat
           | 0 => Warning (s', ScenarioFalse)
               ["ReevaluateScenarioTree Iteration limit exceeded!"]
          end
        end
    | TCError e' =>
        (* Adding these edges would form a cycle: fail *)
        let result := (UpdateFOLState true s (ScenarioEdgeLeaf e'), ScenarioFalse) in
        if PrintFlag 3
        then
          let f a b := Comment a [StringOfGraphEdge b] in
          let result := fold_left f e' result in
          Comment result ("Graph is now cyclic; pruning." :: newline ::
            (GraphvizCompressedGraph "DeadEnd" stage_names
              (stateEdges (fst result)) [] arch_edges))
        else result
    end
  end.

Fixpoint StringOfCase
  (t : ScenarioTree)
  : string :=
    match t with
    | ScenarioEdgeLeaf l => 
        fold_left (fun a b => StringOf [a; newline; "// "; StringOfGraphEdge b]) l
        (StringOf [newline; "// Case: "])
    | ScenarioNotEdgeLeaf l =>
        fold_left (fun a b => StringOf [a; newline; "// "; StringOfGraphEdge b]) l
        (StringOf [newline; "// Case: Not all of edges: "])
    | ScenarioNodeLeaf l =>
        fold_left (fun a b => StringOf [a; newline; "// "; GraphvizShortStringOfGraphNode b]) l
        (StringOf [newline; "// Case: "])
    | ScenarioNotNodeLeaf l =>
        fold_left (fun a b => StringOf [a; newline; "// "; GraphvizShortStringOfGraphNode b]) l
        (StringOf [newline; "// Case: Not all of nodes: "])
    | ScenarioPred p =>
        StringOf [newline; "// Case: "; StringOf (PrintPredicate p)]
    | ScenarioNotPred p =>
        StringOf [newline; "// Case: NotPred "; StringOf (PrintPredicate p)]
    | ScenarioAnd a b =>
        StringOf [newline; "//Case: AND of "; StringOfCase a; newline; " AND "; newline; StringOfCase b]
    | _ => Warning (StringOf [newline; "//Case is something mysterious!"; newline]) ["Case is indecipherable!"]
    end.

Fixpoint StringOfDPLLState
  (h : nat * nat)
  : string :=
  let (h1, h2) := h in
  StringOf [" ("; stringOfNat h1; "/"; stringOfNat h2; ")"].

Fixpoint PrintISAChainHelper2
  (first : bool)
  (l : list ISAEdge)
  (l' : list string)
  : list string :=
  match l with
  | [] => l'
  | h::[] => if first then
              let f x :=
               match x with
               | EdgePO => "po;"
               | EdgeCO => "co;"
               | EdgeRF => "rf;"
               | EdgeFR => "fr;"
               | EdgeRFE => "rfe;"
               | EdgeFRE => "fre;"
               | EdgePO_loc => "po_loc;"
               | EdgePO_plus => "po+;"
               | EdgePO_loc_plus => "po_loc+;"
               | EdgeFence => "fence;"
               | EdgeToFence => "to_fence;"
               | EdgeFromFence => "from_fence;"
               | EdgeFence_plus => "fence+;"
               | EdgeFencePO_plus => "fence_po+;"
               | EdgePOFence_plus => "po_fence+;"
               | EdgePPO => "ppo;"
               | EdgePPO_plus => "ppo+;"
               | EdgePPOFence_plus => "ppo_fence+;"
               | EdgeFencePPO_plus => "fence_ppo+;"
               end in
               ((f h)::l')
             else
              let f x :=
               match x with
               | EdgePO => "po);"
               | EdgeCO => "co);"
               | EdgeRF => "rf);"
               | EdgeFR => "fr);"
               | EdgeRFE => "rfe);"
               | EdgeFRE => "fre);"
               | EdgePO_loc => "po_loc);"
               | EdgePO_plus => "po+);"
               | EdgePO_loc_plus => "po_loc+);"
               | EdgeFence => "fence);"
               | EdgeToFence => "to_fence);"
               | EdgeFromFence => "from_fence);"
               | EdgeFence_plus => "fence+);"
               | EdgeFencePO_plus => "fence_po+);"
               | EdgePOFence_plus => "po_fence+);"
               | EdgePPO => "ppo);"
               | EdgePPO_plus => "ppo+);"
               | EdgePPOFence_plus => "ppo_fence+);"
               | EdgeFencePPO_plus => "fence_ppo+);"
               end in
               ((f h)::l')
  | h::t => if first then 
              let f x :=
              match x with
              | EdgePO => "(po & "
              | EdgeCO => "(co & "
              | EdgeRF => "(rf & "
              | EdgeFR => "(fr & "
              | EdgeRFE => "(rfe & "
              | EdgeFRE => "(fre & "
              | EdgePO_loc => "(po_loc & "
              | EdgePO_plus => "(po+ & "
              | EdgePO_loc_plus => "(po_loc+ &"
              | EdgeFence => "(fence &"
              | EdgeToFence => "(to_fence &"
              | EdgeFromFence => "(from_fence &"
              | EdgeFence_plus => "(fence+ &"
              | EdgeFencePO_plus => "(fence_po+ &"
              | EdgePOFence_plus => "(po_fence+ &"
              | EdgePPO => "(ppo &"
              | EdgePPO_plus => "(ppo+ &"
              | EdgePPOFence_plus => "(ppo_fence+ &"
              | EdgeFencePPO_plus => "(fence_ppo+ &"
              end in
              (PrintISAChainHelper2 false t ((f h)::l'))
            else
              let f x :=
              match x with
              | EdgePO => "po & "
              | EdgeCO => "co & "
              | EdgeRF => "rf & "
              | EdgeFR => "fr & "
              | EdgeRFE => "rfe & "
              | EdgeFRE => "fre & "
              | EdgePO_loc => "po_loc & "
              | EdgePO_plus => "po+ & "
              | EdgePO_loc_plus => "po_loc+ &"
              | EdgeFence => "fence &"
              | EdgeToFence => "to_fence &"
              | EdgeFromFence => "from_fence &"
              | EdgeFence_plus => "fence+ &"
              | EdgeFencePO_plus => "fence_po+ &"
              | EdgePOFence_plus => "po_fence+ &"
              | EdgePPO => "ppo &"
              | EdgePPO_plus => "ppo+ &"
              | EdgePPOFence_plus => "ppo_fence+ &"
              | EdgeFencePPO_plus => "fence_ppo+ &"
              end in
              (PrintISAChainHelper2 false t ((f h)::l'))
  end.

Fixpoint PrintISAChainHelper
  (l : list (list ISAEdge))
  (l' : list string)
  : list string :=
  match l with
  | [] => rev l'
  | h::t => PrintISAChainHelper t (PrintISAChainHelper2 true h l')
  end.

Definition PrintISAChain
  (l : list (list ISAEdge))
  : list string :=
  PrintISAChainHelper l [].

Definition ReplaceISAEdges
  (path : list (nat * nat * option (list ISAEdge)))
  (e : list ISAEdge)
  : list (nat * nat * option (list ISAEdge)) :=
  match path with
  | [] => Warning [] ["Replacing ISA edges on an empty path?"]
  | h::t => let '(h1, h2, h3) := h in
              match h3 with
              | None => ((h1, h2, Some e)::t)
              | Some s => Comment ((h1, h2, Some e)::t) (["Replacing real ISA edges "] ++ (PrintISAChain [s])
                                        ++ [" with "] ++ (PrintISAChain [e]) ++ ["; should be an invariant case."])
              end
  end.

Definition StringOfPiProofState
  (h : nat * nat * option (list (list ISAEdge)))
  : string :=
  let '(h1, h2, h3) := h in
  match h3 with
  | None => StringOf [" ("; stringOfNat h1; "/"; stringOfNat h2; ")"]
  | Some h3' => StringOf ([" ("; stringOfNat h1; "/"; stringOfNat h2; ", "] ++ (PrintISAChain h3') ++ [")"])
  end.

Fixpoint NegateScenarioTree
  (t : ScenarioTree)
  : ScenarioTree :=
  match t with
  | ScenarioName s t' => ScenarioName s (NegateScenarioTree t')
  | ScenarioConflict t' => ScenarioConflict (NegateScenarioTree t')
  | ScenarioAnd a b =>
      ScenarioOr (NegateScenarioTree a) (NegateScenarioTree b)
  | ScenarioOr a b =>
      ScenarioAnd (NegateScenarioTree a) (NegateScenarioTree b)
  | ScenarioEdgeLeaf l => fold_left (FoldFlipEdge false) l ScenarioFalse
  | ScenarioNotEdgeLeaf l => fold_left (FoldFlipEdge true) l ScenarioFalse
  | ScenarioNodeLeaf l => fold_left (FoldFlipNode false) l ScenarioFalse
  | ScenarioNotNodeLeaf l => fold_left (FoldFlipNode true) l ScenarioFalse
  | ScenarioPred p => ScenarioNotPred p
  | ScenarioNotPred p => ScenarioPred p
  | ScenarioTrue => ScenarioFalse
  | ScenarioFalse => ScenarioTrue
  end.

Fixpoint TabList
  (n : nat)
  (l : list string)
  : list string :=
  match n with
  | O => l
  | S n' => TabList n' (tab::l)
  end.

Fixpoint PrintBranchingChoice
  {A : Type}
  (s : A)
  (n : nat)
  (t : ScenarioTree)
  : A :=
  match t with
  | ScenarioName _ t' => PrintBranchingChoice s n t'
  | ScenarioConflict t' => let t' := Comment t' ((TabList n [newline]) ++ ["Conflict choice:"]) in
                              PrintBranchingChoice s n t'
  | ScenarioAnd a b =>
      let s := PrintBranchingChoice s (n + 1) a in
      let s := Comment s ((TabList n [newline]) ++ ["AND"]) in
      PrintBranchingChoice s (n + 1) b
  | ScenarioOr a b =>
      let s := PrintBranchingChoice s (n + 1) a in
      let s := Comment s ((TabList n [newline]) ++ ["OR"]) in
      PrintBranchingChoice s (n + 1) b
  | ScenarioEdgeLeaf l => Comment s (rev (fold_left (fun x y => y::newline::x) (Map (fun x => StringOf ((TabList n []) ++ [ShortStringOfGraphEdge x])) l) [newline]))
  | ScenarioNotEdgeLeaf l => Comment s (rev (")"::(fold_left (fun x y => y::newline::x) (Map (fun x => StringOf ((TabList n []) ++ [ShortStringOfGraphEdge x])) l) [newline; "NOT:("])))
  | ScenarioNodeLeaf l => Comment s (rev (fold_left (fun x y => y::newline::x) (Map (fun x => StringOf ((TabList n []) ++ [ShortStringOfGraphNode x])) l) [newline]))
  | ScenarioNotNodeLeaf l => Comment s (rev (")"::(fold_left (fun x y => y::newline::x) (Map (fun x => StringOf ((TabList n []) ++ [ShortStringOfGraphNode x])) l) [newline; "NOT:("])))
  | ScenarioPred p => Comment s (PrintPredicate p)
  | ScenarioNotPred p => Comment s (("NOT:("::(PrintPredicate p)) ++ [")"])
  | ScenarioTrue => Comment s ["TRUE"]
  | ScenarioFalse => Comment s ["FALSE"]
  end.

Fixpoint FOL_DPLL
  (n : nat)
  (arch_edges : list ArchitectureLevelEdge)
  (req_edges : list GraphEdge)
  (path : list (nat * nat))
  (stage_names : list (list string))
  (s : FOLState)
  (t : ScenarioTree)
  (strat : BranchingStrategy)
  : option FOLState :=
  match n with
  | S n' =>
    (* Depending on the backend, print a status update every once in a while *)
    let s :=
      if orb (PrintFlag 5) (TimeForStatusUpdate 1)
      then CommentFlush s ("Progress: " :: Map StringOfDPLLState (rev_append path []))
      else s in
    (* Evaluate one step *)
    match ReevaluateScenarioTreeIterator 100 stage_names arch_edges req_edges s t strat with
    | (s', t') =>
      (* Debug output *)
      let t' := ScenarioTreeEdgeCountGraph 3 t' "ScenarioCounts" in
      let t' :=
        if PrintFlag 3
        then Comment t' ("Graph is:" :: newline ::
          (GraphvizCompressedGraph
            (StringOf ("Converged: " ::
              (Map StringOfDPLLState (rev_append path []))))
            stage_names
            (stateEdges s') [] arch_edges))
        else t' in
      (* Check if the graph reduces to TRUE or FALSE *)
      let t'' := t' in
      let t'' := ScenarioTreeEdgeCountGraph 3 (SimplifyScenarioTree t'')
        "BranchingEdges" in
      if ReducesToTrue  t'' then Some s' else
      if ReducesToFalse t''
      then
        if PrintFlag 3
        then
          (* Debug: find and display the constraints that caused the problem *)
          let t := ScenarioTreeEdgeCountGraph 5 (ScenarioTreeAssignLeaves s' t')
            "PreUnsatisfiableConstraints" in
          let t''' :=
          match ScenarioTreeKeepIfFalse s t with
          | Some t''' =>
              ScenarioTreeEdgeCountGraph 3 t''' "UnsatisfiableConstraints"
          | None =>
              match Topsort (stateEdges s') with
              | ReverseTotalOrder _ => Warning
                  (ScenarioTreeEdgeCountGraph 1 t' "UnsatisfiableConstraints")
                  ["Disagreement on whether tree reduces to false?"]
              | _ => ScenarioName "Cyclic" ScenarioFalse
              end
          end in
          match t''' with
          | ScenarioTrue => Warning None ["Tree reduced to false?"]
          | _ =>
              if PrintFlag 2
              then Comment None ["Tree reduced to false"]
              else None
          end
        else None
      else
      (* Neither TRUE nor FALSE: find a set of branching choices *)
      let t'' :=
      match strat with
      | NotEdgeStrat _ => if PrintFlag 2 then ScenarioTreeEdgeCountGraph 1 t'' "BeforeBranching" else t''
      | _ => t''
      end
      in
      match FindBranchingChoices strat t'' with
      | Some (RegularChoice cases)
      | Some (ConflictChoice cases) =>
        (* Only try not edges for the first branching decision; that's all we need... *)
        let strat :=
        match strat with
        | NotEdgeStrat _ => NotEdgeStrat false
        | HasDepStrat _ => HasDepStrat false
        | _ => strat
        end
        in
        let cases := SortChoices cases in
        let cases :=
          if PrintFlag 3
          then
            Comment cases ["DPLL Found ";
            stringOfNat (List.length cases); " to consider";
            StringOf (Map StringOfCase cases)]
          else cases in
        (* For each branching choice, recursively evaluate the graph with
         * this choice added.  If a branch doesn't work, add the opposite
         * of that choice as a learned conflict term. *)
        let f_fold
          (a : option FOLState * ScenarioTree * nat) (b : ScenarioTree) :=
          let '(a1, a2, a3) := a in
          match a1 with
          | Some _ =>
              (* Found a solution down a previous branch: return it, and don't
               * evaluate further *)
              (a1, ScenarioFalse, S a3)
          | None =>
              (* Add the choice to the current graph *)
              let s'' := UpdateFOLState false s' b in
              let new_path := ((a3, List.length cases) :: path) in
              (* Debug output *)
              let s'' :=
                if PrintFlag 3
                then
                  let s'' := Comment s'' ["Considering case:"; newline] in
                  Comment (PrintBranchingChoice s'' 0 b) [newline]
                else s'' in
              (* Add the current conflict clauses to the scenario tree *)
              let new_tree := ScenarioAnd a2 t' in
              (* Add the negation of the current branch as a conflict clause for
                 future branches if this branch should fail to work *)
              let new_conflict := (ScenarioAnd a2
                (NegateScenarioTree b)) in
              if (negb (FOLStateIsConsistent s'')) then
                (None, new_conflict, S a3)
              else
                (* Recurse *)
                (FOL_DPLL n' arch_edges req_edges new_path stage_names s'' new_tree strat, new_conflict, S a3)
          end in
        (* Loop over each branch in the branching set *)
        fst (fst (fold_left f_fold cases (None, ScenarioTrue, 0)))
      | None =>
        Warning None ["DPLL could not find branching edges!"]
      end
    end
  | 0 =>
      (* Oops!  Recursed too deep! *)
      let t := ScenarioTreeEdgeCountGraph 3 t "ScenarioCounts" in
      let t := ScenarioTreeEdgeCountGraph 1
        (SimplifyScenarioTree (ScenarioTreeCheckNodes s t))
        "BranchingEdges" in
      match t with
      | ScenarioTrue => Warning (Some s) ["FOL_DPLL iteration limit reached TRUE!"]
      | _ => Warning (Some s) ["FOL_DPLL iteration limit reached!"]
      end
  end.

Inductive FOLStatement : Set :=
| FOLAxiom : FOLFormula -> FOLStatement
| FOLMacroDefinition : FOLMacro -> FOLStatement
| FOLContextTerm : FOLTerm -> FOLStatement.

Fixpoint AddContext
  (core : nat)
  (c : list FOLTerm)
  (f : FOLFormula)
  : FOLFormula :=
  match c with
  | h::t => FOLLet h (AddContext core t f)
  | [] => f
  end.

Fixpoint EvaluateFOLStatementsHelper
  (core : nat)
  (m : list FOLMacro)
  (c : list FOLTerm)
  (f : FOLFormula)
  (l : list FOLStatement)
  : FOLFormula :=
  match l with
  | (FOLAxiom f')::t => EvaluateFOLStatementsHelper core m c (FOLAnd f f') t
  | (FOLMacroDefinition m')::t => EvaluateFOLStatementsHelper core (m' :: m) c f t
  | (FOLContextTerm c')::t => EvaluateFOLStatementsHelper core m (AddTerm c c') f t
  | [] => FOLExpandMacros MacroExpansionDepth m (AddContext core c f)
  end.

Definition EvaluateFOLStatements
  (c : nat)
  (l : list FOLStatement)
  : FOLFormula :=
  EvaluateFOLStatementsHelper c [] [IntTerm "c" c] (FOLPredicate PredTrue) l.

Definition MicroarchitecturalComponent := list FOLStatement.

Definition Microarchitecture := list MicroarchitecturalComponent.

Fixpoint BuildMicroarchitectureHelper
  (l : list MicroarchitecturalComponent)
  (c : nat)
  : FOLFormula :=
  match l with
  | [] => FOLPredicate PredFalse
  | [h] =>
      let result := EvaluateFOLStatements c h in
      PrintGraphvizStringOfFOLFormula result
  | h::t =>
      let result := EvaluateFOLStatements c h in
      let result := PrintGraphvizStringOfFOLFormula result in
      FOLAnd result (BuildMicroarchitectureHelper t (S c))
  end.

Fixpoint BuildMicroarchitecture
  (m : Microarchitecture)
  : FOLFormula :=
  BuildMicroarchitectureHelper m 0.

Fixpoint SetNth
  {A : Type}
  (n : nat)
  (l : list (option A))
  (a : A)
  : list (option A) :=
  match (n, l) with
  | (S n', h::t) => h      :: SetNth n' t  a
  | (S n', []  ) => None   :: SetNth n' [] a
  | (O   , h::t) => Some a :: t
  | (O   , []  ) => [Some a]
  end.

Fixpoint StageNamesRemoveOptions
  (l : list (option string))
  : list string :=
  match l with
  | Some h :: t => h         :: StageNamesRemoveOptions t
  | None   :: t => "Unknown" :: StageNamesRemoveOptions t
  | []          => []
  end.

Fixpoint StageNamesHelper
  (m : MicroarchitecturalComponent)
  (l : list (option string))
  : list string :=
  match m with
  | FOLContextTerm (StageNameTerm s n)::t =>
      StageNamesHelper t (SetNth n l s)
  | _::t => StageNamesHelper t l
  | [] => StageNamesRemoveOptions l
  end.

Fixpoint StageNames
  (m : Microarchitecture)
  : list (list string) :=
  match m with
  | h::t => StageNamesHelper h [] :: StageNames t
  | [] => []
  end.

Fixpoint MakeISAChainList
  (l : list ISAEdge)
  : list (list ISAEdge) :=
  match l with
  | [] => []
  | h::t => [h]::(MakeISAChainList t)
  end.

Fixpoint FilterUspecHelper
  (m : list FOLStatement)
  (axioms : list FOLStatement)
  (mapping : list FOLStatement)
  (theory : list FOLStatement)
  (inv : list FOLStatement)
  : (list FOLStatement * list FOLStatement * list FOLStatement * list FOLStatement) :=
  match m with
  | [] => (axioms, mapping, theory, inv)
  | h::t => match h with
            | FOLAxiom (FOLName n _)
            | FOLMacroDefinition (n, _, _) =>
                if string_prefix "Mapping" n then
                  FilterUspecHelper t axioms (h::mapping) theory inv
                else if string_prefix "Theory" n then
                  FilterUspecHelper t axioms mapping (h::theory) inv
                else if string_prefix "Invariant" n then
                  FilterUspecHelper t axioms mapping theory (h::inv)
                else
                  FilterUspecHelper t (h::axioms) mapping theory inv
            | FOLContextTerm c' => FilterUspecHelper t (h::axioms) (h::mapping) (h::theory) (h::inv)
            | _ => Warning ([], [], [], []) ["Found a nameless axiom or macro!"]
            end
  end.

Fixpoint FilterUspecInput
  (m : list MicroarchitecturalComponent)
  (axioms : list FOLStatement)
  (mapping : list FOLStatement)
  (theory : list FOLStatement)
  (inv : list FOLStatement)
  : (list FOLStatement * list FOLStatement * list FOLStatement * list FOLStatement) :=
  match m with
  | [] => (axioms, mapping, theory, inv)
  | h::t => match FilterUspecHelper h axioms mapping theory inv with
            | (axioms', mapping', theory', inv') => FilterUspecInput t axioms' mapping' theory' inv'
            end
  end.

Fixpoint AllConnectionsHelper2
  (a b : Microop)
  (n : nat)
  (l' : list nat)
  (r : list GraphEdge)
  : list GraphEdge :=
  match l' with
  | [] => r
  | h::t => AllConnectionsHelper2 a b n t (app_rev r [((a, (coreID a, n)), ((b, (coreID b, h))), "", "")])
  end.

Fixpoint AllConnectionsHelper
  (a b : Microop)
  (l l' : list nat)
  (r : list GraphEdge)
  : list GraphEdge :=
  match l with
  | [] => r
  | h::t => AllConnectionsHelper a b t l' (AllConnectionsHelper2 a b h l' r)
  end.

Definition AllConnections
  (a b : Microop)
  (l l' : list nat)
  : list GraphEdge :=
  AllConnectionsHelper a b l l' [].

Definition FoldISAEdge
  (a b : Microop)
  (tree : ScenarioTree)
  (edge : ISAEdge)
  : ScenarioTree :=
  ScenarioAnd tree (ScenarioPred (SymPredHasDependency a b edge)).

Definition FoldISAEdges
  (a b : Microop)
  (tree : ScenarioTree)
  (edges : list ISAEdge)
  : ScenarioTree :=
  match edges with
  | [] => tree
  | h::t =>
      ScenarioOr tree (fold_left (FoldISAEdge a b) edges ScenarioTrue)
  end.

Definition ISAEdgeDisjunction
  (a b : Microop)
  (isa_edges : list (list ISAEdge))
  : ScenarioTree :=
  fold_left (FoldISAEdges a b) isa_edges ScenarioFalse.

Definition ISAEdgeInvifiedDisjunction
  (a b : Microop)
  : ScenarioTree :=
  ScenarioOr (ScenarioOr (ScenarioOr
    (ScenarioPred (SymPredHasDependency a b EdgePO_plus))
    (ScenarioPred (SymPredHasDependency a b EdgeCO)))
    (ScenarioPred (SymPredHasDependency a b EdgeRF)))
    (ScenarioPred (SymPredHasDependency a b EdgeFR)).

Fixpoint GetLocationsHelper
  (m : MicroarchitecturalComponent)
  (l : list nat)
  : list nat :=
  match m with
  | [] => l
  | h::t => match h with
            | (FOLContextTerm (StageNameTerm _ n)) => GetLocationsHelper t (n::l)
            | _ => GetLocationsHelper t l
            end
  end.

Fixpoint GetLocations
  (m : Microarchitecture)
  (l : list nat)
  : list nat :=
  match m with
  | [] => l
  | h::t => GetLocations t (GetLocationsHelper h l)
  end.

(* Create an axioms-mapping-theory-invariants (AMTI) ScenarioTree for the microarchitecture and state. *)
Definition CreateAMTITree
  (s : FOLState)
  (amti : FOLFormula * FOLFormula * FOLFormula * FOLFormula)
  (stage_names : list (list string))
  : ScenarioTree :=
  let '(axioms, mapping, theory, inv) := amti in
  let axioms_tree := EliminateQuantifiers true true stage_names s axioms [] in
  let mapping_tree := EliminateQuantifiers true true stage_names s mapping [] in
  let theory_tree := EliminateQuantifiers true true stage_names s theory [] in
  let inv_tree := EliminateQuantifiers true true stage_names s inv [] in
  ScenarioAnd (ScenarioAnd (ScenarioAnd axioms_tree mapping_tree) theory_tree) inv_tree.

Fixpoint CreateLayersTree
  (flip : bool)
  (l : list (list ISAEdge))
  (l' : list Microop)
  : ScenarioTree :=
  match (l, l') with
  | ([], _) => ScenarioTrue 
  | (h::t, h'::t') => match t' with
                      | [] => Warning ScenarioFalse ["Reached end of microops before ISA chain constructed!"]
                      | h''::t'' =>
                          (* It's ok to call ISAEdgeDisjunction here, because [h] is always a single-element list
                             at the top level. So it will just return <all edges in h> \/ False, which is just
                             <all edges in h>, which is exactly what we want. *)
                          if flip then
                            ScenarioAnd (ISAEdgeDisjunction h'' h' [h]) (CreateLayersTree flip t t')
                          else
                            ScenarioAnd (ISAEdgeDisjunction h' h'' [h]) (CreateLayersTree flip t t')
                      end
  | (h::t, []) => Warning ScenarioFalse ["Reached end of microops before ISA chain constructed!"]
  end.

Fixpoint FilterTranConnsHelper
  (tran_conns : list GraphEdge)
  (s : FOLState)
  (tree : ScenarioTree)
  (stage_names : list (list string))
  (ret : list GraphEdge)
  : list GraphEdge :=
  match tran_conns with
  | [] => ret
  | h::t => let tree' := ScenarioAnd tree (ScenarioEdgeLeaf [h]) in
              match FOL_DPLL 1000 [] [] [] stage_names s tree' (NotEdgeStrat true) with
              | Some _ => let t :=
                            if PrintFlag 2 then
                              Comment t ["Eliminated the following transitive connection:"; newline; GraphvizStringOfGraphEdge [] "" h]
                            else
                              t
                          in
                          FilterTranConnsHelper t s tree stage_names ret
              | None => let h :=
                          if PrintFlag 2 then
                            Comment h ["This transitive connection satisfies required edges:"; newline; GraphvizStringOfGraphEdge [] "" h]
                          else
                            h
                        in
                        FilterTranConnsHelper t s tree stage_names (h::ret)
              end
  end.

Fixpoint CoveredBy
  (s : FOLState)
  (tree : ScenarioTree)
  (stage_names : list (list string))
  (cov_conns : list GraphEdge)
  (conn : GraphEdge)
  : bool :=
  match cov_conns with
  | [] => false
  | h::t => let tree' := ScenarioAnd tree (ScenarioAnd (ScenarioEdgeLeaf [conn]) (ScenarioNotEdgeLeaf [h])) in (* A /\ ~B *)
              match FOL_DPLL 1000 [] [] [] stage_names s tree' DefaultStrat with
              | Some _ => CoveredBy s tree stage_names t conn
              | None => let result := Comment true [GraphvizStringOfGraphEdge [] "" conn; " is covered by "; GraphvizStringOfGraphEdge [] "" h] in
                        result
              end
  end.

Inductive CoverSet : Set :=
| ConnSet : GraphEdge -> list GraphEdge -> CoverSet.

(* Returns:

   -(Some true) if e is covered by e'
   -(Some false) if e' is covered by e
   -None if the two are incompatible
*)
Definition CheckCoverage
  (s : FOLState)
  (tree : ScenarioTree)
  (stage_names : list (list string))
  (e e' : GraphEdge)
  : option bool :=
  let tree' := ScenarioAnd tree (ScenarioAnd (ScenarioEdgeLeaf [e]) (ScenarioNotEdgeLeaf [e'])) in (* A /\ ~B *)
  let tree'' := ScenarioAnd tree (ScenarioAnd (ScenarioEdgeLeaf [e']) (ScenarioNotEdgeLeaf [e])) in (* B /\ ~A *)
  let covered_by := FOL_DPLL 1000 [] [] [] stage_names s tree' DefaultStrat in
  let covers := FOL_DPLL 1000 [] [] [] stage_names s tree'' DefaultStrat in
  match (covered_by, covers) with
  | (None, _) => (Some true)
  | (_, None) => (Some false)
  | _ => None
  end.

Fixpoint GetNextCoveringSet
  (s : FOLState)
  (tree : ScenarioTree)
  (stage_names : list (list string))
  (remain : list GraphEdge)
  (conns : list GraphEdge)
  (set : CoverSet)
  : (CoverSet * list GraphEdge) :=
  match conns with
  | [] => (set, remain)
  | h::t => match set with
            | ConnSet set_rep elems =>
                let result := CheckCoverage s tree stage_names h set_rep in
                let '(remain, set_rep, elems) :=
                  match result with
                  | Some true =>
                      let elems :=
                        if PrintFlag 2 then
                          Comment elems [GraphvizStringOfGraphEdge [] "" h; " is covered by "; GraphvizStringOfGraphEdge [] "" set_rep]
                        else
                          elems
                      in
                      (remain, set_rep, (h::elems))
                  | Some false =>
                      let elems :=
                        if PrintFlag 2 then
                          Comment elems [GraphvizStringOfGraphEdge [] "" set_rep; " is covered by "; GraphvizStringOfGraphEdge [] "" h]
                        else
                          elems
                      in
                      (remain, h, (set_rep::elems))
                  | None => ((h::remain), set_rep, elems)
                  end
                in
                GetNextCoveringSet s tree stage_names remain t (ConnSet set_rep elems)
            end
  end.

Fixpoint MergeCoveringSets
  (s : FOLState)
  (tree : ScenarioTree)
  (stage_names : list (list string))
  (checked_sets : list CoverSet)
  (cov_sets : list CoverSet)
  (new_set : CoverSet)
  : list CoverSet :=
  match cov_sets with
  | [] => (new_set::checked_sets)
  | h::t =>
      match (h, new_set) with
      | (ConnSet h' h_elems, ConnSet nset' n_elems) =>
          match CheckCoverage s tree stage_names h' nset' with
          | Some true => app_tail ((ConnSet nset' (app_tail (h'::h_elems) n_elems))::checked_sets) t
          | Some false => app_tail ((ConnSet h' (app_tail h_elems (nset'::n_elems)))::checked_sets) t
          | None => MergeCoveringSets s tree stage_names (h::checked_sets) t new_set
          end
      end
  end.

(* For the moment, we are just focusing on making the minimal number of covering sets, not on ensuring that
   each covering set is complete (i.e. everything that the top element covers is in its "descendants"). The
   former should be enough for our purposes (at least for the moment) because I hypothesize that uarches follow a pattern of
   having 1 coverer for all connections that won't be torched by required edge requirements. *)
Fixpoint GetCoveringSets
  (n : nat)
  (s : FOLState)
  (tree : ScenarioTree)
  (stage_names : list (list string))
  (cov_sets : list CoverSet)
  (poss_conns : list GraphEdge)
  : list CoverSet :=
  match n with
  | S n' =>
      match poss_conns with
      | [] => cov_sets
      | h::t => let (new_set, remain) := GetNextCoveringSet s tree stage_names [] t (ConnSet h []) in
                 let cov_sets := MergeCoveringSets s tree stage_names [] cov_sets new_set in
                 GetCoveringSets n' s tree stage_names cov_sets remain
      end
  | O => Warning [] ["Recursed too far in GetCoveringSets!"]
  end.

Definition Coverify
  (l : list GraphEdge)
  : list CoverSet :=
  let f x :=
    ConnSet x []
  in
  Map f l.

Inductive FilterStrategy : Set :=
| FilterAndCover : FilterStrategy
| FilterOnly : FilterStrategy
| CoverOnly : FilterStrategy
| DoNothing : FilterStrategy.

Definition FilterTranConns
  (strat : FilterStrategy)
  (tran_conns : list GraphEdge)
  (s : FOLState)
  (t : ScenarioTree)
  (rt : ScenarioTree)
  (stage_names : list (list string))
  : list CoverSet :=
  let s := PrintTimestamp s "Filter_start" in
  let req_filtered :=
    match strat with
    | FilterAndCover
    | FilterOnly => FilterTranConnsHelper tran_conns s (ScenarioAnd t rt) stage_names []
    | CoverOnly
    | DoNothing => tran_conns
    end
  in
  let result :=
    match strat with
    | FilterAndCover
    | CoverOnly => GetCoveringSets 100 s t stage_names [] req_filtered
    | FilterOnly
    | DoNothing => Coverify req_filtered
    end
  in
  PrintTimestamp result "Filter_end".

Fixpoint PrintMicroopChain
  {A : Type}
  (s : A)
  (l : list Microop)
  : A :=
  match l with
  | [] => s
  | h::t => let t := Comment t ["Instr "; stringOfNat (globalID h); ";"] in
              PrintMicroopChain s t
  end.

Fixpoint PrintEdgeList
  {A : Type}
  (s : A)
  (l : list GraphEdge)
  : A :=
  match l with
  | [] => s
  | h::t => let t := Comment t [GraphvizStringOfGraphEdge [] "" h; newline] in
            PrintEdgeList s t
  end.

Fixpoint FindISADependencies
  (a b : Microop)
  (s : FOLState)
  : list ISAEdge :=
  let f x :=
    match x with
    | SymPredHasDependency a' b' c' => andb (beq_uop a a') (beq_uop b b')
    | _ => false
    end
  in
  let g x y :=
    match y with
    | SymPredHasDependency a' b' c' => (c'::x)
    | _ => Warning x ["FindISADependencies: filter function not working properly..."]
    end
  in
  fold_left g (filter f (statePreds s)) [].

Fixpoint ConvertToISAChainHelper
  (l : list Microop)
  (s : FOLState)
  (l' : list (list ISAEdge))
  : list (list ISAEdge) :=
  match l with
  | [] => rev l'
  | h::t => match t with
            | [] => l'
            | h'::t' => ConvertToISAChainHelper t s ((FindISADependencies h h' s)::l')
            end
  end.

Fixpoint ConvertToISAChain
  (l : list Microop)
  (s : FOLState)
  : list (list ISAEdge) :=
  ConvertToISAChainHelper l s [].

Definition StartChain
  (l : list Microop)
  : option Microop :=
  match l with
  | [] => Comment None ["Finding start of an empty chain?"]
  | h::t => Some h
  end.

Fixpoint EndChain
  (l : list Microop)
  : option Microop :=
  match l with
  | [] => Comment None ["Finding end of an empty chain?"]
  | h::[] => Some h
  | h::t => EndChain t
  end.

Fixpoint TryISAPattern
  (n : nat)
  (inv_uop : Microop)
  (inv_edge : ISAEdge)
  (ret : bool * list (list ISAEdge) * list Microop)
  (choice : list ISAEdge * option ISAPattern)
  : (bool * list (list ISAEdge) * list Microop) :=
  match n with
  | S n' =>
      let '(changed, l, inter) := ret in
      if changed then
        (* We already succeeded down another path, just return what we already have. *)
        ret
      else
        (* Get the current step. *)
        match (l, inter) with
        | (h::t, h''::t'') =>
            let (edges, rem) := choice in
            (* Does the current step match with what the inv requires? *)
            if ISASubsetOf edges h then
              (* Is this the end of the pattern? *)
              match rem with
              | None =>
                  let t :=
                  if PrintFlag 2 then
                    Comment t ["Reached base case of TryISAPattern for "; PrintISAEdge inv_edge]
                  else
                    t
                  in
                  (true, ([inv_edge]::t), inv_uop::t'')
              | Some rem' =>
                  (* Check the rest of the path. *)
                  let choices := GetInitialEdge true 100 rem' in
                  let '(changed', l', inter') := fold_left (TryISAPattern n' inv_uop inv_edge) choices (changed, t, t'') in
                  if changed' then (changed', l', inter') else ret (* Only return the new result if we succeeded. *)
              end
            else
              (* Nothing to see here, move along. *)
              ret
        | _ => 
          if PrintFlag 2 then
            Comment ret ["Ran out of steps before we could get to the end of the invariant."] 
          else
            ret
        end
  | O => Warning (false, [], []) ["Recursed too far in TryISAPattern!"]
  end.
  
Fixpoint ReplaceWithInvariantsHelper
  (changed : bool)
  (l : list (list ISAEdge))
  (inter : list Microop)
  (inv_patterns : list (ISAPattern * ISAEdge))
  : (bool * list (list ISAEdge) * list Microop) :=
  match StartChain inter with
  | None => (changed, l, inter)
  | Some inv_uop =>
      match inv_patterns with
      | [] => (changed, l, inter)
      | h::t => let (pat, inv_edge) := h in
                let choices := GetInitialEdge true 100 pat in
                let '(changed', l', inter') := fold_left (TryISAPattern 100 inv_uop inv_edge) choices (false, l, inter) in
                if orb changed changed' then
                  ReplaceWithInvariantsHelper true l' inter' t
                else
                  ReplaceWithInvariantsHelper false l' inter' t
      end
  end.

Fixpoint ReplaceWithInvariantsInner
  (n : nat)
  (changed : bool)
  (l : list (list ISAEdge))
  (inter : list Microop)
  (inv_patterns : list (ISAPattern * ISAEdge))
  : (list (list ISAEdge) * list Microop) :=
  match n with
  | S n' =>
      let ret := ReplaceWithInvariantsHelper false l inter inv_patterns in
      let '(changed', l', inter') := ret in
      if changed' then
        ReplaceWithInvariantsInner n' true l' inter' inv_patterns
      else
        (l', inter')
  | O => Warning ([], []) ["Recursed too far in ReplaceWithInvariantsInner!"]
  end.

Definition ReplaceWithInvariants
  (l : list (list ISAEdge))
  (inter : list Microop)
  (inv_patterns : list (ISAPattern * ISAEdge))
  : (list (list ISAEdge) * list Microop) :=
  ReplaceWithInvariantsInner 100 false l inter inv_patterns.

Fixpoint ReplaceWithInvariantsOuter
  (l : list (list ISAEdge))
  (inter : list Microop)
  (inv_patterns : list (ISAPattern * ISAEdge))
  : (list (list ISAEdge) * list Microop) :=
  match (l, inter) with
  | ([], h::[]) => (l, inter)
  | (h::t, h'::t') =>
      let (l', inter') := ReplaceWithInvariantsOuter t t' inv_patterns in
      ReplaceWithInvariants (h::l') (h'::inter') inv_patterns
  | _ => Warning ([], []) ["Unexpected pattern in ReplaceWithInvariantsOuter!"]
  end.

Definition InvPatterns :=
  [
    ((Rel EdgePO), EdgePO_plus);
    ((Rel EdgePPO), EdgePPO_plus);
    ((Rel EdgePO_loc), EdgePO_loc_plus);
    ((Rel EdgeFence), EdgeFence_plus);
    (Chain (Rel EdgeFence_plus) (Rel EdgePO_plus), EdgeFencePO_plus);
    (Chain (Rel EdgePO_plus) (Rel EdgeFence_plus), EdgePOFence_plus);
    (Chain (Rel EdgeFence_plus) (Rel EdgePPO_plus), EdgeFencePPO_plus);
    (Chain (Rel EdgePPO_plus) (Rel EdgeFence_plus), EdgePPOFence_plus)
  ].

Definition InvariantifyChain
  (l : list (list ISAEdge))
  : list (list ISAEdge) :=
  (* Make dummy chains for the rest of the parameters to ReplaceWithInvariants.
     We don't care about their values here. *)
  let l := 
    if PrintFlag 2 then
      Comment l (["Invariantifying the chain "] ++ (PrintISAChain l))
    else
      l
  in
  let inter := Map (fun x => mkMicroop 0 0 0 0 (Fence [])) ([]::l) in
  let '(chain, _) := ReplaceWithInvariantsOuter l inter InvPatterns in
  let chain :=
    if PrintFlag 2 then
      Comment chain (["Invariantified chain is "] ++ (PrintISAChain chain))
    else
      chain
  in
  chain.

Definition TransformISAEdge
  (e : list ISAEdge)
  : list (list ISAEdge) :=
  match e with
  | _ => [e]
  end.

Definition GetInvEdges
  (l : list (ISAPattern * ISAEdge))
  : list ISAEdge :=
  let f x :=
    match x with
    | (y, z) => z
    end
  in
  Map f l.

Definition GetInvPatterns
  (l : list (ISAPattern * ISAEdge))
  : list ISAPattern :=
  let f x :=
    match x with
    | (y, z) => y
    end
  in
  Map f l.

Fixpoint InvCoveredByHelper2
  (peel_left : bool)
  (e : ISAEdge)
  (l : list ISAEdge)
  (inv_patterns : list (ISAPattern * ISAEdge))
  : bool :=
  match l with
  | [] => false
  | h::t => match find (fun x => beq_isa_edge h (snd x)) inv_patterns with
            | None => InvCoveredByHelper2 peel_left e t inv_patterns
            | Some (pat, _) =>
                let pat := Comment pat (["Found pattern "] ++ (PrintISAPattern pat) ++ [" for "; PrintISAEdge h; " in inv_patterns when filtering peeling choices."]) in
                let choices :=
                  if peel_left then
                    GetISAEdges (GetFinalEdge 100 pat)
                  else
                    GetISAEdges (GetInitialEdge false 100 pat)
                in
                let f x :=
                  if find (beq_isa_edge e) x then true else false
                in
                if fold_left andb (Map f choices) true then
                  true
                else
                  InvCoveredByHelper2 peel_left e t inv_patterns
            end
  end.

Definition InvCoveredByHelper
  (peel_left : bool)
  (e : ISAEdge)
  (l : list ISAEdge)
  (inv_patterns : list (ISAPattern * ISAEdge))
  : bool :=
  match (find (beq_isa_edge e) l, find (fun x => beq_isa_edge e (snd x)) inv_patterns) with
  | (Some _, Some _) => true (* This is the simple case. The invified edge matches the end of the current chain. *)
  | _ =>
      InvCoveredByHelper2 peel_left e l inv_patterns (* Check whether the innards of invariantified edges ending chains could eat up our choice "e". *)
  end.

Fixpoint InvCoveredBy
  (peel_left : bool)
  (l l' : list ISAEdge)
  (inv_patterns : list (ISAPattern * ISAEdge))
  : bool :=
  match l with
  | [] => true
  | h::t => if InvCoveredByHelper peel_left h l' inv_patterns then InvCoveredBy peel_left t l' inv_patterns else false
  end.

Definition ChopHead
  (l : list (list ISAEdge))
  : list (list ISAEdge) * list ISAEdge :=
  match l with
  | [] => Warning ([], []) ["Chopping head of an empty list?"]
  | h::t => (t, h)
  end.

Definition ChopTail
  (l : list (list ISAEdge))
  : list (list ISAEdge) * list ISAEdge :=
  let l' := rev l in
  match l' with
  | [] => Warning ([], []) ["Chopping tail of an empty list?"]
  | h::t => (rev t, h)
  end.

Fixpoint ChopNumHelper
  {A : Type}
  (flip : bool)
  (n : nat)
  (l : list A)
  : list A :=
  match n with
  | O => if flip then rev l else l
  | S n' => match l with
            | [] => Warning [] ["Chopping an empty list?"]
            | h::t => ChopNumHelper flip n' t
            end
  end.

Definition ChopHeadNum
  {A : Type}
  (n : nat)
  (l : list A)
  : list A :=
  ChopNumHelper false n l.

Definition ChopTailNum
  {A : Type}
  (n : nat)
  (l : list A)
  : list A :=
  ChopNumHelper true n (rev l).

(* This function checks if an initial subchain (check_chain) can be subsumed within the rest of the chain (rest_chain). It's essentially
   checking whether the edge added to a chain by the peeling "completes the pattern" of an invariant which is right next to it (and thus
   should subsume it). In this case, the function returns false, indicating that this choice ought to be tossed.

   Example: fence+; ppo_fence+

   If we add ppo (and thus ppo+) to this chain, we'd get "ppo+; fence+; ppo_fence+". CheckChoiceHelper would first check "ppo+" against "fence+; ppo_fence+"
   and come up empty. It would then check "ppo+; fence+" against "ppo_fence+". It first invariantifies "ppo+; fence+" (the call to InvariantifyChain below)
   into "ppo_fence+", which can be subsumed into the rest_chain of "ppo_fence+", so we return false.

   If no initial subchain can be subsumed within the rest of the chain, the function returns true, indicating that this choice is a valid choice.
*)
Fixpoint CheckChoiceHelper
  (n : nat)
  (peel_left : bool)
  (inv_patterns : list (ISAPattern * ISAEdge))
  (check_chain : list (list ISAEdge))
  (rest_chain : list (list ISAEdge))
  : bool :=
  match n with
  | S n' =>
      let check_chain' := InvariantifyChain check_chain in
      let check_chain' :=
      if PrintFlag 2 then
        Comment check_chain' (["Checking "] ++ (PrintISAChain check_chain') ++ [" against "] ++ (PrintISAChain rest_chain))
      else
        check_chain'
      in
      match rest_chain with
      | [] =>
          if PrintFlag 2 then
            Comment true ["Reached the end of rest_chain without a match..."]
          else
            true
      | h'::t' =>
        match check_chain' with
        | [h] =>
            if peel_left then
              let (rest_start, rest_tail) := ChopTail rest_chain in
              if InvCoveredBy peel_left h rest_tail inv_patterns then
                if PrintFlag 2 then
                  Comment false ["check_chain is covered, tossing."]
                else
                  false
              else 
                CheckChoiceHelper n' peel_left inv_patterns (rest_tail::check_chain) rest_start
            else
              if InvCoveredBy peel_left h h' inv_patterns then
                if PrintFlag 2 then
                  Comment false ["check_chain is covered, tossing."]
                else
                  false
              else 
                CheckChoiceHelper n' peel_left inv_patterns (app_tail check_chain [h']) t'
        | _ =>
            if peel_left then
              let (rest_start, rest_tail) := ChopTail rest_chain in
              CheckChoiceHelper n' peel_left inv_patterns (rest_tail::check_chain) rest_start
            else
              CheckChoiceHelper n' peel_left inv_patterns (app_tail check_chain [h']) t'
        end
      end
  | O => Warning false ["Recursed too far in CheckChoiceHelper!"]
  end.

Fixpoint EdgesAreExcluded
  (edges : list ISAEdge)
  (excluded_edges : list (list ISAEdge))
  : bool :=
  match excluded_edges with
  | [] => false
  | h::t => if ISASubsetOf edges h then true else EdgesAreExcluded edges t
  end.

Definition CheckChoice
  (peel_left : bool)
  (inv_patterns : list (ISAPattern * ISAEdge))
  (rest_chain : list (list ISAEdge))
  (excluded_edges : list (list ISAEdge))
  (choice : list ISAEdge * option ISAPattern)
  : (bool * list ISAEdge * option ISAPattern) :=
  let (edges, rem) := choice in
  if EdgesAreExcluded edges excluded_edges then
    (false, edges, rem)
  else
    let check_chain := [edges] in
    let matched := CheckChoiceHelper 100 peel_left inv_patterns check_chain rest_chain in
    (matched, edges, rem).

Definition FilterNextChoices
  (peel_left : bool)
  (chain : list (list ISAEdge))
  (next : list (list ISAEdge * option ISAPattern))
  (inv_patterns : list (ISAPattern * ISAEdge))
  (excluded_edges : list (list ISAEdge))
  : list (list ISAEdge * option ISAPattern) :=
  let f x y :=
    match y with
    | (true, a, b) => ((a, b)::x)
    | _ => x
    end
  in
  fold_left f (Map (CheckChoice peel_left inv_patterns chain excluded_edges) next) [].

Fixpoint FilterISAPeelChoicesHelper
  (l ret : list ((list ISAEdge) * option ISAPattern))
  (exclude_last : bool)
  : list ((list ISAEdge) * option ISAPattern) :=
  match l with
  | [] => ret
  | h::t => match h with
            | ([], None) => let t := 
                              if PrintFlag 2 then
                                Comment t ["Tossing an empty choice..."]
                              else
                                t
                            in
                            FilterISAPeelChoicesHelper t ret exclude_last
            | (rel, None) => if exclude_last then
                               let t :=
                                 if PrintFlag 2 then
                                   Comment t (["Tossing (( "] ++ (PrintISAChain [rel]) ++
                                   [" ), (None)), a choice with no part of the axiom left (should have been tried in concretization/base case)..."])
                                 else
                                   t
                               in
                               FilterISAPeelChoicesHelper t ret exclude_last
                             else
                               let t :=
                                 if PrintFlag 2 then
                                   Comment t (["Found a choice with no part of the axiom left: (( "] ++ (PrintISAChain [rel])
                                   ++ [" ), (None)). Adding it to the list."])
                                 else
                                   t
                               in
                               FilterISAPeelChoicesHelper t (h::ret) exclude_last
            | ([], Some rem) => let t := Warning t (["Found a nothing choice with ("] ++ (PrintISAPattern rem) ++ [") still left after it!"]) in
                              FilterISAPeelChoicesHelper t ret exclude_last
            | (rel, Some rem) => let t :=
                                  if PrintFlag 2 then
                                    Comment t (["Found a right and proper choice: (( "] ++ (PrintISAChain [rel]) ++ [" ), ( "] ++ (PrintISAPattern rem)
                                     ++ [" )). Adding it to the list."])
                                  else
                                    t
                                 in
                             FilterISAPeelChoicesHelper t (h::ret) exclude_last
            end
  end.

Definition FilterISAPeelChoices
  (l : list ((list ISAEdge) * option ISAPattern))
  (exclude_last : bool)
  : list ((list ISAEdge) * option ISAPattern) :=
  FilterISAPeelChoicesHelper l [] exclude_last.

Fixpoint FilterReqEdges
  (uops : list Microop)
  (l : list GraphEdge)
  : list GraphEdge :=
  match l with
  | [] => []
  | h::t => 
      match h with
      | ((src, loc1), (dest, loc2), _, _) =>
            if find (beq_uop src) uops then
              if find (beq_uop dest) uops then
                h::(FilterReqEdges uops t)
              else
                FilterReqEdges uops t
            else
              FilterReqEdges uops t
      end
  end.

(* Extracted to a function in BackendLinux.ml. *)
Definition IsFilterStrat (n : nat) := false.

Fixpoint TCInductiveCaseRunOne
  (m n : nat)
  (path : list (nat * nat * option (list (list ISAEdge))))
  (remain : option ISAPattern)
  (amti : FOLFormula * FOLFormula * FOLFormula * FOLFormula)
  (stage_names : list (list string))
  (locations : list nat)
  (chain : list (list ISAEdge))
  (a : Microop)
  (uop_chain : list Microop)
  (req_edges : list GraphEdge)
  (inv_patterns : list (ISAPattern * ISAEdge))
  : option (list (list ISAEdge)) :=
  match m with
  | S m' =>
    let '(axioms, mapping, theory, inv) := amti in
    match remain with
    | None => Warning None ["An empty remaining pattern passed to TCInductiveCaseRunOne?"]
    | Some pat =>
        let s := (mkFOLState [] [] [] [] [] [] [] (a::uop_chain) [] [] []) in
        let s := Printf s (StringOf [newline; "//TCInductiveCaseRunOne (g_fold) start, depth "; stringOfNat n; ";"; newline]) in
        let s := Comment s (["Remaining ISA pattern is: "] ++ (PrintISAPattern pat)) in
        let s := Comment s (["Current Path is: "] ++ (Map StringOfPiProofState (rev path))) in
        let s := Comment s ["Current instructions are:"] in
        let s := PrintMicroopChain s (a::uop_chain) in
        let chain := Comment chain (["ISA chain is "] ++ (PrintISAChain chain)) in
        let poss_b' := StartChain uop_chain in
        let poss_c := EndChain uop_chain in
        match (poss_b', poss_c) with
        | (Some b', Some c) =>
            let amti_tree := CreateAMTITree s amti stage_names in
            let layers := CreateLayersTree false chain uop_chain in
            let property := ScenarioNotEdgeLeaf (AllConnections a c locations locations) in
            let tran_conns := AllConnections a b' locations locations in
            let tran_conns := Comment tran_conns ["There are "; stringOfNat (List.length tran_conns);
                                " possible transitive connections."] in
            let req_edges_tree := fold_left (FoldFlipEdge false) req_edges ScenarioFalse in
            let filter_tree := ScenarioAnd amti_tree layers in
            let (filt_strat_1, filt_strat_2) :=
              if IsFilterStrat 0 then
                let res := Comment (FilterOnly, FilterOnly) ["Strat was 0"] in res
              else if IsFilterStrat 1 then
                let res := Comment (DoNothing, FilterOnly) ["Strat was 1"] in res
              else if IsFilterStrat 2 then
                let res := Comment (DoNothing, FilterAndCover) ["Strat was 2"] in res
              else
                let res := Comment (FilterAndCover, FilterAndCover) ["Strat was 3"] in res
            in
            let tran_conns_filt := FilterTranConns filt_strat_1 tran_conns s filter_tree req_edges_tree stage_names in
            let (chain, uop_chain) := ReplaceWithInvariants chain uop_chain inv_patterns in
            let s := (mkFOLState [] [] [] [] [] [] [] (a::uop_chain) [] [] []) in
            let chain := Comment chain (["New ISA chain is "] ++ (PrintISAChain chain)) in
            let uop_chain := Comment uop_chain ["New instructions are:"] in
            let s := PrintMicroopChain s (a::uop_chain) in
            let amti_tree := CreateAMTITree s amti stage_names in
            let layers := CreateLayersTree false chain uop_chain in
            let filter_tree := ScenarioAnd amti_tree layers in
            let req_edges := FilterReqEdges (a::uop_chain) req_edges in
            let req_edges_tree := fold_left (FoldFlipEdge false) req_edges ScenarioFalse in
            let f x :=
              match x with
              | ConnSet x' _ => x'
              end
            in
            let tran_conns :=
              match (filt_strat_1, filt_strat_2) with
              | (FilterOnly, CoverOnly) => Map f tran_conns_filt (* the covered sets will be empty because no covering was done - see FilterTranConns *)
              | _ => tran_conns
              end
            in
            let tran_conns_inv := FilterTranConns filt_strat_2 tran_conns s filter_tree req_edges_tree stage_names in
            let tran_conns :=
              match (filt_strat_1, filt_strat_2) with
              | (FilterAndCover, FilterAndCover) =>
                  if orb (negb (SubsetOf (Map f tran_conns_filt) (Map f tran_conns_inv))) (negb (SubsetOf (Map f tran_conns_inv) (Map f tran_conns_filt))) then
                    Warning tran_conns_inv ["Filtered transitive connections did NOT match for inv and non-inv versions!"]
                  else
                    Comment tran_conns_inv ["Filtered transitive connections matched for inv and non-inv versions!"]
              | _ => tran_conns_inv
              end
            in
            let tran_conns := Comment tran_conns ["After filtering, there are "; stringOfNat (List.length tran_conns);
                                " possible transitive connections."] in
            let tran_conns := Comment tran_conns ["Recursing over all those transitive connections..."] in
            let partial_tree := ScenarioAnd (ScenarioAnd amti_tree layers) property in
            (* Get peeling choices. *)
            let isa_choices := FilterISAPeelChoices (GetFinalEdge 100 pat) true in
            let isa_choices := FilterNextChoices false chain isa_choices inv_patterns [] in
            let g_fold (prev : option (list (list ISAEdge)) * nat * nat) (covset : CoverSet) :=
              let (conn, covered) :=
                match covset with
                | ConnSet conn' covered' => (conn', covered')
                end
              in
              let '(prev_soln, cur_index, num_choices) := prev in
              let path := ((cur_index, num_choices, Some chain)::path) in
              let s := Comment s (["Checking Path: "] ++ (Map StringOfPiProofState (rev path))) in
              match prev_soln with
              | Some s' => (prev_soln, S cur_index, num_choices) (* Return the existing soln... *)
              | None =>
                  let cur_tree := ScenarioAnd partial_tree (ScenarioEdgeLeaf [conn]) in
                  let cur_tree := Printf cur_tree (StringOf ["//Adding edge "; GraphvizStringOfGraphEdge [] "" conn]) in
                  match FOL_DPLL 1000 [] req_edges [] stage_names s cur_tree (DefaultStrat) with
                  | None => Comment (None, S cur_index, num_choices) ["TCInductiveCaseRunOne depth "; stringOfNat n; " returned UNSAT!"]
                  | Some s' =>
                      let partial_tree := Comment partial_tree ["Abstract counterexample found; ";
                        "TCInductiveCaseRunOne depth "; stringOfNat n; " returned SAT!"] in
                      let concr_choices := GetSingleEdgeChoices pat in
                      let concr_tree := ScenarioAnd partial_tree (ISAEdgeDisjunction a b' concr_choices) in
                      let req_edges := PrintTimestamp req_edges "Concr_start" in
                      match FOL_DPLL 1000 [] req_edges [] stage_names s concr_tree (HasDepStrat true) with
                      | Some s' => Comment (Some (ConvertToISAChain (a::uop_chain) s'), S cur_index, num_choices) ["Concretized with "; stringOfNat n; " instrs!"]
                      | None => let req_edges := Comment req_edges ["Could not concretize with "; stringOfNat n; " instrs. Peeling off layer."] in
                          (* Now we peel off a layer and repeat the process. *)
                          (* First, add the current transitive connection to the required edges. *)
                          let req_edges := PrintTimestamp req_edges "Concr_end" in
                          let req_edges := (conn::req_edges) in
                          (* Now create the new uop and add it to the chain. *)
                          let uop_b'' := mkMicroop n 0 0 0 (Fence []) in
                          let uop_chain := (uop_b''::uop_chain) in
                          (* And now call the solver once for each possible ISA-level edge that we could be
                             peeling off the chain. *)
                          let h_fold (prev_soln' : option (list (list ISAEdge))) (choice : list ISAEdge * option ISAPattern) :=
                            match prev_soln' with
                            | Some _ => prev_soln'
                            | None => 
                                let (edges', remain') := choice in
                                  (TCInductiveCaseRunOne m' (S n) path remain' amti stage_names locations (edges'::chain) a uop_chain req_edges inv_patterns)
                            end
                          in
                          (fold_left h_fold isa_choices None, S cur_index, num_choices)
                      end
                  end
              end
            in
            fst (fst (fold_left g_fold tran_conns (None, 1, List.length tran_conns)))
        | _ => Warning None ["Couldn't pull start/end of chain?"]
        end
    end
  | O => Warning None ["Recursed too deep in transitive chain case!"]
  end.

Fixpoint TCInductiveCase
  (n : nat)
  (amti : FOLFormula * FOLFormula * FOLFormula * FOLFormula)
  (stage_names : list (list string))
  (locations : list nat)
  (a : Microop)
  (b : Microop)
  (c : Microop)
  (pats : list ISAPattern)
  (inv_patterns : list (ISAPattern * ISAEdge))
  : option (list (list ISAEdge)) :=
  match pats with
  | [] => None
  | h::t => let h := Comment h (["Checking TC for ISA pattern: "] ++ (PrintISAPattern h)) in
            let fold_choices := FilterISAPeelChoices (GetInitialEdge false 100 h) true in
            let k_fold (prev_soln : option (list (list ISAEdge))) (choice : list ISAEdge * option ISAPattern) :=
              match prev_soln with
              | Some _ => prev_soln
              | None => 
                  let (edges, left) := choice in
                  TCInductiveCaseRunOne 100 n [] left amti stage_names locations [edges] a [b; c] [] inv_patterns
              end
            in
            match fold_left k_fold fold_choices None with
            | None =>
                let n := Comment n ["Passed Transitive Chain Inductive Case for an ISA pattern."] in
                TCInductiveCase n amti stage_names locations a b c t inv_patterns
            | Some s => Comment (Some s) ["Transitive Chain Inductive Case found a counterexample for an ISA pattern; returning."]
            end
  end.

Fixpoint SplitInvariantsHelper
  (invs : list FOLStatement)
  (inv_list : list FOLStatement)
  (other_list : list FOLStatement)
  : list (list FOLStatement) :=
  match invs with
  | [] => let f x := (x::other_list) in
          Map f inv_list
  | h::t => match h with
            | FOLAxiom _ => SplitInvariantsHelper t (h::inv_list) other_list
            | FOLMacroDefinition _ => SplitInvariantsHelper t inv_list (h::other_list)
            | FOLContextTerm _ => SplitInvariantsHelper t inv_list (h::other_list)
            end
  end.

Definition SplitInvariants
  (invs : list FOLStatement)
  : list (list FOLStatement) :=
  SplitInvariantsHelper invs [] [].

Fixpoint CreateInvProperty
  (pq : bool) (* Are we inside the quantifiers that need replacing? *)
  (uop_a : Microop) (* First microop of pair *)
  (uop_b : Microop) (* Second microop of pair *)
  (inv_name : string)
  (inv : FOLFormula)
  : FOLFormula :=
  match inv with
  (* The main implication. At present there can only be one of these in the invariant.
     i.e. You can only have HasDependency po+ i j => <something not containing HasDep po+>. *)
  | FOLOr (FOLNot a) b => match a with
                          | FOLPredicate (PredHasDependency s _ _) =>
                              if beq_string s inv_name then
                                (* Drop the dependency *)
                                Comment b ["Found invariant property!"]
                              else FOLOr
                                    (FOLNot (CreateInvProperty pq uop_a uop_b inv_name a))
                                    (CreateInvProperty pq uop_a uop_b inv_name b)
                          | _ => FOLOr
                                  (FOLNot (CreateInvProperty pq uop_a uop_b inv_name a))
                                  (CreateInvProperty pq uop_a uop_b inv_name b)
                          end
  | FOLName n f => FOLName n (CreateInvProperty pq uop_a uop_b inv_name f)
  | FOLExpandMacro _ _ => inv
  | FOLPredicate _ => inv
  | FOLNot f => FOLNot (CreateInvProperty pq uop_a uop_b inv_name f)
  | FOLOr a b => FOLOr (CreateInvProperty pq uop_a uop_b inv_name a) (CreateInvProperty pq uop_a uop_b inv_name b)
  | FOLAnd a b => FOLAnd (CreateInvProperty pq uop_a uop_b inv_name a) (CreateInvProperty pq uop_a uop_b inv_name b)
  (* Replace the first 2 microop quantifiers with just the single pair of uops that we want to check. *)
  | FOLForAll q f =>
      if pq then
        (* Quantifiers have already been replaced, move along. *)
        FOLForAll q (CreateInvProperty pq uop_a uop_b inv_name f)
      else
        match f with
        | FOLForAll q' f' =>
            (* Replace quantifiers and continue. *)
            (* A dummy FOL state... *)
            let s := (mkFOLState [] [] [] [] [] [] [] [] [] [] []) in
            let name_a := fst (q s []) in
            let name_b := fst (q' s []) in
            let quant_a := DummyQuantifier name_a uop_a in
            let quant_b := DummyQuantifier name_b uop_b in
            let quant_b := Comment quant_b ["Found quantifiers to replace..."] in
              FOLForAll quant_a (FOLForAll quant_b (CreateInvProperty true uop_a uop_b inv_name f'))
        | _ => (* We haven't yet found our quantifiers to replace. *)
          FOLForAll q (CreateInvProperty pq uop_a uop_b inv_name f)
        end
  | FOLExists q f => FOLForAll q (CreateInvProperty pq uop_a uop_b inv_name f)
  | FOLLet t f => FOLLet t (CreateInvProperty pq uop_a uop_b inv_name f)
  end.

Fixpoint GetInvEdge
  (inv : FOLFormula)
  : option ISAEdge :=
  match inv with
  (* The main implication. At present there can only be one of these in the invariant.
     i.e. You can only have HasDependency po+ i j => <something not containing HasDep po+>. *)
  | FOLOr (FOLNot a) b => match a with
                          | FOLPredicate (PredHasDependency s _ _) =>
                              Some (GetISAEdge s)
                          | _ => Warning None ["Implication"]
                          end
  | FOLName n f => GetInvEdge f
  | FOLExpandMacro _ _ => Warning None ["Macro"]
  | FOLPredicate _ => None
  | FOLNot f => GetInvEdge f
  | FOLOr a b
  | FOLAnd a b => 
      match (GetInvEdge a, GetInvEdge b) with
      | (Some e1, Some e2) => Warning (Some e1) ["Found an edge on both branches?"]
      | (Some e1, None) => Some e1
      | (None, Some e2) => Some e2
      | _ => Warning None ["And/or"]
      end
  | FOLForAll q f
  | FOLExists q f =>
      GetInvEdge f
  | FOLLet t f => GetInvEdge f
  end.

Fixpoint FindInv
  (inv_patterns : list (ISAPattern * ISAEdge))
  (inv : FOLFormula)
  : option (ISAPattern * ISAEdge) :=
  let inv_patterns := Comment inv_patterns [stringOfFOLFormula 100 inv] in
  match inv_patterns with
  | [] => None
  | h::t =>
      let (pat, edge) := h in
      match GetInvEdge inv with
      | None => Warning None ["Could not find inv edge!"]
      | Some inv_edge => if beq_isa_edge edge inv_edge then Some h else FindInv t inv
      end
  end.

Fixpoint GetPatternCases
  (n : nat)
  (pat : option ISAPattern)
  (existing : list (list ISAEdge))
  : list (list (list ISAEdge)) :=
  let f n'' x := 
    match x with
    | (y, z) => GetPatternCases n'' z (existing ++ [y])
    end
  in
  match n with
  | O => Warning [] ["Recursed too far in GetPatternCases!"]
  | S n' =>
      match pat with
      | None => [existing]
      | Some pat' =>
          let choices := GetInitialEdge false 100 pat' in
          let choices := Map (f n') choices in
          fold_left app_tail choices []
      end
  end.

Fixpoint GenUops
  (size : nat)
  : list Microop :=
  match size with
  | O => []
  | S n => (mkMicroop n 0 0 0 (Fence []))::(GenUops n)
  end.

Definition ProveInvBaseCase
  (m : Microarchitecture)
  (amti : FOLFormula * FOLFormula * FOLFormula * FOLFormula)
  (inv : FOLFormula)
  (inv_edge : ISAEdge)
  (chain : list (list ISAEdge))
  : bool :=
  (* Generate n+1 uops for the n edges... *)
  let uops := GenUops (S (List.length chain)) in
  (* Create the base case's chain... *)
  let layers_tree := CreateLayersTree false chain uops in
  let poss_uop_a := StartChain uops in
  let poss_uop_b := EndChain uops in
  match (poss_uop_a, poss_uop_b) with
  | (Some uop_a, Some uop_b) =>
      (* Create the invariant property that must be true for the invified abstraction (like po+). *)
      let inv_prop := CreateInvProperty false uop_a uop_b (GetISAEdgeString inv_edge) inv in
      (* A FOL state... *)
      let s := (mkFOLState [] [] [] [] [] [] [] uops [] [] []) in
      let amti_tree := CreateAMTITree s amti (StageNames m) in
      let inv_prop_tree := EliminateQuantifiers true true (StageNames m) s inv_prop [] in
      let inv_prop_tree := NegateScenarioTree inv_prop_tree in
      let amti_tree := ScenarioTreeEdgeCountGraph 5 amti_tree "amti" in
      let inv_prop_tree := ScenarioTreeEdgeCountGraph 5 inv_prop_tree "neg_inv_prop_tree" in
      let layers_tree := ScenarioTreeEdgeCountGraph 5 layers_tree "layers_tree" in
      let final_tree := ScenarioAnd (ScenarioAnd amti_tree inv_prop_tree) layers_tree in
      let final_tree := Comment final_tree ["Checking Invariant Base Case:"] in
      let result := FOL_DPLL 1000 [] [] [] (StageNames m) s final_tree DefaultStrat in
      match result with
      | Some s' => Warning false ["Invariant base case could not be proven!"]
      | None => let result := Comment true ["Inv base case for "; PrintISAEdge inv_edge; " passed!"] in result
      end
  | _ => Warning false ["Could not find start or end of chain when proving Inv base case!"]
  end.

Definition ProveInvIndCase
  (m : Microarchitecture)
  (amti : FOLFormula * FOLFormula * FOLFormula * FOLFormula)
  (inv : FOLFormula)
  (inv_edge : ISAEdge)
  (chain : list (list ISAEdge))
  : bool :=
  (* Generate n+1 uops for the n edges... *)
  let chain_len := S (List.length chain) in
  let uops := GenUops chain_len in
  (* And now the last uop for the inv edge from the IH. *)
  let uop_c := mkMicroop (S chain_len) 0 0 0 (Fence []) in
  (* Create the chain... *)
  let layers_tree := CreateLayersTree false chain uops in
  let poss_uop_a := StartChain uops in
  let poss_uop_b := EndChain uops in
  let uops := app_tail uops [uop_c] in
  match (poss_uop_a, poss_uop_b) with
  | (Some uop_a, Some uop_b) =>
      (* And the property that must hold, this time between a and c... *)
      let inv_prop := CreateInvProperty false uop_a uop_c (GetISAEdgeString inv_edge) inv in
      (* And the FOL state...*)
      let s := (mkFOLState [] [] [] [] [] [] [] uops [] [] []) in
      let amti_tree := CreateAMTITree s amti (StageNames m) in
      let inv_tree := EliminateQuantifiers true true (StageNames m) s inv [] in
      let inv_prop_tree := EliminateQuantifiers true true (StageNames m) s inv_prop [] in
      let inv_prop_tree := NegateScenarioTree inv_prop_tree in
      let concr_prop_tree := ScenarioAnd layers_tree
        (ScenarioPred (SymPredHasDependency uop_b uop_c inv_edge))
      in
      let amti_tree := ScenarioTreeEdgeCountGraph 5 amti_tree "amti" in
      let inv_tree := ScenarioTreeEdgeCountGraph 5 inv_tree "inv_tree" in
      let inv_prop_tree := ScenarioTreeEdgeCountGraph 5 inv_prop_tree "neg_inv_prop_tree" in
      let concr_prop_tree := ScenarioTreeEdgeCountGraph 5 concr_prop_tree "concr_prop_tree" in
      let final_tree := ScenarioAnd (ScenarioAnd (ScenarioAnd amti_tree inv_tree)
                          inv_prop_tree) concr_prop_tree in
      let final_tree := Comment final_tree ["Checking Invariant Inductive Case:"] in
      let result := FOL_DPLL 1000 [] [] [] (StageNames m) s final_tree DefaultStrat in
      match result with
      | None => Comment true ["Hooray! Invariant passed!"]
      | _ => Comment false ["Invariant inductive case failed!"]
      end
  | _ => Warning false ["Could not find start or end of chain when proving Inv inductive case!"]
  end.

Definition ProveInvariant
  (m : Microarchitecture)
  (amt : FOLFormula * FOLFormula * FOLFormula)
  (other_invs : FOLFormula)
  (inv : FOLFormula)
  : bool :=
  let amti := (amt, other_invs) in
  match FindInv InvPatterns inv with
  | None => Warning false ["Could not find invariant!"]
  | Some (pat, inv_edge) =>
      let pat := Comment pat ["Found invariant for "; PrintISAEdge inv_edge] in
      let base_cases := GetPatternCases 100 (Some pat) [] in
      let base_results := Map (ProveInvBaseCase m amti inv inv_edge) base_cases in
      if fold_left andb base_results true then
        (* Ok, now the inductive case. *)
        let ind_results := Map (ProveInvIndCase m amti inv inv_edge) base_cases in
        let result := fold_left andb ind_results true in
        let result := Comment result ["Inductive case for invariant "; PrintISAEdge inv_edge; " returned "; (if result then "true" else "false")] in
        result
      else
        Warning false ["Could not prove invariant for "; PrintISAEdge inv_edge]
  end.

Definition FoldInvs
  (l : list FOLFormula)
  : FOLFormula :=
  let f x y := FOLAnd x y in
  fold_left f l (FOLPredicate PredTrue).

Fixpoint ProveInvariantsHelper
  (n : nat)
  (m : Microarchitecture)
  (amt : FOLFormula * FOLFormula * FOLFormula)
  (invs : list FOLFormula)
  : bool :=
  match n with
  | O => true
  | S n' => match invs with
            | [] => Warning false ["nonzero invariants but empty list?"]
            | h::t => if ProveInvariant m amt (FoldInvs t) h then ProveInvariantsHelper n' m amt (t ++ [h]) else false
            end
  end.

Definition ProveInvariants
  (m : Microarchitecture)
  (amt : FOLFormula * FOLFormula * FOLFormula)
  (invs : list FOLStatement)
  : bool :=
  let invs := SplitInvariants invs in
  let invs := Map (fun x => [x]) invs in
  let invs := Map BuildMicroarchitecture invs in
  ProveInvariantsHelper (List.length invs) m amt invs.

Fixpoint GenISAEdgeTree
  (a : Microop)
  (b : Microop)
  (edges : list ISAEdge)
  : ScenarioTree :=
  match edges with
  | [] => ScenarioTrue
  | h::t => ScenarioAnd (ScenarioPred (SymPredHasDependency a b h)) (GenISAEdgeTree a b t)
  end.

Definition ISAChainFold
  (ret : ScenarioTree * list Microop * nat)
  (isa_edges : list ISAEdge)
  : ScenarioTree * list Microop * nat :=
  let '(tree, uops, gid) := ret in
  let last_uop := EndChain uops in
  match last_uop with
  | None => Warning (tree, uops, gid) ["No last uop in the chain?"]
  | Some last_uop' =>
      let new_uop := mkMicroop gid 0 0 0 (Fence []) in
      (ScenarioAnd tree (GenISAEdgeTree last_uop' new_uop isa_edges), (app_tail uops [new_uop]), S gid)
  end.

Definition FoldMicroopChain
  (ret : ScenarioTree * Microop)
  (cur_uop : Microop)
  : ScenarioTree * Microop :=
  let (tree, prev_uop) := ret in
  (ScenarioAnd tree (ISAEdgeInvifiedDisjunction prev_uop cur_uop), cur_uop).

Definition FoldMaxGid
  (n : nat)
  (a : Microop)
  : nat :=
  if (blt_nat n (globalID a)) then (globalID a) else n.

Definition GenCex
  (amti : FOLFormula * FOLFormula * FOLFormula * FOLFormula)
  (stage_names : list (list string))
  (left_uops : list Microop)
  (right_uops : list Microop)
  (tc_cex : list (list ISAEdge))
  : option (list (list ISAEdge)) :=
  let left_tree :=
    match left_uops with
    | [] => ScenarioTrue
    | h::t => fst (fold_left FoldMicroopChain t (ScenarioTrue, h))
    end
  in
  let right_tree :=
    match right_uops with
    | [] => ScenarioTrue
    | h::t => fst (fold_left FoldMicroopChain t (ScenarioTrue, h))
    end
  in
  let (mid_tree, all_uops) :=
    match (rev tc_cex) with
    | [] => (* There is no tran chain. If there are left and right components, add an ISAEdgeInvifiedDisjunction
               between them and move along. *)
            match (EndChain left_uops, StartChain right_uops) with
            | (Some cs, Some ce) => (ISAEdgeInvifiedDisjunction cs ce, app_tail left_uops right_uops)
            | _ => (ScenarioTrue, app_tail left_uops right_uops)
            end
    | h::t => (* The final i.e. "h" case needs to be handled manually. Rev back the t and pass it to the
                 fold below. *)
        let max_gid := fold_left FoldMaxGid left_uops 0 in
        let max_gid := fold_left FoldMaxGid right_uops max_gid in
        let max_gid := S max_gid in
        let (left_uops, chain_start) :=
          match EndChain left_uops with
          | None => let uop := (mkMicroop max_gid 0 0 0 (Fence [])) in
                      Comment ([uop], uop) ["No instrs in the left chain"]
          | Some cs => (left_uops, cs)
          end
        in
        (* Increment by one if we had to create a uop... *)
        let max_gid := if beq_nat max_gid (globalID chain_start) then S max_gid else max_gid in
        let (right_uops, chain_end) :=
          match StartChain right_uops with
          | None => let uop := (mkMicroop max_gid 0 0 0 (Fence [])) in
                      Comment ([uop], uop) ["No instrs in the right chain"]
          | Some ce => (right_uops, ce)
          end
        in
        let max_gid := if beq_nat max_gid (globalID chain_end) then S max_gid else max_gid in
        let '(tc_cex_tree, tc_cex_uops, _) := fold_left ISAChainFold (rev t) (ScenarioTrue, [chain_start], max_gid) in
        let tc_cex_uops :=
          match tc_cex_uops with
          | [] => Warning [] ["tc_cex_uops is empty?"]
          | h::t => t (* Drop chain_start from the beginning as it's already in left_uops, one way or another... *)
          end
        in
        let last_gen_uop :=
          match EndChain tc_cex_uops with
          | None => chain_start (* There was only one edge in the chain i.e. t was empty. Just add the edge between chain_start and chain_end. *)
          | Some e => e
          end
        in
        let tc_cex_tree := ScenarioAnd tc_cex_tree (GenISAEdgeTree last_gen_uop chain_end h) in
        (tc_cex_tree, app_tail (app_tail left_uops tc_cex_uops) right_uops)
    end
  in
  match (StartChain all_uops, EndChain all_uops) with
  | (Some dest, Some src) =>
      let total_tree := ScenarioAnd (ScenarioAnd (ScenarioAnd
                          (left_tree) (right_tree)) (mid_tree))
                          (ISAEdgeInvifiedDisjunction src dest)
      in
      (* Now, finally, pass this to the solver. *)
      let s := (mkFOLState [] [] [] [] [] [] [] all_uops [] [] []) in
      let amti_tree := CreateAMTITree s amti stage_names in
      let final_tree := ScenarioAnd amti_tree total_tree in
      let final_tree := Comment final_tree ["Checking candidate counterexample"] in
      match FOL_DPLL 1000 [] [] [] stage_names s final_tree DefaultStrat with
      | None => None (* This isn't the cex we're looking for. *)
      | Some s' => (* Hooray! We have our cex. *)
          Some (ConvertToISAChain (all_uops ++ [dest]) s')
      end
  | _ => Warning None ["No uops in all_uops?"]
  end.

Fixpoint GenCex2
  (steps_left : nat)
  (amti : FOLFormula * FOLFormula * FOLFormula * FOLFormula)
  (stage_names : list (list string))
  (chain : list (list ISAEdge))
  (pat : option ISAPattern)
  : option (list (list ISAEdge)) :=
  let f n'' x :=
    match x with
    | (y, z) => GenCex2 n'' amti stage_names (app_tail chain [y]) z
    end
  in
  let g x y :=
    match x with
    | Some _ => x
    | None => y
    end
  in
  match steps_left with
  | O => 
      (* We've added as much as we're supposed to. Now let's add the loopback edge and be done with it. *)
      match pat with
      | None => None (* We're out of axiom. *)
      | Some pat' =>
          let loops := GetSingleEdgeChoices pat' in
          (* Create the uops we need. *)
          let uops := GenUops (S (List.length chain)) in
          let poss_cycle_start := EndChain uops in
          let poss_cycle_end := StartChain uops in
          match (poss_cycle_start, poss_cycle_end) with
          | (Some cycle_start, Some cycle_end) =>
              let s := (mkFOLState [] [] [] [] [] [] [] uops [] [] []) in
              let amti_tree := CreateAMTITree s amti stage_names in
              let layers_tree := CreateLayersTree false chain uops in
              (* Now try all possibilities for the loopback edge. *)
              let l_fold (prev_soln : option (list (list ISAEdge))) (loop_edges : list ISAEdge) :=
                match prev_soln with
                | Some _ => prev_soln
                | None => let cex_tree := ScenarioAnd (ScenarioAnd amti_tree layers_tree) (ISAEdgeDisjunction cycle_start cycle_end [loop_edges]) in
                          match FOL_DPLL 1000 [] [] [] stage_names s cex_tree DefaultStrat with
                          | None => None
                          | Some s' => Some (ConvertToISAChain (app_tail uops [cycle_end]) s')
                          end
                end
              in
              fold_left l_fold loops None
          | _ => Warning None ["Created uops but couldn't get start/end of chain?"]
          end
      end
  | S n' =>
      match pat with
      | None => None (* We ran out of steps. *)
      | Some pat' =>
          (* Generate all possible next steps in the cycle. *)
          let choices := GetInitialEdge false 100 pat' in
          let results := Map (f n') choices in
          fold_left g results None
      end
  end.

(* Extracted to a function in BackendLinux.ml. *)
Definition LowerThanBound (n : nat) := false.

Fixpoint FindCex
  (n : nat)
  (pat : ISAPattern)
  (amti : FOLFormula * FOLFormula * FOLFormula * FOLFormula)
  (stage_names : list (list string))
  (cur_size : nat)
  : option (list (list ISAEdge)) :=
  match n with
  | S n' =>
      if LowerThanBound cur_size then
        let amti := Comment amti ["Checking for cycle cex of size "; stringOfNat (S cur_size)] in
        match GenCex2 cur_size amti stage_names [] (Some pat) with
        | None => FindCex n' pat amti stage_names (S cur_size)
        | Some cex => Some cex
        end
      else
        None
  | _ => Warning None ["Recursed too deep in FindCex."]
  end.

Definition Invariantify
  (e : ISAEdge)
  : ISAEdge :=
  match e with
  | EdgePO => EdgePO_plus
  | _ => e
  end.

Definition FoldEdgeChoices
  (edges : list ISAEdge)
  (new_choices : list (list ISAEdge))
  (choice : list ISAEdge)
  : list (list ISAEdge) :=
  app_tail new_choices (Map (fun x => (x::choice)) edges).

Fixpoint GenAdditionsList
  (depth : nat)
  (edges : list ISAEdge)
  (additions : list (list ISAEdge))
  : list (list ISAEdge) :=
  match depth with
  | O => additions
  | S n' =>
      let additions :=
        match edges with
        | [] => Warning additions ["Could not find any edges to add to the choices!"]
        | _ => fold_left (FoldEdgeChoices edges) additions []
        end
      in
      GenAdditionsList n' edges additions
  end.

Fixpoint GenCexGrow
  (max_depth : nat)
  (cur_depth : nat) (* number of edges in a choice - 1 *)
  (amti : FOLFormula * FOLFormula * FOLFormula * FOLFormula)
  (stage_names : list (list string))
  (chain : list (list ISAEdge))
  (remnants : list (option ISAPattern))
  : list (list ISAEdge) :=
  let f x y :=
    match x with
    | Some _ => x
    | None => y
    end
  in
  match max_depth with
  | O => Warning [] ["Could not concretize TC Cex!"]
  | S n' =>
      let results := Map (GenCex2 cur_depth amti stage_names chain) remnants in
      match fold_left f results None with
      | None =>
          (* Try again with a higher depth. *)
          GenCexGrow n' (S cur_depth) amti stage_names chain remnants
      | Some s => s
      end
  end.

Fixpoint GetRemainingPatterns
  (pat : option ISAPattern)
  (l : list (list ISAEdge))
  : list (option ISAPattern) :=
  let f x y z :=
    match z with
    | (a, b) =>
        let a := Comment a (["Checking "] ++ (PrintISAChain [a]) ++ [" against "] ++ (PrintISAChain [x])) in
        let invified := InvariantifyChain [a] in
        match invified with
        | [a'] =>
            if orb (ISASubsetOf a x) (ISASubsetOf a' x) then GetRemainingPatterns b y else []
        | _ => Warning [] ["Non-single-element list when invariantifying to get remaining patterns..."]
        end
    end
  in
  match l with
  | [] => [pat]
  | h::t =>
      match pat with
      | None => []
      | Some pat' =>
          let pat' := Comment pat' (["pat' is "] ++ (PrintISAPattern pat')) in
          let choices := FilterISAPeelChoices (GetInitialEdge false 100 pat') false in
          let results := Map (f h t) choices in
          fold_left app_tail results []
      end
  end.

(* Extracted to a function in BackendLinux.ml. *)
Definition DoGenCex (b : bool) := false.

Definition GenCounterexample
  (pat : ISAPattern)
  (amti : FOLFormula * FOLFormula * FOLFormula * FOLFormula)
  (stage_names : list (list string))
  (chain : list (list ISAEdge))
  : list (list ISAEdge) :=
  (* First, see if the user wants to search for a cyclic counterexample. *)
  if DoGenCex true then
    let amti := Comment amti ["Checking for cyclic counterexamples..."] in
    match FindCex 100 pat amti stage_names 0 with
    | Some cex => cex
    | None =>
          Warning [] ["Could not find cyclic cex within bound"]
    end
  else
    [].

Definition BuildBaseCasePropertyTree
  (a b : Microop)
  (l : list nat)
  (pat : ISAPattern)
  (inv_patterns : list (ISAPattern * ISAEdge))
  : ScenarioTree :=
  let init_edges := GetISAEdges (GetInitialEdge false 100 pat) in
  let f x := 
    match fst (ReplaceWithInvariants [x] [a; b] inv_patterns) with
    | [h] => h
    | _ => Warning x ["Lists are messed up in TC check base case..."]
    end
  in
  let init_edges := Map f init_edges in
  let init_edges := Comment init_edges (["TC base case choices are: "] ++ (PrintISAChain init_edges)) in
  ScenarioAnd (ISAEdgeDisjunction a b init_edges) (ScenarioNotEdgeLeaf (AllConnections a b l l)).

Definition TransitiveChain
  (max_depth : nat)
  (m : Microarchitecture)
  (pattern : ISAAxiom)
  (inv_patterns : list (ISAPattern * ISAEdge))
  : option (list (list ISAEdge)) :=
  match (pattern, FilterUspecInput m [] [] [] []) with
  | (Irr pat, (axioms, mapping, theory, inv)) =>
      let axioms := BuildMicroarchitecture [axioms] in
      let mapping := BuildMicroarchitecture [mapping] in
      let theory := BuildMicroarchitecture [theory] in
      let axioms := PrintTimestamp axioms "Inv_proof_start" in
      if negb (ProveInvariants m (axioms, mapping, theory) inv) then
        let result := Some [] in
        let result := PrintTimestamp result "Inv_proof_end_failure" in
        Warning result ["Invariants could not be proven! Aborting."]
      else
      (* Begin with the base case. 2 instructions, A and B. The params of the uop have
         no meaning besides the global ID, since everything else will be a variable.
         Fences are the easiest to create so I've made them both fences. *)
      let inv := PrintTimestamp inv "Inv_proof_end_success" in
      let inv := BuildMicroarchitecture [inv] in
      let uop_a := mkMicroop 0 0 0 0 (Fence []) in
      let uop_b := mkMicroop 1 0 0 0 (Fence []) in
      let s := (mkFOLState [] [] [] [] [] [] [] [uop_a; uop_b] [] [] []) in
      let locations := GetLocations m [] in
      let property_tree := BuildBaseCasePropertyTree uop_a uop_b locations pat inv_patterns in
      let amti := (axioms, mapping, theory, inv) in
      let amti_tree := CreateAMTITree s amti (StageNames m) in
      let final_tree := ScenarioAnd amti_tree property_tree in
      let final_tree := Comment final_tree ["Checking Transitive Chain Base Case:"] in
      let result := FOL_DPLL max_depth [] [] [] (StageNames m) s final_tree DefaultStrat in
      match result with
      | Some s' => let s' := Comment s' ["Transitive Chain Base Case returned SAT! Failing fragment is:"] in
                   let fail_frag := ConvertToISAChain [uop_a; uop_b] s' in
                   let fail_frag := Comment fail_frag (PrintISAChain fail_frag) in
                    Some (GenCounterexample pat amti (StageNames m) fail_frag)
      | None => let result := Comment result ["Transitive Chain Base Case returned UNSAT"] in
                let result := Comment result ["Checking Transitive Chain Inductive Case:"] in
                (* Now the inductive case. *)
                (* The third instruction. *)
                let uop_c := mkMicroop 2 0 0 0 (Fence []) in
                (* Rip the last part off the pattern to give us all possible TCs. *)
                let tchains := GetAllTranChains pat in
                let tchains := Comment tchains (["The tranchains are: "] ++ (PrintISAPatterns tchains)) in
                let tchains := Comment tchains ["Length of GetAllTranChains is "; stringOfNat (List.length tchains)] in
                let tchains := Map (GetAllSubchains 100 []) tchains in
                let tchains := fold_left FoldISAChains tchains [] in
                let tchains := Comment tchains (["The folded tranchains are: "] ++ (PrintISAPatterns tchains)) in
                let tchains := Comment tchains ["Length of folded ISA chains is "; stringOfNat (List.length tchains)] in
                match TCInductiveCase 3 amti (StageNames m) locations uop_a uop_b uop_c tchains inv_patterns with
                | Some s'' => let s'' := Comment s'' ("TC failing fragment is "::(PrintISAChain (rev s''))) in
                    Comment (Some (GenCounterexample pat amti (StageNames m) s'')) ["Transitive Chain Inductive Case returned SAT!"]
                | None => Comment None ["Transitive Chain Inductive Case returned UNSAT."]
                end
      end
  end.

(* Checks if everything in l is in l'. This equates to checking if the new scenario is just a more constrained version of the older one. *)
Fixpoint ISAListCoveredBy
  (l l' : list ISAEdge)
  : bool :=
  match l with
  | [] => true
  | h::t => if find (beq_isa_edge h) l' then ISAListCoveredBy t l' else false
  end.

Fixpoint ISAEdgesMatch
  (edges edges' : list (list ISAEdge))
  : bool :=
  match (edges, edges') with
  | ([], []) => true
  | (h::t, h'::t') => if ISAListCoveredBy h h' then ISAEdgesMatch t t' else false
  | _ => Warning false ["ISA cycle lengths don't match?"]
  end.

Definition beq_tran_conn
  (tc tc' : GraphEdge)
  : bool :=
  match (tc, tc') with
  | (((_, (_, src)), (_, (_, dest)), _, _), ((_, (_, src')), (_, (_, dest')), _, _)) =>
      andb (beq_nat src src') (beq_nat dest dest')
  end.

Definition ReplaceUops
  (left_tc right_tc : Microop)
  (e : GraphEdge)
  : GraphEdge :=
  match e with
  | ((_, (_, s)), ((_, (_, d))), _, _) => ((left_tc, (coreID left_tc, s)), ((right_tc, (coreID right_tc, d))), "", "")
  end.

Definition ConjoinNegatedTranConns
  (left_tc right_tc : Microop)
  (l : list GraphEdge)
  (tree : ScenarioTree)
  : ScenarioTree :=
  match l with
  | [] => tree
  | _ => let l := Map (ReplaceUops left_tc right_tc) l in
         ScenarioAnd tree (ScenarioNotEdgeLeaf l)
  end.

Definition ISACycleMatch
  (check_req_edges : bool)
  (checked : list (list ISAEdge) * (list GraphEdge))
  (case : list (list ISAEdge) * GraphEdge)
  (params : FOLState * ScenarioTree * list (list string))
  (left_tc right_tc : option Microop)
  : bool :=
  let (edges, conns) := checked in
  let (edges', conn') := case in
  (* A peephole optimization... *)
  if beq_nat (List.length edges) (List.length edges') then
    let edges :=
      if PrintFlag 2 then
        Comment edges ["Edge lists are the same length..."]
      else
        edges
      in
      if ISAEdgesMatch edges edges' then
        let conns := Comment conns ["ISA chains match:"; newline] in
        let conns := Comment conns (["ISACycle1: "] ++ (PrintISAChain edges) ++ [newline; "   ISACycle2: "] ++ (PrintISAChain edges')) in
        let conns := Comment conns ["Conn is "; GraphvizStringOfGraphEdge [] "" conn'] in
        let conns := PrintEdgeList conns conns in
        if check_req_edges then
          (* Check if our current scenario is a decomposition of the case checked earlier. *)
          match (left_tc, right_tc) with
          | (Some left_tc', Some right_tc') =>
              let '(s, cur_tree, stage_names) := params in
              let cur_tree := ScenarioAnd cur_tree (ConjoinNegatedTranConns left_tc' right_tc' conns ScenarioTrue) in
              match FOL_DPLL 1000 [] [] [] stage_names s cur_tree (DefaultStrat) with
              | None => true
              | Some _ => false
              end
          | _ => Warning false ["No TC ends when checking req edges for memoization?"]
          end
        else
          (* Just compare the conns. *)
          (* beq_tran_conn takes symmetry into account... *)
          if find (beq_tran_conn conn') conns then
            let result :=
              if PrintFlag 2 then
                Comment true ["Tran conn found..."]
              else
                true
              in
            result
          else
            false
      else
        false
  else
    false.


Fixpoint ISACycleInHelper
  (check_req_edges : bool)
  (checked_cases : list (list (list ISAEdge) * (list GraphEdge)))
  (case : list (list ISAEdge) * GraphEdge)
  (params : FOLState * ScenarioTree * list (list string))
  (left_tc right_tc : option Microop)
  : bool :=
  match checked_cases with
  | [] => false
  | h::t => if ISACycleMatch check_req_edges h case params left_tc right_tc then
              true
            else
              ISACycleInHelper check_req_edges t case params left_tc right_tc
  end.

Definition Canonicalise
  (e : ISAEdge)
  : list (list ISAEdge) :=
  match e with
  | EdgeFencePO_plus => [[EdgeFence_plus]; [EdgePO_plus]]
  | EdgePOFence_plus => [[EdgePO_plus]; [EdgeFence_plus]]
  | EdgeFencePPO_plus => [[EdgeFence_plus]; [EdgePPO_plus]]
  | EdgePPOFence_plus => [[EdgePPO_plus]; [EdgeFence_plus]]
  | _ => [[e]]
  end.

Fixpoint CanonicaliseChainHelper
  (chain ret : list (list ISAEdge))
  : list (list ISAEdge) :=
  match chain with
  | [] => ret
  | h::t => match h with
            | [edge] => CanonicaliseChainHelper t (ret ++ (Canonicalise edge))
            | _ => Warning [] ["Found multiple edges when trying to canonicalise chain!"]
            end
  end.

Fixpoint MergeIdenticalInvs
  (chain : list (list ISAEdge))
  : list (list ISAEdge) :=
  match chain with
  | [] => []
  | h::t => match t with
            | [] => chain
            | h'::t' =>
                match (h, h') with
                | ([EdgePO_plus], [EdgePO_plus])
                | ([EdgePO_loc_plus], [EdgePO_loc_plus])
                | ([EdgeFence_plus], [EdgeFence_plus])
                | ([EdgePPO_plus], [EdgePPO_plus]) => h::(MergeIdenticalInvs t')
                | _ => h::(MergeIdenticalInvs t)
                end
            end
  end.

Definition CanonicaliseChain
  (chain : list (list ISAEdge))
  : list (list ISAEdge) :=
  CanonicaliseChainHelper chain [].

(* How many elements from either end do we toss when trying to find memoized matches? *)
(* This function is implemented in BackendLinux.ml. *)
Definition BelowMemoThreshold (n : nat) := false.

Definition ISACycleInChop
  (checked_cases : list (list (list ISAEdge) * (list GraphEdge)))
  (chain : list (list ISAEdge))
  (conn : GraphEdge)
  (uops : list Microop)
  (params : FOLState * ScenarioTree * list (list string))
  (n : nat) (* How much to chop from the head or the tail *)
  : bool :=
  if bgt_nat (List.length chain) n then
    let uops' := ChopTailNum n uops in
    let chain' := ChopTailNum n chain in
    (* Only check required edges if you're chopping things off the chain (i.e. checking decompositions). *)
    if ISACycleInHelper (bgt_nat n 0) checked_cases (chain', conn) params (EndChain uops') (StartChain uops') then
      true
    else if bgt_nat n 0 then (* If n = 0, the chopHead and chopTail cases do the same thing, so don't check again... *)
      let uops' := ChopHeadNum n uops in
      let chain' := ChopHeadNum n chain in
      ISACycleInHelper true checked_cases (chain', conn) params (EndChain uops') (StartChain uops')
    else
      false
  else
    false.

Fixpoint ISACycleIn
  (m : nat)
  (checked_cases : list (list (list ISAEdge) * (list GraphEdge)))
  (chain : list (list ISAEdge))
  (conn : GraphEdge)
  (uops : list Microop)
  (params : FOLState * ScenarioTree * list (list string))
  (n : nat) (* How much are we chopping off this time? *)
  : bool :=
  match m with
  | S m' =>
    if BelowMemoThreshold n then
      if ISACycleInChop checked_cases chain conn uops params n then
        true
      else
        ISACycleIn m' checked_cases chain conn uops params (S n)
    else
      false
  | O => Warning false ["Recursed too far in ISACycleIn!"]
  end.

Definition ReverseEdge
  (e : ISAEdge)
  : ISAEdge :=
  match e with
  | EdgeFencePO_plus => EdgePOFence_plus
  | EdgePOFence_plus => EdgeFencePO_plus
  | EdgeFencePPO_plus => EdgePPOFence_plus
  | EdgePPOFence_plus => EdgeFencePPO_plus
  | _ => e
  end.

Definition ReverseEdgeList
  (l : list ISAEdge)
  : list ISAEdge :=
  Map ReverseEdge l.

Definition ReverseChain
  (l : list (list ISAEdge))
  : list (list ISAEdge) :=
  let l := rev l in
  Map ReverseEdgeList l.

(* Extracted to an fn in BackendLinux.ml... *)
Definition UseISASym (n : nat) := false.

(* TC is the loopback... *)
Fixpoint CycleCheckSolveOne
  (m n : nat)
  (peel_left : bool)
  (path : list (nat * nat * option (list (list ISAEdge))))
  (uops : list Microop)
  (chain : list (list ISAEdge))
  (remain : option ISAPattern)
  (amti : FOLFormula * FOLFormula * FOLFormula * FOLFormula)
  (stage_names : list (list string))
  (locations : list nat)
  (req_edges : list GraphEdge)
  (inv_patterns : list (ISAPattern * ISAEdge))
  (checked_cases : list (list (list ISAEdge) * (list GraphEdge)))
  (excluded_edges : list (list ISAEdge))
  : option (list (list ISAEdge)) * list (list (list ISAEdge) * (list GraphEdge)) :=
  match m with
  | S m' =>
    match remain with
    | Some pat =>
    let s := (mkFOLState [] [] [] [] [] [] [] uops [] [] []) in
    let s := Printf s (StringOf [newline; "//CycleCheckSolveOne (g_fold) start, depth "; stringOfNat n; ";"; newline]) in
    let s := Comment s (["Remaining ISA pattern is: "] ++ (PrintISAPattern pat)) in
    let s := Comment s (["Current Path is: "] ++ (Map StringOfPiProofState (rev path))) in
    let s := Comment s ["Current instructions are:"] in
    let s := PrintMicroopChain s uops in
    let s := Comment s (["ISA chain is "] ++ (PrintISAChain chain)) in
    let amti_tree := CreateAMTITree s amti stage_names in
    let layers := CreateLayersTree false chain uops in
    let left_tc := EndChain uops in
    let right_tc := StartChain uops in
    (* There is no "property" here, it's just whether or not you can get a SAT assignment. *)
    match (left_tc, right_tc) with
    | (Some left_tc', Some right_tc') =>
        let left_tc := left_tc' in
        let right_tc := right_tc' in
        let tran_conns := AllConnections left_tc right_tc locations locations in
        let tran_conns := Comment tran_conns ["There are "; stringOfNat (List.length tran_conns);
                            " possible transitive connections."] in
        let req_edges_tree := fold_left (FoldFlipEdge false) req_edges ScenarioFalse in
        let filter_tree := ScenarioAnd amti_tree layers in
        let (filt_strat_1, filt_strat_2) :=
          if IsFilterStrat 0 then
            let res := Comment (FilterOnly, FilterOnly) ["Strat was 0"] in res
          else if IsFilterStrat 1 then
            let res := Comment (DoNothing, FilterOnly) ["Strat was 1"] in res
          else if IsFilterStrat 2 then
            let res := Comment (DoNothing, FilterAndCover) ["Strat was 2"] in res
          else
            let res := Comment (FilterAndCover, FilterAndCover) ["Strat was 3"] in res
        in
        let tran_conns_filt := FilterTranConns filt_strat_1 tran_conns s filter_tree req_edges_tree stage_names in
        (* If we have an invariant that can be applied from the left and from the right, and they're mutually exclusive, we'll prefer the left. *)
        let '(chain, uops) := ReplaceWithInvariantsOuter chain uops inv_patterns in
        let chain := Comment chain (["New ISA chain is "] ++ (PrintISAChain chain)) in
        let s := (mkFOLState [] [] [] [] [] [] [] uops [] [] []) in
        let s := Comment s ["New instructions are:"] in
        let s := PrintMicroopChain s uops in
        let amti_tree := CreateAMTITree s amti stage_names in
        let layers := CreateLayersTree false chain uops in
        let filter_tree := ScenarioAnd amti_tree layers in
        let req_edges := FilterReqEdges uops req_edges in
        let req_edges_tree := fold_left (FoldFlipEdge false) req_edges ScenarioFalse in
        let f x :=
          match x with
          | ConnSet x' _ => x'
          end
        in
        let tran_conns :=
          match (filt_strat_1, filt_strat_2) with
          | (FilterOnly, CoverOnly) => Map f tran_conns_filt (* the covered sets will be empty because no covering was done - see FilterTranConns *)
          | _ => tran_conns
          end
        in
        let tran_conns_inv := FilterTranConns filt_strat_2 tran_conns s filter_tree req_edges_tree stage_names in
        let tran_conns :=
          match (filt_strat_1, filt_strat_2) with
          | (FilterAndCover, FilterAndCover) =>
              if orb (negb (SubsetOf (Map f tran_conns_filt) (Map f tran_conns_inv))) (negb (SubsetOf (Map f tran_conns_inv) (Map f tran_conns_filt))) then
                Warning tran_conns_inv ["Filtered transitive connections did NOT match for inv and non-inv versions!"]
              else
                Comment tran_conns_inv ["Filtered transitive connections matched for inv and non-inv versions!"]
          | _ => tran_conns_inv
          end
        in
        let tran_conns := Comment tran_conns ["After filtering, there are "; stringOfNat (List.length tran_conns);
                            " possible transitive connections."] in
        let tran_conns := Comment tran_conns ["Recursing over all those transitive connections..."] in
        let partial_tree := ScenarioAnd amti_tree layers in
        (* Peeling off choices... *)
        let isa_choices :=
          if peel_left then
            FilterNextChoices peel_left chain (FilterISAPeelChoices (GetInitialEdge false 100 pat) true) inv_patterns excluded_edges
          else
            FilterNextChoices peel_left chain (FilterISAPeelChoices (GetFinalEdge 100 pat) true) inv_patterns excluded_edges
        in
        let g_fold (prev : option (list (list ISAEdge)) * list (list (list ISAEdge) * (list GraphEdge)) * nat * nat) (covset : CoverSet) :=
          let (conn, covered) :=
            match covset with
            | ConnSet conn' covered' => (conn', covered')
            end
          in
          let '(prev_soln, checked_cases', cur_index, num_choices) := prev in
          let path := ((cur_index, num_choices, Some chain)::path) in
          let s := Comment s (["Checking Path: "]
            ++ (Map StringOfPiProofState (rev path))
          ) in
          match prev_soln with
          | Some s' => (prev_soln, checked_cases', S cur_index, num_choices) (* Return the existing soln... *)
          | None =>
              let cur_tree := ScenarioAnd partial_tree (ScenarioEdgeLeaf [conn]) in
              let cur_tree := Printf cur_tree (StringOf ["//Adding edge "; GraphvizStringOfGraphEdge [] "" conn]) in
              (* Prepare the current case to add to our list of checked scenarios later if this branch is successfully verified. *)
              let case_to_add := (CanonicaliseChain chain, (conn::covered)) in
              match FOL_DPLL 1000 [] req_edges [] stage_names s cur_tree DefaultStrat with
              | None =>
                  Comment (None, checked_cases', S cur_index, num_choices) ["CycleCheckSolveOne depth "; stringOfNat n; " returned UNSAT!"]
              | Some s' =>
                  let partial_tree := Comment partial_tree ["Abstract counterexample found; ";
                    "CycleCheckSolveOne depth "; stringOfNat n; " returned SAT!"] in
                  let concr_choices := GetSingleEdgeChoices pat in
                  (* Ok, first let's try and concretize with the current number of instructions. *)
                  let concr_tree := ScenarioAnd partial_tree (ISAEdgeDisjunction left_tc right_tc concr_choices) in
                  let req_edges := PrintTimestamp req_edges "concr_start" in
                  match FOL_DPLL 1000 [] req_edges [] stage_names s concr_tree (HasDepStrat true) with
                  | Some s' =>
                      match StartChain uops with
                      | None => Warning (None, checked_cases', S cur_index, num_choices) ["Concretized but couldn't pull the start of the uop chain?"]
                      | Some chain_start_uop =>
                          Comment (Some (ConvertToISAChain (uops ++ [chain_start_uop]) s'), checked_cases',
                            S cur_index, num_choices) ["Concretized with "; stringOfNat n; " instrs!"]
                      end
                  | None => let req_edges := Comment req_edges ["Could not concretize with "; stringOfNat n; " instrs. Peeling off layer."] in
                      (* Now we peel off a layer and repeat the process. *)
                      (* First, add the current transitive connection to the required edges. *)
                      let req_edges := PrintTimestamp req_edges "concr_end" in
                      let req_edges := (conn::req_edges) in
                      (* Now create the new uop and add it to the chain. *)
                      let uop_b'' := mkMicroop n 0 0 0 (Fence []) in
                      let uops :=
                        if peel_left then
                          app_tail uops [uop_b'']
                        else
                          (uop_b''::uops)
                      in
                      (* And now call the solver once for each possible ISA-level edge that we could be
                         peeling off the chain. *)
                      let h_fold (prev_soln' : option (list (list ISAEdge)) * list (list (list ISAEdge) * (list GraphEdge))) (choice : list ISAEdge * option ISAPattern) :=
                        let prev_soln' := Comment prev_soln' ["In h_fold"] in
                        match prev_soln' with
                        | (Some _, _) => prev_soln'
                        | (None, checked_cases'') => 
                            let (edges', remain') := choice in
                            let chain :=
                              if peel_left then
                                app_tail chain [edges']
                              else
                                (edges'::chain)
                            in
                              (CycleCheckSolveOne m' (S n) (negb peel_left) path uops chain remain'
                                amti stage_names locations req_edges inv_patterns checked_cases'' excluded_edges)
                        end
                      in
                      let (result, checked_cases_ret) := fold_left h_fold isa_choices (None, checked_cases') in
                      match result with
                      | None =>
                          (result, checked_cases_ret, S cur_index, num_choices)
                      | Some _ => (result, checked_cases_ret, S cur_index, num_choices)
                      end
                  end
              end
          end
        in
        fst (fst (fold_left g_fold tran_conns (None, checked_cases, 1, List.length tran_conns)))
      | _ => Warning (None, []) ["No ops in one or both chains???"]
      end
    | None => Warning (None, []) ["An empty remaining pattern passed to CycleCheckSolveOne?"]
    end
    | O => Warning (None, []) ["Recursed too deep in cycle check case!"]
    end.

Fixpoint CycleCheckSolve
  (n : nat)
  (amti : FOLFormula * FOLFormula * FOLFormula * FOLFormula)
  (stage_names : list (list string))
  (locations : list nat)
  (pat : ISAPattern)
  (uops : list Microop)
  (inv_patterns : list (ISAPattern * ISAEdge))
  : option (list (list ISAEdge)) :=
  let pat := Comment pat (["Checking cycles for ISA pattern: "] ++ (PrintISAPattern pat)) in
  let fold_choices := FilterISAPeelChoices (GetFinalEdge 100 pat) true in
  let k_fold (prev_soln : option (list (list ISAEdge)) * list (list (list ISAEdge) * (list GraphEdge)) * list (list ISAEdge) * bool) (choice : list ISAEdge * option ISAPattern) :=
    match prev_soln with
    | (Some _, _, _, _) => prev_soln
    | (None, checked_cases, excluded_edges, peel_left) => 
        let (edges, left) := choice in
        let excluded_edges' :=
          if UseISASym 1 then
            Comment (edges::excluded_edges) ["Using Ultimate ISA-level symmetry!"]
          else
            excluded_edges
        in
        (CycleCheckSolveOne 100 n peel_left [] uops [edges] left amti stage_names locations [] inv_patterns checked_cases excluded_edges,
            excluded_edges', negb peel_left)
    end
  in
  match fold_left k_fold fold_choices (None, [], [], false) with
  | (None, _, _, _) => Comment None ["Passed Cycle check for an ISA level pattern."]
  | (Some s, _, _, _) => Comment (Some s) ["Cycle Check found a counterexample for an ISA pattern; returning."]
  end.
  
Definition CycleCheck
  (max_depth : nat)
  (m : Microarchitecture)
  (pattern : ISAAxiom)
  (inv_patterns : list (ISAPattern * ISAEdge))
  : option (list (list ISAEdge)) :=
  match (pattern, FilterUspecInput m [] [] [] []) with
  | (Irr pat, (axioms, mapping, theory, inv)) =>
      let axioms := BuildMicroarchitecture [axioms] in
      let mapping := BuildMicroarchitecture [mapping] in
      let theory := BuildMicroarchitecture [theory] in
      (* Invariants should already have been proven... *)
      let inv := BuildMicroarchitecture [inv] in
      (* First the "base case", an instruction with a cycle to itself. *)
      let uop := mkMicroop 0 0 0 0 (Fence []) in
      let s := (mkFOLState [] [] [] [] [] [] [] [uop] [] [] []) in
      let locations := GetLocations m [] in
      let chain := GetSingleEdgeChoices pat in
      let uops := [uop; uop] in
      let f x := 
        match fst (ReplaceWithInvariants [x] uops inv_patterns) with
        | [h] => h
        | _ => Warning x ["Lists are messed up in cycle check base case..."]
        end
      in
      let chain := Map f chain in
      let property_tree := ISAEdgeDisjunction uop uop chain in
      let amti_tree := CreateAMTITree s (axioms, mapping, theory, inv) (StageNames m) in
      let final_tree := ScenarioAnd amti_tree property_tree in
      let final_tree := Comment final_tree ["Checking cycle base case:"] in
      let result := FOL_DPLL max_depth [] [] [] (StageNames m) s final_tree DefaultStrat in
      match result with
      | Some s' => let s' := Comment s' ["Cycle check base case returned SAT; returning"] in
                    Some (ConvertToISAChain [uop; uop] s')
      | None => 
          (* Now for all other cycles. *)
          (* Begin with 2 instructions, A and B. The params of the uop have
             no meaning besides the global ID, since everything else will be a variable.
             Fences are the easiest to create so I've made them both fences. *)
          let uop_a := mkMicroop 0 0 0 0 (Fence []) in
          let uop_b := mkMicroop 1 0 0 0 (Fence []) in
          let locations := GetLocations m [] in
          match CycleCheckSolve 2 (axioms, mapping, theory, inv) (StageNames m) locations pat [uop_a; uop_b] inv_patterns with
          | Some s'' => Comment (Some s'') ["Cycle check returned SAT, returning."]
          | None => Comment None ["Cycle check returned UNSAT."]
          end
      end
  end.

Definition SeqConst :=
  [
    Acyclic (Union (Union (Union (Rel EdgeRF) (Rel EdgeFR)) (Rel EdgeCO)) (Rel EdgePO))
  ].

Definition TSO :=
  [
    Acyclic (Union (Union (Union (Union (Rel EdgePPO) (Rel EdgeCO)) (Rel EdgeRFE)) (Rel EdgeFR)) (Rel EdgeFence));
    Acyclic (Union (Union (Union (Rel EdgePO_loc) (Rel EdgeRF)) (Rel EdgeCO)) (Rel EdgeFR))
  ].

Definition ISAMcm := list ISAAxiom.

Fixpoint CheckAxioms
  (max_depth : nat)
  (m : Microarchitecture)
  (l : list ISAAxiom)
  : option (list (list ISAEdge)) :=
  match l with
  | [] => None
  | h::t =>
      let h := PrintTimestamp h "Axiom_start" in
      match h with
      | Irr pat =>
          let max_depth := PrintTimestamp max_depth "TC_start" in
          match TransitiveChain max_depth m h InvPatterns with
          | None =>
              let h := PrintTimestamp h "TC_end_success" in
              let h := Comment h (["Transitive chain passed successfully for "] ++ (PrintISAPattern pat)) in
                      let h := PrintTimestamp h "CycleCheck_start" in
                      match CycleCheck max_depth m h InvPatterns with
                      | None => 
                          let t := PrintTimestamp t "CycleCheck_end_success" in
                          let t := PrintTimestamp t "Axiom_end_success" in
                          let t := Comment t (["Cycle check passed successfully for "] ++ (PrintISAPattern pat)) in
                                CheckAxioms max_depth m t
                      | Some l =>
                          let l := PrintTimestamp l "CycleCheck_end_failure" in
                          let l := PrintTimestamp l "Axiom_end_failure" in
                          let result := Some l in
                          let result := Comment result (["CycleCheck failed for "] ++ (PrintISAPattern pat)) in
                          Comment result (PrintISAChain l)
                      end
          | Some l =>
              let l := PrintTimestamp l "TC_end_failure" in
              let l := PrintTimestamp l "Axiom_end_failure" in
              let result := Some l in
              let result := Comment result (["Transitive chain failed for "] ++ (PrintISAPattern pat)) in
              Comment result (["Counterexample below if generation requested:"; newline] ++ (PrintISAChain l))
          end
      end
  end.

Fixpoint EvaluateUHBGraphs
  (max_depth : nat)
  (m : Microarchitecture)
  (isa_mcm : ISAMcm)
  : option (list GraphEdge * list ArchitectureLevelEdge) :=
  let max_depth := PrintTimestamp max_depth "Total_Start" in
  let result :=
    match CheckAxioms max_depth m isa_mcm with
    | None => None
    | Some _ => Some ([], []) (* Doesn't matter what the fn returns, only if it's None/Some...*)
    end
  in
  PrintTimestamp result "Total_End".

Inductive ExpectedResult : Set :=
  Permitted | Forbidden | Required | Unobserved.
