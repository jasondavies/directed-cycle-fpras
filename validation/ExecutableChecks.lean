module

public meta import DirectedCycleFPRAS.RationalProgram
public meta import DirectedCycleFPRAS.RationalRejection
public meta import DirectedCycleFPRAS.RationalCounting
public meta import DirectedCycleFPRAS.ExecutableFPRAS
public meta import DirectedCycleFPRAS.RationalAlgorithmS

public meta import DirectedCycleFPRAS.RationalExecution
public meta import DirectedCycleFPRAS.ExecutableGraph

meta section

open DirectedCycleFPRAS

-- Exercise actual rational comparisons at grid boundaries, not real-valued semantics.
def third : RatLaw 2 := RatLaw.norm (fun i => if i = 0 then 1 else 2) 0
#guard (third.select 3 ⟨2, by decide⟩).val = 0
#guard (third.select 3 ⟨3, by decide⟩).val = 1
#guard third.searchUpper 3 ⟨2, by decide⟩ 2 0 = (0,1)
#guard third.searchUpper 3 ⟨3, by decide⟩ 2 0 = (1,2)
#guard (RatLaw.norm (fun i : Fin 3 => if i=2 then (1 : ℚ) else 0) 0).searchUpper
  0 ⟨0, by decide⟩ 3 0 = (2,3)
#guard ((RatLaw.norm (fun _ : Fin 2 => (0 : ℚ)) 1).select 3 ⟨0, by decide⟩).val = 1
#guard ((RatLaw.norm (fun i : Fin 2 => if i = 0 then (-1 : ℚ) else 2) 1).select 3 ⟨0, by decide⟩).val = 1

-- Adaptive continuation: selected branch determines the second block width.
def adaptive : BitProg Nat := .draw 1 fun u =>
  if u.val = 0 then .ret 7 else .draw 2 fun v => .ret (10+v.val)
#guard adaptive.run (fun _ => false) 0 = (7,1)
#guard adaptive.run (fun _ => true) 0 = (13,3)

def loopGraph : Digraph (Fin 1) (Fin 1) := ⟨fun _ => 0, fun _ => 0⟩
def pairGraph : Digraph (Fin 2) (Fin 2) := ⟨id, fun e => if e = 0 then 1 else 0⟩
#guard loopGraph.hasCycle (fun _ => true)
#guard !loopGraph.hasCycle (fun _ => false)
#guard pairGraph.hasCycle (fun _ => true)
#guard !pairGraph.hasCycle (fun e => decide (e = 0))
#guard pairGraph.reaches (fun _ => false) 0 0
#guard !pairGraph.reaches (fun _ => false) 0 1
#guard (pairGraph.reachCloseCount (fun _ => true) 2 {0}).2 = 2

-- A retained fair self-loop: one witness, nominal proposal probability one.
def soleWitness : (Finset.univ : Finset (Fin 1)) := ⟨0, by simp⟩
#guard loopGraph.rationalReject Finset.univ (fun _ => 1/2) (fun _ => 1/2)
  soleWitness (fun _ => true) 1 = 1/2
#guard loopGraph.rationalReject Finset.univ (fun _ => 1/2) (fun _ => 0)
  soleWitness (fun _ => true) 1 = 0
#guard loopGraph.rationalReject Finset.univ (fun _ => 1/2) (fun _ => 1/2)
  soleWitness (fun _ => false) 1 = 0

-- Complete rational Algorithm S runs on explicitly ordered arcs and bit tapes.
def oneArc : Digraph (Fin 2) (Fin 1) := ⟨fun _ => 0, fun _ => 1⟩
def oneArcRun (p : ℚ) (bits : Bool) :=
  ((oneArc.rationalAlgS (fun _ => p) (Equiv.refl _) (Equiv.refl _)
    [0] (fun e => e.val) 0 1 1).compile 4).run (fun _ => bits) 0
#guard (oneArcRun 1 false).1 = 1
#guard (oneArcRun 1 true).1 = 1
#guard (oneArcRun (1/2) false).1 = 1/2
#guard (oneArcRun (1/2) true).1 = 1/2
#guard (oneArcRun 0 false).1 = 0
#guard (oneArcRun 1 false).2 = 12
#guard (((oneArc.rationalAlgS (fun _ => 1/2) (Equiv.refl _) (Equiv.refl _)
  [0] (fun e => e.val) 0 0 0).compile 4).run (fun _ => false) 0) = (1,0)

-- Lower medians agree with the convention used in both amplification stages.
#guard rationalMedian ![3, 1, 4, 2] = 2
#guard rationalMedian ![3, 1, 2] = 2
#guard rationalMedian (fun i : Fin 0 => i.elim0) = 0

def loneOrder : Fin 1 ≃ (Finset.univ : Finset (Fin 1)) where
  toFun i := ⟨i, Finset.mem_univ i⟩
  invFun i := i.val
  left_inv _ := rfl
  right_inv i := by cases i; rfl

-- Exact zero exits before oracle construction, consuming no bits.
#guard (loopGraph.executableCount Finset.univ (Equiv.refl _) (Equiv.refl _)
  loneOrder (fun _ => 0) 64 10 10 10).run (fun _ => true) 5 = (0,5)

#guard (loopGraph.executableFPRAS Finset.univ (Equiv.refl _) (Equiv.refl _)
  loneOrder (fun _ => 0) 2 4).run (fun _ => true) 5 = (0,5)
