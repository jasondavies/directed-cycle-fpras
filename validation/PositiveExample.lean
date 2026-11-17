module

public meta import DirectedCycleFPRAS.CheckedSampler
public meta import DirectedCycleFPRAS.RationalAlgorithmS

meta section
open DirectedCycleFPRAS

private def oneArc : Digraph (Fin 2) (Fin 1) := ⟨fun _ => 0, fun _ => 1⟩
private def loopGraph : Digraph (Fin 1) (Fin 1) := ⟨fun _ => 0, fun _ => 0⟩
private def loneOrder : Fin 1 ≃ (Finset.univ : Finset (Fin 1)) where
  toFun i := ⟨i, Finset.mem_univ i⟩
  invFun i := i.val
  left_inv _ := rfl
  right_inv i := by cases i; rfl

/-- Positive execution examples. The quick suite runs `oracle`, using
Theorem 9's actual budget at accuracy 1/2 and failure 1/8.
`sample` and `count` use the full vertex-reduction production parameters;
these are benchmarks, not a promise of practical runtime. -/
public def main (args : List String) : IO Unit := do
  let mode := args.headD "oracle"
  let start ← IO.monoMsNow
  if mode == "oracle" then
    let M := 16*2^3*1*2^2
    let A := Digraph.algSChoices 2 1 M
    let b := Nat.clog 2 (max 1 (8*A))
    IO.println s!"Algorithm S: n=2 m=1 alpha=1/2 delta=1/8 M={M} b={b}"
    (← IO.getStdout).flush
    let result := ((oneArc.rationalAlgS (fun _ => 1/2) (Equiv.refl _) (Equiv.refl _)
      [0] (fun e => e.val) 0 1 M).compile b).run (fun _ => false) 0
    if result.1 != 1/2 then throw (IO.userError "unexpected reliability estimate")
    IO.println s!"estimate={result.1} bits={result.2}"
  else if mode == "sample" then
    IO.println s!"Sampler: n=m=k=1 d=2 M={Digraph.rationalVertexSamples 1 1}"
    (← IO.getStdout).flush
    let result := (loopGraph.checkedConditionalSampler Finset.univ (Equiv.refl _)
      (Equiv.refl _) loneOrder (fun _ => 1/2) 2).run (fun _ => true) 0
    match result.1 with
    | none => throw (IO.userError "positive cyclicity incorrectly reported undefined")
    | some configuration =>
      if !configuration 0 then throw (IO.userError "returned an acyclic configuration")
      IO.println s!"retained self-loop; bits={result.2}"
  else if mode == "count" then
    IO.println s!"Counter: n=m=k=1 r=2 d=2 M={Digraph.rationalVertexSamples 1 1}"
    (← IO.getStdout).flush
    let result := (loopGraph.executableFPRAS Finset.univ (Equiv.refl _)
      (Equiv.refl _) loneOrder (fun _ => 1/2) 2 2).run (fun _ => true) 0
    IO.println s!"estimate={result.1} bits={result.2}"
  else
    throw (IO.userError "usage: lean --run validation/PositiveExample.lean [oracle|sample|count]")
  let stop ← IO.monoMsNow
  IO.println s!"elapsed_ms={stop-start}"
