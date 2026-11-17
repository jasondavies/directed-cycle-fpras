module

public import DirectedCycleFPRAS.AlgorithmSInvariants

@[expose] public section
namespace DirectedCycleFPRAS
set_option linter.unusedSectionVars false
open Classical
noncomputable section
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

/-- Finish exploring the stack, without recording another target snapshot. -/
def sExplore (R : Finset V) (pre : E → Option Bool) :
    ℕ → Finset V → List (V × Bool) → Prog Empty (Finset V)
  | 0, D, _ => .ret D
  | _ + 1, D, [] => .ret D
  | f + 1, D, (z, flag) :: st =>
    (G.sScan p R pre z flag (arcOrder E) D st).bind fun r => sExplore R pre f r.1 r.2

/-- Finishing DFS also terminates within the discovered/stack potential. -/
theorem sExplore_fuel_add (R : Finset V) (pre : E → Option Bool)
    (f extra : ℕ) (D : Finset V) (st : List (V × Bool))
    (hf : Fintype.card V - D.card + st.length < f) :
    G.sExplore p R pre f D st = G.sExplore p R pre (f + extra) D st := by
  induction f generalizing D st with
  | zero => omega
  | succ f ih =>
    cases st with
    | nil => simp [Nat.succ_add, sExplore]
    | cons zf st =>
      obtain ⟨z, flag⟩ := zf
      simp only [Nat.succ_add, sExplore]
      apply (G.sScan_balance p R pre z flag (arcOrder E) D st).bind_congr (fun _ => trivial)
      intro r hr
      apply ih
      have hD := Finset.card_le_univ D
      have hD' := Finset.card_le_univ r.1
      simp only [List.length_cons] at hf
      omega

/-- A variant that records at the target pop, then finishes its exploration.
The recorded set and eligibility flag are frozen before the target is scanned. -/
def sDfsFullSnapshot (R : Finset V) (pre : E → Option Bool) (v : V) :
    ℕ → Finset V → List (V × Bool) → Prog Empty (Option (Finset V))
  | 0, _, _ => .ret none
  | _ + 1, _, [] => .ret none
  | f + 1, D, (z, flag) :: st =>
    if z = v then
      (G.sExplore p R pre (f + 1) D ((z, flag) :: st)).bind fun _ =>
        .ret (if flag then some D else none)
    else (G.sScan p R pre z flag (arcOrder E) D st).bind fun r =>
      sDfsFullSnapshot R pre v f r.1 r.2

/-- Early stopping preserves the complete law of the recorded snapshot;
all random choices after recording are integrated out exactly. -/
theorem sDfs_earlyStop (R : Finset V) (pre : E → Option Bool) (v : V)
    (fuel : ℕ) (D : Finset V) (st : List (V × Bool)) (f : Option (Finset V) → ℝ) :
    (G.sDfs (Q := Empty) p R pre v fuel D st).exp noOracle f =
      (G.sDfsFullSnapshot p R pre v fuel D st).exp noOracle f := by
  induction fuel generalizing D st with
  | zero => rfl
  | succ fuel ih =>
    cases st with
    | nil => rfl
    | cons zf st =>
      obtain ⟨z, flag⟩ := zf
      simp only [sDfs, sDfsFullSnapshot]
      by_cases hz : z = v
      · simp only [hz, ite_true, Prog.exp_bind, Prog.exp]
        exact (Prog.exp_const noOracle _ _).symm
      · simp only [hz, ite_false, Prog.exp_bind]
        exact congrArg ((G.sScan p R pre z flag (arcOrder E) D st).exp noOracle)
          (funext fun r => ih r.1 r.2)

end Digraph
end
end DirectedCycleFPRAS
