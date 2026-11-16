module

public import DirectedCycleFPRAS.ProgramComposition

@[expose] public section

namespace DirectedCycleFPRAS
set_option linter.unusedSectionVars false
open scoped BigOperators
open Classical
noncomputable section
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

/-- Scanning preserves discovered-cardinality minus stack length. This bounds
DFS even on probability-zero branches, independently of edge probabilities. -/
theorem sScan_balance (R : Finset V) (pre : E → Option Bool) (z : V) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool)) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (fun r : Finset V × List (V × Bool) => r.1.card + st.length = D.card + r.2.length)
      (G.sScan (Q := Empty) p R pre z flag l D st) := by
  induction l generalizing D st with
  | nil => exact .ret _ rfl
  | cons e l ih =>
    unfold sScan
    split_ifs with he
    · refine (Prog.Sat.trivial _).bind fun o _ => ?_
      cases o with
      | false => exact ih D st
      | true =>
        apply (ih (insert (G.target e) D) ((G.target e, flag && decide (G.target e ∉ R)) :: st)).imp
        intro r hr
        simp only [List.length_cons, Finset.card_insert_of_notMem he.2] at hr
        omega
    · exact ih D st

/-- Extra DFS fuel does not change the program once the unseen-vertex/stack
potential is below the available fuel. -/
theorem sDfs_fuel_add (R : Finset V) (pre : E → Option Bool) (v : V)
    (f extra : ℕ) (D : Finset V) (st : List (V × Bool))
    (hf : Fintype.card V - D.card + st.length < f) :
    G.sDfs (Q := Empty) p R pre v f D st = G.sDfs p R pre v (f + extra) D st := by
  induction f generalizing D st with
  | zero => omega
  | succ f ih =>
    cases st with
    | nil => simp [Nat.succ_add, sDfs]
    | cons zf st =>
      obtain ⟨z, flag⟩ := zf
      simp only [Nat.succ_add, sDfs]
      by_cases hz : z = v
      · simp only [hz, ite_true]
      · simp only [hz, ite_false]
        apply (G.sScan_balance p R pre z flag (arcOrder E) D st).bind_congr (fun _ => trivial)
        intro r hr
        apply ih
        have hD := Finset.card_le_univ D
        have hD' := Finset.card_le_univ r.1
        simp only [List.length_cons] at hf
        omega

/-- The transcription's n+1 DFS fuel is sufficient for any nonempty snapshot. -/
theorem sDfs_initial_fuel (R : Finset V) (pre : E → Option Bool) (v u : V)
    (D : Finset V) (hu : u ∈ D) (extra : ℕ) :
    G.sDfs (Q := Empty) p R pre v (Fintype.card V + 1) D [(u, true)] =
      G.sDfs p R pre v (Fintype.card V + 1 + extra) D [(u, true)] := by
  apply G.sDfs_fuel_add
  have hD : 0 < D.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hcard := Finset.card_le_univ D
  simp only [List.length_cons, List.length_nil]
  omega

/-- A vertex set closed under graph edges cannot be left by a scan. The
stack invariant also records that every pending vertex is already discovered. -/
theorem sScan_closed (U R : Finset V) (hU : ∀ e, G.source e ∈ U → G.target e ∈ U)
    (pre : E → Option Bool) (z : V) (hz : z ∈ U) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool)) (hD : D ⊆ U)
    (hst : ∀ x ∈ st, x.1 ∈ D) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (fun r : Finset V × List (V × Bool) => r.1 ⊆ U ∧ ∀ x ∈ r.2, x.1 ∈ r.1)
      (G.sScan (Q := Empty) p R pre z flag l D st) := by
  induction l generalizing D st with
  | nil => exact .ret _ ⟨hD, hst⟩
  | cons e l ih =>
    unfold sScan
    split_ifs with he
    · refine (Prog.Sat.trivial _).bind fun o _ => ?_
      cases o with
      | false => exact ih D st hD hst
      | true =>
        apply ih
        · exact Finset.insert_subset (hU e (he.1 ▸ hz)) hD
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hst x hx)
    · exact ih D st hD hst

/-- Every recorded snapshot remains in a closed vertex set and contains its target. -/
theorem sDfs_closed (U R : Finset V) (hU : ∀ e, G.source e ∈ U → G.target e ∈ U)
    (pre : E → Option Bool) (v : V) (f : ℕ) (D : Finset V)
    (st : List (V × Bool)) (hD : D ⊆ U) (hst : ∀ x ∈ st, x.1 ∈ D) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (fun o : Option (Finset V) => ∀ A ∈ o, A ⊆ U ∧ v ∈ A)
      (G.sDfs (Q := Empty) p R pre v f D st) := by
  induction f generalizing D st with
  | zero => exact .ret _ (by simp)
  | succ f ih =>
    cases st with
    | nil => exact .ret _ (by simp)
    | cons zf st =>
      obtain ⟨z, flag⟩ := zf
      unfold sDfs
      by_cases hz : z = v
      · subst z
        simp only [ite_true]
        cases flag <;> refine .ret _ ?_ <;> simp_all
      · simp only [hz, ite_false]
        apply (G.sScan_closed p U R hU pre z (hD (hst (z, flag) (by simp))) flag
          (arcOrder E) D st hD (fun x hx => hst x (by simp [hx]))).bind
        intro r hr
        exact ih r.1 r.2 hr.1 hr.2

/-- Once the unresolved-vertex count is below the fuel, extra rounds cannot
change Algorithm S, regardless of the estimates or generated snapshots. -/
theorem sRounds_fuel_add (t : V) (M f extra : ℕ) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) (hf : Fintype.card V - R.card < f) :
    G.sRounds (Q := Empty) p t M f R qh pools =
      G.sRounds p t M (f + extra) R qh pools := by
  induction f generalizing R qh pools with
  | zero => omega
  | succ f ih =>
    simp only [Nat.succ_add, sRounds]
    by_cases ht : t ∈ R
    · simp only [ht, ite_true]
    · simp only [ht, ite_false]
      generalize he : (((arcOrder E).filter fun e => G.source e ∈ R ∧ G.target e ∉ R).argmax
        fun e => qh (G.source e) * p e) = o
      cases o with
      | none => rfl
      | some e =>
        have hmem := List.argmax_mem (show e ∈ (((arcOrder E).filter
          fun e => G.source e ∈ R ∧ G.target e ∉ R).argmax
          fun e => qh (G.source e) * p e) by rw [he]; simp)
        have hcut : G.source e ∈ R ∧ G.target e ∉ R := by
          simpa using (List.mem_filter.mp hmem).2
        have htarget := hcut.2
        simp only [Option.elim_some]
        split_ifs
        · rfl
        · apply (Prog.Sat.trivial _).bind_congr (fun _ => trivial)
          intro res _
          apply ih
          rw [Finset.card_insert_of_notMem htarget]
          have hcard := Finset.card_le_univ (insert (G.target e) R)
          rw [Finset.card_insert_of_notMem htarget] at hcard
          omega

theorem algS_round_fuel (s t : V) (M extra : ℕ) :
    G.algS (Q := Empty) p s t M =
      G.sRounds p t M (Fintype.card V + extra) {s} (fun u => if u = s then 1 else 0)
        (fun u => if u = s then [{s}] else []) := by
  apply G.sRounds_fuel_add
  have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  simp
  omega

/-- Changing probabilities or preassigned states on edges whose sources lie
outside U leaves every scan starting in U exactly unchanged. -/
theorem sScan_restrict (q : E → ℝ) (U R : Finset V)
    (pre pre' : E → Option Bool) (hpq : ∀ e, G.source e ∈ U → p e = q e)
    (hpre : ∀ e, G.source e ∈ U → pre e = pre' e) (z : V) (hz : z ∈ U)
    (flag : Bool) (l : List E) (D : Finset V) (st : List (V × Bool)) :
    G.sScan (Q := Empty) p R pre z flag l D st = G.sScan q R pre' z flag l D st := by
  induction l generalizing D st with
  | nil => rfl
  | cons e l ih =>
    simp only [sScan]
    by_cases he : G.source e = z ∧ G.target e ∉ D
    · simp only [he, hpq e (he.1 ▸ hz), hpre e (he.1 ▸ hz)]
      apply (Prog.Sat.trivial _).bind_congr (fun _ => trivial)
      intro o _
      cases o <;> exact ih _ _
    · simp only [he, ite_false]
      exact ih _ _

/-- Exact program equality for exploration after arbitrary changes outside a
closed vertex set, the exploration component of reachable-vertex restriction. -/
theorem sDfs_restrict (q : E → ℝ) (U R : Finset V)
    (hU : ∀ e, G.source e ∈ U → G.target e ∈ U)
    (pre pre' : E → Option Bool) (hpq : ∀ e, G.source e ∈ U → p e = q e)
    (hpre : ∀ e, G.source e ∈ U → pre e = pre' e)
    (v : V) (f : ℕ) (D : Finset V) (st : List (V × Bool))
    (hD : D ⊆ U) (hst : ∀ x ∈ st, x.1 ∈ D) :
    G.sDfs (Q := Empty) p R pre v f D st = G.sDfs q R pre' v f D st := by
  induction f generalizing D st with
  | zero => rfl
  | succ f ih =>
    cases st with
    | nil => rfl
    | cons zf st =>
      obtain ⟨z, flag⟩ := zf
      have hz := hD (hst (z, flag) (by simp))
      simp only [sDfs]
      by_cases hzt : z = v
      · simp only [hzt, ite_true]
      · simp only [hzt, ite_false]
        rw [← G.sScan_restrict p q U R pre pre' hpq hpre z hz flag]
        apply (G.sScan_closed p U R hU pre z hz flag (arcOrder E) D st hD
          (fun x hx => hst x (by simp [hx]))).bind_congr (fun _ => trivial)
        intro r hr
        exact ih r.1 r.2 hr.1 hr.2

/-- The path flag is exactly the absence of resolved vertices on the discovered
path after its root. This is independent of the concrete parent-pointer representation. -/
theorem path_flag (R : Finset V) (path : List V) :
    path.foldl (fun flag v => flag && decide (v ∉ R)) true = true ↔
      ∀ v ∈ path, v ∉ R := by
  have aux : ∀ (l : List V) (flag : Bool),
      l.foldl (fun flag v => flag && decide (v ∉ R)) flag = true ↔
        flag = true ∧ ∀ v ∈ l, v ∉ R := by
    intro l
    induction l with
    | nil => intro flag; simp
    | cons v l ih =>
      intro flag
      rw [List.foldl_cons, ih]
      simp [and_assoc]
  simpa using aux path true

/-- The number of generated records equals the pool length and is bounded by the iterations. -/
theorem sGenerate_pool (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V))
    (M : ℕ) (v : V) (i : ℕ) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (fun r : ℕ × List (Finset V) => r.1 = r.2.length ∧ r.1 ≤ i)
      (G.sGenerate (Q := Empty) p R qh pools M v i) := by
  induction i with
  | zero => exact .ret _ ⟨rfl, le_refl _⟩
  | succ i ih =>
    apply ih.bind
    intro acc hacc
    refine (Prog.Sat.trivial _).bind fun o _ => .ret _ ?_
    cases o <;> simp_all <;> omega

/-- In a continuing round the new estimate is positive exactly when its pool is nonempty. -/
theorem generated_positive_iff (Φ : ℝ) (hΦ : 0 < Φ) {M count : ℕ} (hM : 0 < M)
    (pool : List (Finset V)) (hc : count = pool.length) :
    0 < Φ * count / M ↔ pool ≠ [] := by
  rw [div_pos_iff_of_pos_right (by exact_mod_cast hM), mul_pos_iff_of_pos_left hΦ]
  simp [hc, List.length_pos_iff_ne_nil]

end Digraph
end
end DirectedCycleFPRAS
