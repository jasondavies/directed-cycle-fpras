module

public import DirectedCycleFPRAS.ProgramComposition

@[expose] public section

namespace DirectedCycleFPRAS
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
open scoped BigOperators Nat
open Classical
noncomputable section

/-- A uniform bound over all possible numbers of positive edges of a query. -/
def oracleBitBudget (n m : ℕ) (α : ℝ) : ℕ :=
  ∑ j ∈ Finset.range (m + 1),
    algSBits n j (algSSamples n j α) * Digraph.algSChoices n j (algSSamples n j α)

/-- A common answer height over all residual queries; the extra one covers zero budgets. -/
def oracleHeight (n m H : ℕ) (α : ℝ) : ℕ :=
  1 + ∑ j ∈ Finset.range (m + 1),
    max 1 (Digraph.sizeBase n j (algSSamples n j α) (H ^ j) ^ n)

namespace Digraph
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E)

/-- The concrete fair-bit program answering one residual query. -/
def algSQuery (α : ℝ) (x : Query V E) : Prog Empty ℝ :=
  ((G.positivePart x.1).algS (fun e => x.1 e) x.2.1 x.2.2
    (algSSamples (Fintype.card V) (Fintype.card {e : E // 0 < x.1 e}) α)).discretise
      (algSBits (Fintype.card V) (Fintype.card {e : E // 0 < x.1 e})
        (algSSamples (Fintype.card V) (Fintype.card {e : E // 0 < x.1 e}) α))

theorem algSQuery_bitCost (α : ℝ) (x : Query V E) :
    Prog.BitCost (fun _ : Empty => 0) (G.algSQuery α x)
      (oracleBitBudget (Fintype.card V) (Fintype.card E) α) := by
  have h := (Prog.discretise_bitBound
    (algSBits (Fintype.card V) (Fintype.card {e : E // 0 < x.1 e})
      (algSSamples (Fintype.card V) (Fintype.card {e : E // 0 < x.1 e}) α))
    ((G.positivePart x.1).algS_choiceBound (Q := Empty) (fun e => x.1 e) x.2.1 x.2.2
      (algSSamples (Fintype.card V) (Fintype.card {e : E // 0 < x.1 e}) α))).fairBitCost
  apply h.mono
  unfold oracleBitBudget
  exact Finset.single_le_sum
    (f := fun j => algSBits (Fintype.card V) j (algSSamples (Fintype.card V) j α) *
      algSChoices (Fintype.card V) j (algSSamples (Fintype.card V) j α))
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (Fintype.card_subtype_le (fun e : E => 0 < x.1 e))))

/-- Size invariant for every branch, including probability-zero branches and M=0. -/
theorem algS_sat_total (q : E → ℝ) (s t : V) (M : ℕ) (a b : E → ℕ)
    (hb : ∀ e, 0 < b e) (ha : ∀ e, a e ≤ b e)
    (hq : ∀ e, q e = (a e : ℝ) / (b e : ℝ)) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (Height (max 1 (sizeBase (Fintype.card V) (Fintype.card E) M (∏ e, b e) ^ Fintype.card V)))
      (G.algS (Q := Empty) q s t M) := by
  by_cases hM : 0 < M
  · exact (G.algS_sat q a b hb ha hq s t hM).imp fun _ h => h.mono (le_max_right _ _)
  · have : M = 0 := by omega
    subst M
    exact (G.algS_zero_sat q s t).imp fun _ h => h.mono (le_max_left _ _)

/-- Pinning input probabilities to zero or one preserves a bounded denominator representation. -/
theorem derived_fractions {p q : E → ℝ} (a b : E → ℕ) {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ e, 0 < b e) (ha : ∀ e, a e ≤ b e) (hbH : ∀ e, b e ≤ H)
    (hp : ∀ e, p e = (a e : ℝ) / (b e : ℝ)) (hd : Derived p q) :
    ∃ a' b' : E → ℕ, (∀ e, 0 < b' e) ∧ (∀ e, a' e ≤ b' e) ∧
      (∀ e, b' e ≤ H) ∧ (∀ e, q e = (a' e : ℝ) / (b' e : ℝ)) := by
  have hex : ∀ e, ∃ c d : ℕ, 0 < d ∧ c ≤ d ∧ d ≤ H ∧ q e = (c : ℝ) / d := by
    intro e
    rcases hd e with h | h | h
    · exact ⟨a e, b e, hb e, ha e, hbH e, h.trans (hp e)⟩
    · exact ⟨0, 1, by omega, by omega, hH, by simpa using h⟩
    · exact ⟨1, 1, by omega, by omega, hH, by simpa using h⟩
  choose a' b' hd0 had hdH heq using hex
  exact ⟨a', b', hd0, had, hdH, heq⟩

theorem algSQuery_height {p : E → ℝ} (α : ℝ) (a b : E → ℕ) {H : ℕ}
    (hH : 1 ≤ H) (hb : ∀ e, 0 < b e) (ha : ∀ e, a e ≤ b e)
    (hbH : ∀ e, b e ≤ H) (hp : ∀ e, p e = (a e : ℝ) / (b e : ℝ))
    (x : Query V E) (hd : Derived p x.1) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (Height (oracleHeight (Fintype.card V) (Fintype.card E) H α)) (G.algSQuery α x) := by
  obtain ⟨a', b', hb', ha', hbH', hx⟩ := derived_fractions a b hH hb ha hbH hp hd
  have hs := ((G.positivePart x.1).algS_sat_total (fun e => x.1 e) x.2.1 x.2.2
    (algSSamples (Fintype.card V) (Fintype.card {e : E // 0 < x.1 e}) α)
    (fun e => a' e) (fun e => b' e) (fun e => hb' e) (fun e => ha' e)
    (fun e => hx e)).discretise
      (algSBits (Fintype.card V) (Fintype.card {e : E // 0 < x.1 e})
        (algSSamples (Fintype.card V) (Fintype.card {e : E // 0 < x.1 e}) α))
  apply hs.imp
  intro z hz
  apply hz.mono
  have hprod : (∏ e : {e : E // 0 < x.1 e}, b' e) ≤
      H ^ Fintype.card {e : E // 0 < x.1 e} := by
    calc _ ≤ ∏ _e : {e : E // 0 < x.1 e}, H := Finset.prod_le_prod fun e _ => hbH' e
         _ = _ := by simp
  have hbase := Nat.mul_le_mul_left
    ((Fintype.card V * Fintype.card {e : E // 0 < x.1 e} + 1) *
      algSSamples (Fintype.card V) (Fintype.card {e : E // 0 < x.1 e}) α) hprod
  have hpow := Nat.pow_le_pow_left hbase (Fintype.card V)
  have hmax := max_le_max_left 1 hpow
  have hsum := Finset.single_le_sum
    (f := fun j => max 1 (sizeBase (Fintype.card V) j
      (algSSamples (Fintype.card V) j α) (H ^ j) ^ Fintype.card V))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Fintype.card_subtype_le (fun e : E => 0 < x.1 e))))
  unfold oracleHeight
  have hmax' : max 1 (sizeBase (Fintype.card V) (Fintype.card {e : E // 0 < x.1 e})
      (algSSamples (Fintype.card V) (Fintype.card {e : E // 0 < x.1 e}) α)
      (∏ e : {e : E // 0 < x.1 e}, b' e) ^ Fintype.card V) ≤
      max 1 (sizeBase (Fintype.card V) (Fintype.card {e : E // 0 < x.1 e})
      (algSSamples (Fintype.card V) (Fintype.card {e : E // 0 < x.1 e}) α)
      (H ^ Fintype.card {e : E // 0 < x.1 e}) ^ Fintype.card V) := by
    simpa only [sizeBase, Nat.mul_assoc] using hmax
  exact hmax'.trans (hsum.trans (Nat.le_add_left _ _))

/-- The full cycle algorithm with both amplification stages and all queries expanded. -/
def concreteCycle (p : E → ℝ) (α : ℝ) (bits samples inner outer : ℕ) : Prog Empty ℝ :=
  ((G.cycleAlgorithm p bits samples).medianOf outer).inline
    (fun x => (G.algSQuery α x).medianOf inner)

theorem concreteCycle_law (p : E → ℝ) (α : ℝ) (bits samples inner outer : ℕ) (f : ℝ → ℝ) :
    (G.concreteCycle p α bits samples inner outer).exp noOracle f =
      ((G.cycleAlgorithm p bits samples).medianOf outer).exp
        ((G.oracleOfEstimator (algSEstimator α)).amplify inner) f :=
  Prog.exp_inline_amplify (G.algSQuery α) inner _ f

theorem concreteCycle_bitCost (p : E → ℝ) (α : ℝ) (bits samples inner outer : ℕ) :
    Prog.BitCost (fun _ : Empty => 0) (G.concreteCycle p α bits samples inner outer)
      (bits * (outer * (samples * (Fintype.card E + 1))) +
        (outer * (Fintype.card E + samples * (2 * Fintype.card E))) *
          (inner * oracleBitBudget (Fintype.card V) (Fintype.card E) α)) := by
  have hb := (G.cycleAlgorithm_bitBound p bits samples).medianOf outer
  have hq := Prog.medianOf_queryBound (G.cycleAlgorithm_queryBound p bits samples) outer
  exact (hb.bitCost hq).inline _ fun x => (G.algSQuery_bitCost α x).medianOf inner

theorem concreteCycle_height {p : E → ℝ} (α : ℝ) (bits samples inner outer : ℕ)
    (hsamples : 0 < samples) (a b : E → ℕ) {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ e, 0 < b e) (ha : ∀ e, a e ≤ b e) (hbH : ∀ e, b e ≤ H)
    (hp : ∀ e, p e = (a e : ℝ) / (b e : ℝ)) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (Height ((2 * (H * oracleHeight (Fintype.card V) (Fintype.card E) H α)) ^
        Fintype.card E * (samples * (Fintype.card E)!)))
      (G.concreteCycle p α bits samples inner outer) := by
  have hHo : 1 ≤ oracleHeight (Fintype.card V) (Fintype.card E) H α := by
    unfold oracleHeight; omega
  have hpH : ∀ e, Height H (p e) := fun e =>
    ⟨(a e : ℤ), b e, hb e, by simpa using hp e, by simpa using (ha e).trans (hbH e), hbH e⟩
  have hout : 1 ≤ (2 * (H * oracleHeight (Fintype.card V) (Fintype.card E) H α)) ^
      Fintype.card E * (samples * (Fintype.card E)!) := by
    exact Nat.mul_pos (Nat.pow_pos (by positivity)) (Nat.mul_pos hsamples (Nat.factorial_pos _))
  exact ((G.cycleAlgorithm_sat p hH hHo hpH bits hsamples).medianOf
    (height_zero hout) outer).inline _ fun x hx =>
      (G.algSQuery_height α a b hH hb ha hbH hp x hx.1).medianOf (height_zero hHo) inner

/-- A zero-sample run has output zero even on failed-oracle histories. -/
theorem cycleAlgorithm_zero_sat (p : E → ℝ) (bits : ℕ) :
    Prog.Sat (fun _ => True) (fun _ => True) (Height 1) (G.cycleAlgorithm p bits 0) := by
  unfold cycleAlgorithm
  split_ifs
  · refine (Prog.Sat.trivial _).bind fun w _ => ?_
    simp only [Prog.replicate, Prog.bind]
    refine .work _ _ (.ret _ ?_)
    simpa [Law.sampleAverage] using height_zero (H := 1) (by omega)
  · exact .ret _ (height_zero (by omega))

/-- Final answer size on every branch, without a nonzero sample-budget assumption. -/
theorem concreteCycle_height_total {p : E → ℝ} (α : ℝ) (bits samples inner outer : ℕ)
    (a b : E → ℕ) {H : ℕ} (hH : 1 ≤ H) (hb : ∀ e, 0 < b e)
    (ha : ∀ e, a e ≤ b e) (hbH : ∀ e, b e ≤ H)
    (hp : ∀ e, p e = (a e : ℝ) / (b e : ℝ)) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (Height (max 1 ((2 * (H * oracleHeight (Fintype.card V) (Fintype.card E) H α)) ^
        Fintype.card E * (samples * (Fintype.card E)!))))
      (G.concreteCycle p α bits samples inner outer) := by
  by_cases hs : 0 < samples
  · exact (G.concreteCycle_height α bits samples inner outer hs a b hH hb ha hbH hp).imp
      fun _ h => h.mono (le_max_right _ _)
  · have : samples = 0 := by omega
    subst samples
    have hz := ((G.cycleAlgorithm_zero_sat p bits).medianOf (height_zero (by omega)) outer).inline
      (fun x => (G.algSQuery α x).medianOf inner) (fun _ _ => Prog.Sat.trivial _)
    exact hz.imp fun _ h => h.mono (le_max_left _ _)

/-- The expanded fair-bit program has the accuracy of the abstract-oracle theorem. -/
theorem concreteCycle_correct (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hS : ∀ α : ℝ, 0 < α → α < 1 → AlgSAccurate α) :
    (G.concreteCycle p (ε / (128 * Fintype.card E * (Fintype.card E + 1)))
      (bitBudget (Fintype.card E) ε) (reductionBudget (Fintype.card E) ε)
      (amplifyRounds (Fintype.card E + reductionBudget (Fintype.card E) ε * (2 * Fintype.card E)))
      (confidenceRuns δ)).exp noOracle
      (fun z => if ε * G.cycleMass (edgeLaw p hp0 hp1).toMass <
        |z - G.cycleMass (edgeLaw p hp0 hp1).toMass| then 1 else 0) ≤ δ := by
  rw [concreteCycle_law]
  exact G.cycle_fpras_of_algS p hp0 hp1 hε hε1 hδ hS
/-- The final parameterized program, with no abstract oracle remaining. -/
def cycleFPRAS (p : E → ℝ) (ε δ : ℝ) : Prog Empty ℝ :=
  G.concreteCycle p (ε / (128 * Fintype.card E * (Fintype.card E + 1)))
    (bitBudget (Fintype.card E) ε) (reductionBudget (Fintype.card E) ε)
    (amplifyRounds (Fintype.card E + reductionBudget (Fintype.card E) ε * (2 * Fintype.card E)))
    (confidenceRuns δ)

/-- Accuracy, all fair bits (including amplified queries), and rational output
size hold for the same expanded program. The only accuracy hypothesis is hS. -/
theorem cycleFPRAS_spec (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hS : ∀ α : ℝ, 0 < α → α < 1 → AlgSAccurate α)
    (a b : E → ℕ) {H : ℕ} (hH : 1 ≤ H) (hb : ∀ e, 0 < b e)
    (ha : ∀ e, a e ≤ b e) (hbH : ∀ e, b e ≤ H)
    (hp : ∀ e, p e = (a e : ℝ) / (b e : ℝ)) :
    let m := Fintype.card E
    let α := ε / (128 * m * (m + 1))
    let N := reductionBudget m ε
    let T := m + N * (2 * m)
    let k := amplifyRounds T
    let r := confidenceRuns δ
    (G.cycleFPRAS p ε δ).exp noOracle
      (fun z => if ε * G.cycleMass (edgeLaw p hp0 hp1).toMass <
        |z - G.cycleMass (edgeLaw p hp0 hp1).toMass| then 1 else 0) ≤ δ ∧
    Prog.BitCost (fun _ : Empty => 0) (G.cycleFPRAS p ε δ)
      (bitBudget m ε * (r * (N * (m + 1))) +
        (r * T) * (k * oracleBitBudget (Fintype.card V) m α)) ∧
    Prog.Sat (fun _ => True) (fun _ => True)
      (Height (max 1 ((2 * (H * oracleHeight (Fintype.card V) m H α)) ^ m * (N * Nat.factorial m))))
      (G.cycleFPRAS p ε δ) := by
  exact ⟨G.concreteCycle_correct p hp0 hp1 hε hε1 hδ hS,
    G.concreteCycle_bitCost p _ _ _ _ _,
    G.concreteCycle_height_total _ _ _ _ _ a b hH hb ha hbH hp⟩


end Digraph
end
end DirectedCycleFPRAS
