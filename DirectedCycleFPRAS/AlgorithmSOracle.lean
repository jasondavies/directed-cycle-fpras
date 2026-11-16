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


end Digraph
end
end DirectedCycleFPRAS
