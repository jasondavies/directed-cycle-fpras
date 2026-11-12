module

public import DirectedCycleFPRAS.Confidence

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# Reduction to an estimator for positive edge probabilities

The algorithm's queries delete an edge by giving it probability zero. The
reliability FPRAS of Feng, Fu and Guo is stated for directed multigraphs
(parallel arcs and self-loops allowed) whose edge probabilities lie in `(0,1]`,
so zero is outside its input class. This file removes that mismatch:

* `eventMass_restrict`: coordinates of a product law that are deterministic
  can be removed.
* `Digraph.reliability_positivePart`: deleting the zero-probability edges
  preserves two-terminal reliability.
* `Digraph.cycle_fpras_of_estimator`: the reduction theorem with, as its only
  oracle hypothesis, a reliability estimator that is accurate with probability
  3/4 on finite directed multigraphs with probabilities in `(0,1]`.
-/

namespace DirectedCycleFPRAS

open scoped BigOperators
open Classical

noncomputable section

section Restrict

variable {S E : Type} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]

/-- Extend an assignment along `j`, using the forced bit elsewhere. -/
def extend (j : S → E) (q : E → ℝ) (a : S → Bool) (x : E) : Bool :=
  if h : ∃ s, j s = x then a (Classical.choose h) else decide (q x = 1)

theorem extend_apply {j : S → E} (hj : Function.Injective j) (q : E → ℝ) (a : S → Bool)
    (s : S) : extend j q a (j s) = a s := by
  have h : ∃ s', j s' = j s := ⟨s, rfl⟩
  rw [extend, dite_eq_left h]
  exact congrArg a (hj (Classical.choose_spec h))

theorem extend_of_not {j : S → E} (q : E → ℝ) (a : S → Bool) {x : E}
    (hx : ¬ ∃ s, j s = x) : extend j q a x = decide (q x = 1) := by
  rw [extend, dite_eq_right hx]

theorem edgeWeight_extend {j : S → E} (hj : Function.Injective j) {q : E → ℝ}
    (hq : ∀ x, (¬ ∃ s, j s = x) → q x = 0 ∨ q x = 1) (a : S → Bool) :
    edgeWeight q (extend j q a) = edgeWeight (q ∘ j) a := by
  unfold edgeWeight
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image j)),
    Finset.prod_image fun s _ s' _ h => hj h]
  · apply Finset.prod_congr rfl
    intro s _
    rw [extend_apply hj, Function.comp_apply]
  · intro x _ hx
    have hx' : ¬ ∃ s, j s = x := by
      rintro ⟨s, rfl⟩
      exact hx (Finset.mem_image_of_mem j (Finset.mem_univ s))
    rw [extend_of_not q a hx']
    rcases hq x hx' with h | h <;> simp [h]

theorem edgeWeight_eq_zero_of_ne_extend {j : S → E} (hj : Function.Injective j) {q : E → ℝ}
    (hq : ∀ x, (¬ ∃ s, j s = x) → q x = 0 ∨ q x = 1) (ω : E → Bool)
    (h : ω ≠ extend j q (ω ∘ j)) : edgeWeight q ω = 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp h
  have hx' : ¬ ∃ s, j s = x := by
    rintro ⟨s, rfl⟩
    exact hx (by rw [extend_apply hj]; rfl)
  rw [extend_of_not q _ hx'] at hx
  apply Finset.prod_eq_zero (Finset.mem_univ x)
  rcases hq x hx' with h0 | h1
  · have hω : ω x = true := by simpa [h0] using hx
    simp [hω, h0]
  · have hω : ω x = false := by simpa [h1] using hx
    simp [hω, h1]

/-- Deterministic coordinates of a product law can be removed: if every
coordinate outside the range of `j` has probability 0 or 1, an event has the
same mass under the product law on the remaining coordinates. -/
theorem eventMass_restrict {j : S → E} (hj : Function.Injective j) {q : E → ℝ}
    (hq : ∀ x, (¬ ∃ s, j s = x) → q x = 0 ∨ q x = 1) (B : (E → Bool) → Prop) :
    eventMass q B = eventMass (q ∘ j) (fun a => B (extend j q a)) := by
  have hinj : Function.Injective (extend j q) := by
    intro a a' h
    funext s
    have := congrFun h (j s)
    rwa [extend_apply hj, extend_apply hj] at this
  unfold eventMass
  have hR : (∑ a : S → Bool, if B (extend j q a) then edgeWeight (q ∘ j) a else 0) =
      ∑ ω ∈ Finset.univ.image (extend j q), if B ω then edgeWeight q ω else 0 := by
    rw [Finset.sum_image fun a _ a' _ h => hinj h]
    apply Finset.sum_congr rfl
    intro a _
    rw [edgeWeight_extend hj hq]
  rw [hR]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro ω _ hω
  have hne : ω ≠ extend j q (ω ∘ j) := by
    intro h
    exact hω (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _))
  split_ifs
  · exact edgeWeight_eq_zero_of_ne_extend hj hq ω hne
  · rfl

end Restrict

/-- A randomized real number: a finite seed space, its law, and a value. -/
structure RandReal where
  Seed : Type
  [fintype : Fintype Seed]
  law : Law Seed
  value : Seed → ℝ

attribute [instance] RandReal.fintype

/-- A randomized reliability estimator for arbitrary finite directed
multigraphs: graph, edge probabilities and two terminals in, a randomized
real out. -/
abbrev ReliabilityEstimator : Type 1 :=
  (V E : Type) → [Fintype V] → [Fintype E] → [DecidableEq E] →
    Digraph V E → (E → ℝ) → V → V → RandReal

/-- The estimator has relative error at most `α` with probability at least
3/4 on every instance with all probabilities in `(0,1]` and positive
reliability. Loops and parallel edges are allowed. This is the constant
confidence guarantee of an FPRAS at accuracy `α`. -/
def ReliabilityEstimator.Correct (R : ReliabilityEstimator) (α : ℝ) : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq E] (G : Digraph V E) (q : E → ℝ)
    (s t : V), (∀ e, 0 < q e ∧ q e ≤ 1) → 0 < G.reliability q s t →
    (∑ z, if |(R V E G q s t).value z - G.reliability q s t| ≤ α * G.reliability q s t
      then 0 else (R V E G q s t).law.value z) ≤ 1 / 4

namespace Digraph

variable {V E : Type} [Fintype E] [DecidableEq E] (G : Digraph V E)

/-- The graph with only the positive-probability edges. -/
def positivePart (q : E → ℝ) : Digraph V {e : E // 0 < q e} where
  source e := G.source e
  target e := G.target e

/-- Deleting zero-probability edges preserves two-terminal reliability. -/
theorem reliability_positivePart {q : E → ℝ} (hq : Prob01 q) (s t : V) :
    (G.positivePart q).reliability (fun e => q e) s t = G.reliability q s t := by
  have hj : Function.Injective (Subtype.val : {e : E // 0 < q e} → E) := Subtype.val_injective
  have hq0 : ∀ x, (¬ ∃ e : {e : E // 0 < q e}, e.1 = x) → q x = 0 ∨ q x = 1 := by
    intro x hx
    left
    refine le_antisymm (not_lt.mp fun h => hx ⟨⟨x, h⟩, rfl⟩) (hq x).1
  have hadj : ∀ a : {e : E // 0 < q e} → Bool,
      G.Adj (retained (extend Subtype.val q a)) = (G.positivePart q).Adj (retained a) := by
    intro a
    funext u v
    apply propext
    constructor
    · rintro ⟨e, he, hs, ht⟩
      have he' : extend (Subtype.val : {e : E // 0 < q e} → E) q a e = true := he
      by_cases hpos : 0 < q e
      · have hval := extend_apply hj q a ⟨e, hpos⟩
        exact ⟨⟨e, hpos⟩, hval.symm.trans he', hs, ht⟩
      · have hx : ¬ ∃ e' : {e : E // 0 < q e}, e'.1 = e := by
          rintro ⟨e', rfl⟩
          exact hpos e'.2
        have hz : q e = 0 := le_antisymm (not_lt.mp hpos) (hq e).1
        rw [extend_of_not q a hx] at he'
        simp [hz] at he'
    · rintro ⟨e, he, hs, ht⟩
      exact ⟨e.1, (extend_apply hj q a e).trans he, hs, ht⟩
  unfold reliability
  rw [eventMass_restrict hj hq0]
  simp only [hadj]
  rfl

/-- Answer every reliability query on the fixed graph by deleting its
zero-probability edges and calling the estimator. -/
def oracleOfEstimator [Fintype V] (R : ReliabilityEstimator) : Oracle (Query V E) where
  Seed x := (R V {e : E // 0 < x.1 e} (G.positivePart x.1) (fun e => x.1 e) x.2.1 x.2.2).Seed
  law x := (R V {e : E // 0 < x.1 e} (G.positivePart x.1) (fun e => x.1 e) x.2.1 x.2.2).law
  answer x := (R V {e : E // 0 < x.1 e} (G.positivePart x.1) (fun e => x.1 e) x.2.1 x.2.2).value

/-- **The reduction from a reliability estimator on the positive class.**
Let `R` be a randomized estimator of directed two-terminal reliability that,
on every finite directed multigraph with edge probabilities in `(0,1]`, has
relative error at most `ε / (128 * m * (m + 1))` with probability at least 3/4.
Then for every finite directed multigraph with edge probabilities in `[0,1]`,
`0 < ε ≤ 1` and `δ > 0`, the median of `confidenceRuns δ` runs of the cycle
algorithm, with each query answered by the median of independent runs of `R`
on the instance with its zero-probability edges deleted, has relative error
more than `ε` with probability at most `δ`. -/
theorem cycle_fpras_of_estimator [Fintype V] (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (R : ReliabilityEstimator) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ)
    (hR : R.Correct (ε / (128 * Fintype.card E * (Fintype.card E + 1)))) :
    ((G.cycleAlgorithm p (bitBudget (Fintype.card E) ε)
        (reductionBudget (Fintype.card E) ε)).medianOf (confidenceRuns δ)).exp
        ((G.oracleOfEstimator R).amplify (amplifyRounds (Fintype.card E +
          reductionBudget (Fintype.card E) ε * (2 * Fintype.card E))))
        (fun z =>
          if ε * G.cycleMass (edgeLaw p hp0 hp1).toMass <
            |z - G.cycleMass (edgeLaw p hp0 hp1).toMass| then 1 else 0) ≤ δ := by
  apply G.cycle_fpras_confidence p hp0 hp1 _ hε hε1 hδ
  intro x hx
  have hx01 : Prob01 x.1 := derived_prob01 (fun e => ⟨hp0 e, hp1 e⟩) hx.1
  have hrel := G.reliability_positivePart hx01 x.2.1 x.2.2
  have h := hR V {e : E // 0 < x.1 e} (G.positivePart x.1) (fun e => x.1 e) x.2.1 x.2.2
    (fun e => ⟨e.2, (hx01 e.1).2⟩) (by rw [hrel]; exact hx.2)
  rw [hrel] at h
  exact h

end Digraph
end
end DirectedCycleFPRAS
