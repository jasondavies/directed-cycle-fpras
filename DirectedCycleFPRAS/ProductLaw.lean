module

public import DirectedCycleFPRAS.CycleEstimator

@[expose] public section

/-!
# Product laws with pinned coordinates

Residual instances of the sequential sampler are described by pinning edge
probabilities to zero or one. This file develops the algebra of the product
weight under pinning: the one-edge decomposition, independence of an event
from an irrelevant coordinate, exact positivity of monotone events via the
positive-probability support, and the conditional law of an event.

Everything is stated for the raw product weight `edgeWeight`, which needs no
proof that the parameters are probabilities. It agrees definitionally with
`edgeLaw`.
-/

namespace DirectedCycleFPRAS

open scoped BigOperators
open Classical

noncomputable section

variable {E : Type} [Fintype E] [DecidableEq E]

/-- The product weight of an outcome, with no side conditions on the parameters. -/
def edgeWeight (q : E → ℝ) (ω : E → Bool) : ℝ := ∏ e, if ω e then q e else 1 - q e

theorem edgeLaw_value (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (ω : E → Bool) :
    (edgeLaw p hp0 hp1).value ω = edgeWeight p ω := rfl

/-- The weights sum to one for arbitrary real parameters. -/
theorem edgeWeight_sum (q : E → ℝ) : ∑ ω, edgeWeight q ω = 1 := by
  unfold edgeWeight
  rw [← Fintype.prod_sum (fun (e : E) (b : Bool) => if b then q e else 1 - q e)]
  apply Finset.prod_eq_one
  intro e _
  simp

/-- All parameters are probabilities. -/
def Prob01 (q : E → ℝ) : Prop := ∀ e, 0 ≤ q e ∧ q e ≤ 1

/-- Fix the bit of edge `f` by replacing its probability with one or zero. -/
def pin (q : E → ℝ) (f : E) (b : Bool) : E → ℝ := Function.update q f (if b then 1 else 0)

omit [Fintype E] in
theorem pin_self (q : E → ℝ) (f : E) (b : Bool) : pin q f b f = if b then 1 else 0 := by
  simp [pin]

omit [Fintype E] in
theorem pin_of_ne (q : E → ℝ) {e f : E} (b : Bool) (h : e ≠ f) : pin q f b e = q e := by
  simp [pin, h]

omit [Fintype E] in
theorem prob01_pin {q : E → ℝ} (hq : Prob01 q) (f : E) (b : Bool) : Prob01 (pin q f b) := by
  intro e
  by_cases h : e = f
  · subst h
    rw [pin_self]
    cases b <;> simp
  · rw [pin_of_ne q b h]
    exact hq e

omit [DecidableEq E] in
theorem edgeWeight_nonneg {q : E → ℝ} (hq : Prob01 q) (ω : E → Bool) : 0 ≤ edgeWeight q ω := by
  apply Finset.prod_nonneg
  intro e _
  split_ifs
  · exact (hq e).1
  · exact sub_nonneg.mpr (hq e).2

/-- The factors of the product weight away from a designated edge. -/
def restWeight (q : E → ℝ) (f : E) (ω : E → Bool) : ℝ :=
  ∏ e ∈ Finset.univ.erase f, if ω e then q e else 1 - q e

theorem edgeWeight_eq_mul_rest (q : E → ℝ) (f : E) (ω : E → Bool) :
    edgeWeight q ω = (if ω f then q f else 1 - q f) * restWeight q f ω := by
  unfold edgeWeight restWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ f)]

theorem restWeight_pin (q : E → ℝ) (f : E) (b : Bool) (ω : E → Bool) :
    restWeight (pin q f b) f ω = restWeight q f ω := by
  unfold restWeight
  apply Finset.prod_congr rfl
  intro e he
  rw [pin_of_ne q b (Finset.ne_of_mem_erase he)]

theorem edgeWeight_pin (q : E → ℝ) (f : E) (b : Bool) (ω : E → Bool) :
    edgeWeight (pin q f b) ω = (if ω f = b then 1 else 0) * restWeight q f ω := by
  rw [edgeWeight_eq_mul_rest _ f, restWeight_pin, pin_self]
  congr 1
  cases b <;> cases ω f <;> simp

/-- Multilinearity of the product weight in one parameter. -/
theorem edgeWeight_split (q : E → ℝ) (f : E) (ω : E → Bool) :
    edgeWeight q ω =
      q f * edgeWeight (pin q f true) ω + (1 - q f) * edgeWeight (pin q f false) ω := by
  rw [edgeWeight_pin, edgeWeight_pin, edgeWeight_eq_mul_rest q f]
  cases ω f <;> simp

/-- Probability of an event under the product weight. -/
def eventMass (q : E → ℝ) (B : (E → Bool) → Prop) : ℝ :=
  ∑ ω, if B ω then edgeWeight q ω else 0

theorem eventMass_nonneg {q : E → ℝ} (hq : Prob01 q) (B : (E → Bool) → Prop) :
    0 ≤ eventMass q B := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact edgeWeight_nonneg hq ω
  · rfl

/-- The one-edge decomposition behind the sequential sampler: the two branch
weights of an exposure add up to the current residual probability. -/
theorem eventMass_split (q : E → ℝ) (f : E) (B : (E → Bool) → Prop) :
    eventMass q B =
      q f * eventMass (pin q f true) B + (1 - q f) * eventMass (pin q f false) B := by
  unfold eventMass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs
  · exact edgeWeight_split q f ω
  · simp

theorem eventMass_term_eq_zero {q : E → ℝ} (hq : Prob01 q) {B : (E → Bool) → Prop}
    (h : eventMass q B = 0) (ω : E → Bool) : (if B ω then edgeWeight q ω else 0) = 0 := by
  have hnonneg : ∀ ω ∈ (Finset.univ : Finset (E → Bool)),
      0 ≤ (if B ω then edgeWeight q ω else 0) := by
    intro ω _
    split_ifs
    · exact edgeWeight_nonneg hq ω
    · rfl
  exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h ω (Finset.mem_univ ω)

/-- An event that ignores the bit of `f` has the same probability under both
pinnings of `f`. -/
theorem eventMass_pin_flip (q : E → ℝ) (f : E) (B : (E → Bool) → Prop)
    (hB : ∀ ω b, B (Function.update ω f b) ↔ B ω) :
    eventMass (pin q f true) B = eventMass (pin q f false) B := by
  unfold eventMass
  simp_rw [edgeWeight_pin]
  let σ : (E → Bool) ≃ (E → Bool) :=
    Function.Involutive.toPerm (fun ω => Function.update ω f (!ω f)) (by
      intro ω
      ext e
      by_cases h : e = f
      · subst h
        simp
      · simp [Function.update_of_ne h])
  apply Fintype.sum_equiv σ
  intro ω
  have hσ : σ ω = Function.update ω f (!ω f) := rfl
  have hr : restWeight q f (σ ω) = restWeight q f ω := by
    unfold restWeight
    apply Finset.prod_congr rfl
    intro e he
    rw [hσ, Function.update_of_ne (Finset.ne_of_mem_erase he)]
  have hb : B (σ ω) ↔ B ω := hB ω _
  have hf : σ ω f = !ω f := by simp [hσ]
  simp only [hb, hr, hf]
  cases ω f <;> simp

/-- Consequently its probability does not depend on the parameter of `f`. -/
theorem eventMass_pin_indep (q : E → ℝ) (f : E) (b : Bool) (B : (E → Bool) → Prop)
    (hB : ∀ ω b, B (Function.update ω f b) ↔ B ω) :
    eventMass (pin q f b) B = eventMass q B := by
  have h := eventMass_pin_flip q f B hB
  rw [eventMass_split q f B]
  cases b
  · rw [h]
    ring
  · rw [← h]
    ring

/-- The outcome retaining exactly the positive-probability edges. -/
def support (q : E → ℝ) : E → Bool := fun e => decide (0 < q e)

omit [DecidableEq E] in
theorem edgeWeight_support_pos {q : E → ℝ} (hq : Prob01 q) : 0 < edgeWeight q (support q) := by
  apply Finset.prod_pos
  intro e _
  by_cases h : 0 < q e
  · simp [support, h]
  · have hz : q e = 0 := le_antisymm (not_lt.mp h) (hq e).1
    simp [support, hz]

/-- A monotone event has positive probability exactly when it holds on the
positive-probability support. This is the exact feasibility test used before
every oracle call, and the acyclicity test of the zero case. -/
theorem eventMass_pos_iff {q : E → ℝ} (hq : Prob01 q) (B : (E → Bool) → Prop)
    (hmono : ∀ ω ω' : E → Bool, (∀ e, ω e = true → ω' e = true) → B ω → B ω') :
    0 < eventMass q B ↔ B (support q) := by
  constructor
  · intro hpos
    by_contra hB
    have hz : eventMass q B = 0 := by
      apply Finset.sum_eq_zero
      intro ω _
      split_ifs with hω
      · by_contra hne
        apply hB
        refine hmono ω _ ?_ hω
        intro e he
        have hfac := Finset.prod_ne_zero_iff.mp hne e (Finset.mem_univ e)
        rw [ite_eq_left he] at hfac
        simpa [support] using lt_of_le_of_ne (hq e).1 (Ne.symm hfac)
      · rfl
    rw [hz] at hpos
    exact lt_irrefl _ hpos
  · intro hB
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun ω => if B ω then edgeWeight q ω else 0)
      (fun ω _ => by
        split_ifs
        · exact edgeWeight_nonneg hq ω
        · rfl) (Finset.mem_univ (support q))
    simp only [ite_eq_left hB] at h
    exact lt_of_lt_of_le (edgeWeight_support_pos hq) h

/-- The outcome determined by fully pinned parameters. -/
def pinned (q : E → ℝ) : E → Bool := fun e => decide (q e = 1)

omit [DecidableEq E] in
/-- Fully pinned parameters give a point mass. -/
theorem edgeWeight_bool {q : E → ℝ} (hq : ∀ e, q e = 0 ∨ q e = 1) (ω : E → Bool) :
    edgeWeight q ω = if ω = pinned q then 1 else 0 := by
  split_ifs with h
  · subst h
    apply Finset.prod_eq_one
    intro e _
    rcases hq e with h0 | h1
    · simp [pinned, h0]
    · simp [pinned, h1]
  · obtain ⟨e, he⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    rcases hq e with h0 | h1
    · have hω : ω e = true := by simpa [pinned, h0] using he
      simp [hω, h0]
    · have hω : ω e = false := by simpa [pinned, h1] using he
      simp [hω, h1]

/-- The product law conditioned on an event. It is zero when the event is null. -/
def condWeight (q : E → ℝ) (B : (E → Bool) → Prop) (ω : E → Bool) : ℝ :=
  (if B ω then edgeWeight q ω else 0) / eventMass q B

/-- With all bits pinned and the event feasible, the conditional law is the
point mass at the pinned outcome. -/
theorem condWeight_bool {q : E → ℝ} (hq : ∀ e, q e = 0 ∨ q e = 1)
    {B : (E → Bool) → Prop} (hpos : 0 < eventMass q B) (ω : E → Bool) :
    condWeight q B ω = if ω = pinned q then 1 else 0 := by
  have hm : eventMass q B = if B (pinned q) then 1 else 0 := by
    unfold eventMass
    simp_rw [edgeWeight_bool hq]
    rw [Finset.sum_eq_single (pinned q)]
    · simp
    · intro ω _ hne
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hB : B (pinned q) := by
    by_contra h
    rw [hm, ite_eq_right h] at hpos
    exact lt_irrefl _ hpos
  rw [condWeight, hm, ite_eq_left hB, div_one, edgeWeight_bool hq]
  by_cases h : ω = pinned q
  · subst h
    simp [hB]
  · simp [h]

/-- Exact sequential sampling: the conditional law is the mixture of the two
pinned conditional laws, with branch probabilities proportional to
`q f * R₁` and `(1 - q f) * R₀`, where `R_b` are the residual probabilities. -/
theorem condWeight_split {q : E → ℝ} (hq : Prob01 q) (f : E) (B : (E → Bool) → Prop)
    (ω : E → Bool) :
    condWeight q B ω = ∑ b : Bool,
      ((if b then q f else 1 - q f) * eventMass (pin q f b) B / eventMass q B) *
        condWeight (pin q f b) B ω := by
  have key : ∀ b : Bool,
      ((if b then q f else 1 - q f) * eventMass (pin q f b) B / eventMass q B) *
        condWeight (pin q f b) B ω =
      (if b then q f else 1 - q f) * (if B ω then edgeWeight (pin q f b) ω else 0) /
        eventMass q B := by
    intro b
    by_cases hz : eventMass (pin q f b) B = 0
    · rw [condWeight, hz, eventMass_term_eq_zero (prob01_pin hq f b) hz]
      simp
    · unfold condWeight
      field_simp
  rw [Fintype.sum_bool, key, key]
  unfold condWeight
  by_cases hB : B ω
  · simp only [ite_eq_left hB, ite_true, Bool.false_eq_true, ite_false]
    rw [edgeWeight_split q f ω]
    ring
  · simp [hB]

end
end DirectedCycleFPRAS
