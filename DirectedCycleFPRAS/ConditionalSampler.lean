module

public import DirectedCycleFPRAS.ProductLaw
public import DirectedCycleFPRAS.RandomBits

@[expose] public section

/-!
# Sequential conditional sampling by edge exposure

`expose` samples the product law conditioned on an event by exposing one edge
bit at a time. The two branch weights are the edge probability times the
residual probability of the event after pinning the bit; the residual
probabilities are obtained from oracle calls guarded by an exact feasibility
test, so an impossible branch receives weight zero without any call.

Each binary choice is made from `bits` uniform random bits, by the
cumulative-interval rule of `RandomBits`.

`expose_l1` shows that if every guarded answer is within relative error `α`,
the output law is within L1 distance `4 * α + 2 / 2^bits` per exposed edge of
the exact conditional law. The oracle may be randomized: the bound is averaged
over the fresh seed of every call.
-/

namespace DirectedCycleFPRAS

open scoped BigOperators
open Classical

noncomputable section

/-- Averaging laws that are each close to a fixed target stays close. -/
theorem l1_average_le {Ω S : Type*} [Fintype Ω] [Fintype S] (ρ : S → ℝ) (F : S → Ω → ℝ)
    (C : Ω → ℝ) {η : ℝ} (hρ : ∀ s, 0 ≤ ρ s) (hsum : ∑ s, ρ s = 1)
    (h : ∀ s, l1 (F s) C ≤ η) :
    l1 (fun ω => ∑ s, ρ s * F s ω) C ≤ η := by
  have hC : (fun ω => ∑ s, ρ s * C ω) = C := by
    ext ω
    rw [← Finset.sum_mul, hsum, one_mul]
  calc l1 (fun ω => ∑ s, ρ s * F s ω) C
      = l1 (fun ω => ∑ s, ρ s * F s ω) (fun ω => ∑ s, ρ s * C ω) := by rw [hC]
    _ ≤ ∑ s, ρ s * l1 (F s) C := mixture_stability ρ F (fun _ => C) hρ
    _ ≤ ∑ s, ρ s * η :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (hρ s)
    _ = η := by rw [← Finset.sum_mul, hsum, one_mul]

/-- One step of approximate sequential sampling: selection error plus the
error of the continuation laws, the latter needed only on alternatives of
positive exact probability. -/
theorem l1_mixture_le {Ω I : Type*} [Fintype Ω] [Fintype I] (a' a : I → ℝ)
    (D C : I → Ω → ℝ) {η₁ η₂ : ℝ}
    (hD0 : ∀ i x, 0 ≤ D i x) (hD1 : ∀ i, ∑ x, D i x = 1)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1)
    (hsel : l1 a' a ≤ η₁) (hcond : ∀ i, 0 < a i → l1 (D i) (C i) ≤ η₂) :
    l1 (fun x => ∑ i, a' i * D i x) (fun x => ∑ i, a i * C i x) ≤ η₁ + η₂ := by
  calc l1 (fun x => ∑ i, a' i * D i x) (fun x => ∑ i, a i * C i x)
      ≤ l1 (fun x => ∑ i, a' i * D i x) (fun x => ∑ i, a i * D i x) +
          l1 (fun x => ∑ i, a i * D i x) (fun x => ∑ i, a i * C i x) := l1_triangle _ _ _
    _ ≤ l1 a' a + ∑ i, a i * l1 (D i) (C i) :=
      add_le_add (selection_stability _ _ _ hD0 hD1) (mixture_stability _ _ _ ha)
    _ ≤ η₁ + ∑ i, a i * η₂ := by
      apply add_le_add hsel
      apply Finset.sum_le_sum
      intro i _
      rcases (ha i).eq_or_lt with h | h
      · rw [← h]
        simp
      · exact mul_le_mul_of_nonneg_left (hcond i h) (ha i)
    _ = η₁ + η₂ := by rw [← Finset.sum_mul, hsum, one_mul]

variable {Q : Type} {E : Type} [Fintype E] [DecidableEq E]

/-- Expose the listed edges one at a time. `mk q` is the oracle query for the
residual probability under parameters `q`, and `feas q` the exact test that
this probability is positive. -/
def expose (bits : ℕ) (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop) :
    List E → (E → ℝ) → Prog Q (E → Bool)
  | [], q => .ret (pinned q)
  | f :: l, q =>
    Prog.guarded (feas (pin q f true)) (mk (pin q f true)) fun r₁ =>
    Prog.guarded (feas (pin q f false)) (mk (pin q f false)) fun r₀ =>
    Prog.draw bits
        (normLaw (fun b : Bool => if b then q f * r₁ else (1 - q f) * r₀) true) fun b =>
      expose bits mk feas l (pin q f b)

omit [Fintype E] in
/-- Two guarded calls per exposed edge. -/
theorem expose_queryBound (bits : ℕ) (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop)
    (l : List E) (q : E → ℝ) : Prog.QueryBound (expose bits mk feas l q) (2 * l.length) := by
  induction l generalizing q with
  | nil => exact .ret _ _
  | cons f l ih =>
    have h : Prog.QueryBound (expose bits mk feas (f :: l) q) (2 * l.length + 1 + 1) :=
      Prog.QueryBound.guarded fun r₁ => Prog.QueryBound.guarded fun r₀ =>
        Prog.QueryBound.draw fun b => ih (pin q f b)
    exact h.mono (by simp only [List.length_cons]; omega)

omit [Fintype E] in
/-- One `bits`-bit draw per exposed edge, and no other internal randomness. -/
theorem expose_bitBound (bits : ℕ) (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop)
    (l : List E) (q : E → ℝ) : Prog.BitBound bits (expose bits mk feas l q) l.length := by
  induction l generalizing q with
  | nil => exact .ret _ _
  | cons f l ih =>
    exact Prog.BitBound.guarded fun r₁ => Prog.BitBound.guarded fun r₀ =>
      Prog.BitBound.ofDraw fun b => ih (pin q f b)

/-- The approximate sequential sampler is close to the exact conditional law.
The hypotheses say that the feasibility test is exact and that every oracle
answer to a feasible query has relative error at most `α`, for every seed.
They are required only for parameters satisfying an invariant `Inv` that is
preserved by pinning, so the oracle is constrained only on the residual
instances that can actually arise. -/
theorem expose_l1 (bits : ℕ) (O : Oracle Q) (B : (E → Bool) → Prop) (mk : (E → ℝ) → Q)
    (feas : (E → ℝ) → Prop) (Inv : (E → ℝ) → Prop) {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2)
    (hInv : ∀ q, Inv q → Prob01 q) (hpin : ∀ q f b, Inv q → Inv (pin q f b))
    (hfeas : ∀ q, Inv q → (feas q ↔ 0 < eventMass q B))
    (hacc : ∀ q, Inv q → 0 < eventMass q B →
      ∀ s, |O.answer (mk q) s - eventMass q B| ≤ α * eventMass q B)
    (l : List E) (q : E → ℝ) (hqI : Inv q) (hpos : 0 < eventMass q B)
    (hl : ∀ e, e ∉ l → q e = 0 ∨ q e = 1) :
    l1 ((expose bits mk feas l q).law O).value (condWeight q B) ≤
      l.length * (4 * α + 2 / (2 : ℝ) ^ bits) := by
  induction l generalizing q with
  | nil =>
    have h01 : ∀ e, q e = 0 ∨ q e = 1 := fun e => hl e (by simp)
    have heq : ((expose bits mk feas [] q).law O).value = condWeight q B := by
      ext ω
      rw [condWeight_bool h01 hpos]
      simp only [Prog.law, expose, Prog.exp]
      by_cases h : ω = pinned q
      · rw [ite_eq_left h, ite_eq_left h.symm]
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    rw [heq]
    simp [l1]
  | cons f l ih =>
    have hq : Prob01 q := hInv q hqI
    -- Guarded answers are accurate, including the exact zero of an impossible branch.
    have hans : ∀ q' : E → ℝ, Inv q' → ∀ s,
        |(if feas q' then O.answer (mk q') s else 0) - eventMass q' B| ≤
          α * eventMass q' B := by
      intro q' hq' s
      by_cases hf : feas q'
      · rw [ite_eq_left hf]
        exact hacc q' hq' ((hfeas q' hq').mp hf) s
      · have hz : eventMass q' B = 0 :=
          le_antisymm (not_lt.mp fun h => hf ((hfeas q' hq').mpr h))
            (eventMass_nonneg (hInv q' hq') B)
        rw [ite_eq_right hf, hz]
        simp
    have hlaw : ((expose bits mk feas (f :: l) q).law O).value = fun ω =>
        ∑ s₁, (O.law (mk (pin q f true))).value s₁ *
          ∑ s₀, (O.law (mk (pin q f false))).value s₀ *
            ∑ b, (bitLaw bits (normLaw (fun b : Bool =>
                if b then q f * (if feas (pin q f true) then O.answer (mk (pin q f true)) s₁ else 0)
                else (1 - q f) *
                  (if feas (pin q f false) then O.answer (mk (pin q f false)) s₀ else 0))
                true)).value b *
              ((expose bits mk feas l (pin q f b)).law O).value ω := by
      ext ω
      simp only [Prog.law, expose, Prog.exp_guarded, Prog.exp_draw]
    rw [hlaw]
    have hlen : ((f :: l).length : ℝ) * (4 * α + 2 / (2 : ℝ) ^ bits) =
        (4 * α + 2 / (2 : ℝ) ^ bits) + l.length * (4 * α + 2 / (2 : ℝ) ^ bits) := by
      simp only [List.length_cons]
      push_cast
      ring
    rw [hlen]
    apply l1_average_le _ _ _ (fun s => (O.law _).nonneg s) (O.law _).sum_one
    intro s₁
    apply l1_average_le _ _ _ (fun s => (O.law _).nonneg s) (O.law _).sum_one
    intro s₀
    have h1 := hans (pin q f true) (hpin q f true hqI) s₁
    have h0 := hans (pin q f false) (hpin q f false hqI) s₀
    generalize (if feas (pin q f true) then O.answer (mk (pin q f true)) s₁ else 0) = r₁ at h1 ⊢
    generalize (if feas (pin q f false) then O.answer (mk (pin q f false)) s₀ else 0) = r₀ at h0 ⊢
    -- Exact and estimated branch weights.
    let a : Bool → ℝ := fun b => (if b then q f else 1 - q f) * eventMass (pin q f b) B
    let a' : Bool → ℝ := fun b => if b then q f * r₁ else (1 - q f) * r₀
    have hasum : ∑ b, a b = eventMass q B := by
      rw [Fintype.sum_bool, eventMass_split q f B]
      simp [a]
    have hc1 : 0 ≤ q f := (hq f).1
    have hc0 : 0 ≤ 1 - q f := sub_nonneg.mpr (hq f).2
    have ha0 : ∀ b, 0 ≤ a b := by
      intro b
      cases b
      · exact mul_nonneg (by simpa using hc0) (eventMass_nonneg (prob01_pin hq f false) B)
      · exact mul_nonneg (by simpa using hc1) (eventMass_nonneg (prob01_pin hq f true) B)
    have hest : ∀ b, |a' b - a b| ≤ α * a b := by
      intro b
      cases b
      · have h := mul_le_mul_of_nonneg_left h0 hc0
        simpa [a, a', ← mul_sub, abs_mul, abs_of_nonneg hc0, mul_left_comm] using h
      · have h := mul_le_mul_of_nonneg_left h1 hc1
        simpa [a, a', ← mul_sub, abs_mul, abs_of_nonneg hc1, mul_left_comm] using h
    have hlow : ∀ b, (1 - α) * a b ≤ a' b := by
      intro b
      have := (abs_le.mp (hest b)).1
      linarith
    have ha'0 : ∀ b, 0 ≤ a' b := fun b =>
      (mul_nonneg (by linarith) (ha0 b)).trans (hlow b)
    have hapos : 0 < ∑ b, a b := hasum ▸ hpos
    have ha'pos : 0 < ∑ b, a' b := by
      have hle : (1 - α) * ∑ b, a b ≤ ∑ b, a' b := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun b _ => hlow b
      have : 0 < (1 - α) * ∑ b, a b := mul_pos (by linarith) hapos
      linarith
    have hsel := normalised_weights_l1 a a' ha0 hα0 hα hapos hest
    have hval : (normLaw a' true).value = fun b => a' b / ∑ j, a' j :=
      funext (normLaw_value a' true ha'0 ha'pos)
    have hC : condWeight q B = fun ω => ∑ b, (a b / ∑ j, a j) * condWeight (pin q f b) B ω := by
      ext ω
      rw [condWeight_split hq f B ω, hasum]
    -- Rounding to `bits` random bits costs at most `2 / 2^bits` more.
    have hsel' : l1 (bitLaw bits (normLaw a' true)).value (fun b => a b / ∑ j, a j) ≤
        4 * α + 2 / (2 : ℝ) ^ bits := by
      have hbit := bitLaw_l1 bits (normLaw a' true)
      rw [Fintype.card_bool] at hbit
      have hnorm : l1 (normLaw a' true).value (fun b => a b / ∑ j, a j) ≤ 4 * α := by
        rw [hval]
        exact hsel
      have htri := l1_triangle (bitLaw bits (normLaw a' true)).value (normLaw a' true).value
        (fun b => a b / ∑ j, a j)
      push_cast at hbit
      linarith
    change l1 (fun ω => ∑ b, (bitLaw bits (normLaw a' true)).value b *
      ((expose bits mk feas l (pin q f b)).law O).value ω) (condWeight q B) ≤ _
    rw [hC]
    apply l1_mixture_le (fun b => (bitLaw bits (normLaw a' true)).value b)
      (fun b => a b / ∑ j, a j)
      (fun b => ((expose bits mk feas l (pin q f b)).law O).value)
      (fun b => condWeight (pin q f b) B)
    · exact fun b x => Mass.nonneg _ x
    · exact fun b => Law.sum_one _
    · exact fun b => div_nonneg (ha0 b) hapos.le
    · rw [← Finset.sum_div, div_self (ne_of_gt hapos)]
    · exact hsel'
    · intro b hb
      have hab : 0 < a b := by
        by_contra h
        have hz : a b = 0 := le_antisymm (not_lt.mp h) (ha0 b)
        rw [hz, zero_div] at hb
        exact lt_irrefl _ hb
      have hpos' : 0 < eventMass (pin q f b) B := by
        by_contra h
        have hz : eventMass (pin q f b) B = 0 :=
          le_antisymm (not_lt.mp h) (eventMass_nonneg (prob01_pin hq f b) B)
        simp only [a, hz, mul_zero] at hab
        exact lt_irrefl _ hab
      refine ih (pin q f b) (hpin q f b hqI) hpos' ?_
      intro e he
      by_cases hef : e = f
      · subst hef
        rw [pin_self]
        cases b <;> simp
      · rw [pin_of_ne q b hef]
        exact hl e (by simp [hef, he])

end
end DirectedCycleFPRAS
