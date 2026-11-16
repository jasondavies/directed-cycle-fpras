module

public import DirectedCycleFPRAS.CorrectedRejection

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
variable {Q E I : Type} [Fintype E] [DecidableEq E] [Fintype I]

/-- Oracle accuracy depends on the number of edge exposures, not on the final
counting error or sampling tolerance. -/
def rejectionAccuracy (m : ℕ) : ℝ := 1/(16*((m : ℝ)+1))

theorem rejectionAccuracy_bounds (m : ℕ) :
    0 < rejectionAccuracy m ∧ rejectionAccuracy m ≤ 1/16 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold rejectionAccuracy
  constructor
  · positivity
  · apply (div_le_iff₀ (show 0 < 16*((m : ℝ)+1) by positivity)).mpr
    nlinarith

/-- Bernoulli's inequality gives a uniform rejection envelope without any
exponential estimates. -/
theorem rejectionAccuracy_envelope (m : ℕ) :
    1/2 ≤ (1-rejectionAccuracy m)*(1-2*rejectionAccuracy m)^m := by
  have ha := rejectionAccuracy_bounds m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hb := one_add_mul_le_pow (a := -2*rejectionAccuracy m) (by linarith : -2 ≤ -2*rejectionAccuracy m) m
  have he : 2*rejectionAccuracy m*(m : ℝ) ≤ 1/8 := by
    unfold rejectionAccuracy
    have hd : 0 < 16*((m : ℝ)+1) := by positivity
    rw [show 2*(1/(16*((m : ℝ)+1)))*(m : ℝ) = (2*(m : ℝ))/(16*((m : ℝ)+1)) by ring]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hp : 7/8 ≤ (1-2*rejectionAccuracy m)^m := by
    have hr : 1 + -2*rejectionAccuracy m = 1-2*rejectionAccuracy m := by ring
    rw [hr] at hb
    nlinarith
  have hh := mul_le_mul (show (15:ℝ)/16 ≤ 1-rejectionAccuracy m by linarith) hp
    (by norm_num : (0:ℝ) ≤ 7/8) (by linarith : 0 ≤ 1-rejectionAccuracy m)
  norm_num at hh
  linarith

/-- Reliability exposure supplies every hypothesis of the generic rejection
identity. Initial witness estimates and branch estimates use the same accuracy. -/
theorem recordedRejectionSpec (O : Oracle Q) (B : I → (E → Bool) → Prop)
    (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop)
    (Inv : (E → ℝ) → Prop) (hInv : ∀ q, Inv q → Prob01 q)
    (hpin : ∀ q e b, Inv q → Inv (pin q e b))
    (hfeas : ∀ i q, Inv q → (feas i q ↔ 0 < eventMass q (B i)))
    (p : E → ℝ) (hp : Inv p) (l : List E) (hl : ∀ e, e ∈ l)
    (w : I → ℝ) (hW : 0 < ∑ i, eventMass p (B i))
    (hw : ∀ i, |w i-eventMass p (B i)| ≤ rejectionAccuracy l.length*eventMass p (B i))
    (hacc : ∀ i q, Inv q → 0 < eventMass q (B i) → ∀ s,
      |O.answer (mk i q) s-eventMass q (B i)| ≤ rejectionAccuracy l.length*eventMass q (B i)) :
    RejectionSpec O (edgeLaw p (fun e => (hInv p hp e).1) (fun e => (hInv p hp e).2)).toMass B w
      (fun i => recordedExpose (mk i) (feas i) l p) := by
  let a := rejectionAccuracy l.length
  have ha := rejectionAccuracy_bounds l.length
  have hnorm := normalized_lower (fun i => eventMass p (B i)) w
  have hlo (i : I) : (1-a)*eventMass p (B i) ≤ w i := by
    have h := (abs_le.mp (hw i)).1
    dsimp [a]
    nlinarith
  have hnonneg (i : I) : 0 ≤ w i := le_trans
    (mul_nonneg (by dsimp [a]; linarith) (eventMass_nonneg (hInv p hp) _)) (hlo i)
  have htotal : 0 < ∑ i, w i := by
    have hs : (1-a)*(∑ i, eventMass p (B i)) ≤ ∑ i, w i := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hlo i
    exact lt_of_lt_of_le (mul_pos (by dsimp [a]; linarith) hW) hs
  have hpos (i : I) (hi : 0 < w i) : 0 < eventMass p (B i) := by
    have hz := eventMass_nonneg (hInv p hp) (B i)
    have he := (abs_le.mp (hw i)).2
    by_contra hn
    have hzero := le_antisymm (not_lt.mp hn) hz
    simp [hzero] at he
    linarith
  refine ⟨hnonneg, htotal, ?_, ?_, ?_⟩
  · intro i x hB hmass
    have ht := possible_mass_pos (hInv p hp) (show possible p (B i) x from ⟨hB, hmass⟩)
    exact lt_of_lt_of_le (mul_pos (by dsimp [a]; linarith) ht) (hlo i)
  · intro i hi
    apply (recordedExpose_envelope O (B i) (mk i) (feas i) Inv ha.1.le (by linarith)
      hInv hpin (hfeas i) (hacc i) l p hp (hpos i hi)
      (fun e he => False.elim (he (hl e)))).imp
    intro r hr
    refine ⟨hr.1.1, hr.1.2, hr.2.1, ?_⟩
    have hR := hpos i hi
    have hc : 0 ≤ (1-2*a)^l.length := pow_nonneg (by dsimp [a]; linarith) _
    have hμ := hr.1.2
    have hcw : condWeight p (B i) r.1 = edgeWeight p r.1/eventMass p (B i) := by
      simp [condWeight, hr.1.1]
    rw [hcw] at hr
    have hm : (1-a)*(1-2*a)^l.length*(edgeWeight p r.1) ≤ w i*r.2 := by
      have hmul := mul_le_mul (hlo i) hr.2.2
        (mul_nonneg hc (div_nonneg hμ.le hR.le)) (hnonneg i)
      have heq : ((1-a)*eventMass p (B i))*
          ((1-2*a)^l.length*(edgeWeight p r.1/eventMass p (B i))) =
          (1-a)*(1-2*a)^l.length*edgeWeight p r.1 := by field_simp
      rw [heq] at hmul
      exact hmul
    have hb := mul_le_mul_of_nonneg_right (rejectionAccuracy_envelope l.length) hμ.le
    change edgeWeight p r.1 ≤ _
    dsimp [a] at hm
    nlinarith
  · intro i hi f
    apply (recordedExpose_inverse O (B i) (mk i) (feas i) Inv ha.1.le (by linarith)
      hInv hpin (hfeas i) (hacc i) l p hp (hpos i hi)
      (fun e he => False.elim (he (hl e))) f).trans
    unfold completionSum
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : possible p (B i) x
    · rw [ite_eq_left hx, ite_eq_left (show B i x ∧ 0 < (edgeLaw p _ _).value x from hx)]
    · rw [ite_eq_right hx, ite_eq_right (show ¬ (B i x ∧ 0 < (edgeLaw p _ _).value x) from hx)]

end
end DirectedCycleFPRAS
