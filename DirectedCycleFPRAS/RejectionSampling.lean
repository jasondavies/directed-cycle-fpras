module

public import DirectedCycleFPRAS.RejectionCounting

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {Q Ω : Type} [Fintype Ω]

/-- Stop at the first accepted configuration, with a deterministic fallback
at the prescribed cap. This is a worst-case bounded program. -/
def cappedSample (proposal : Prog Q (Option Ω)) (fallback : Ω) : ℕ → Prog Q Ω
  | 0 => .ret fallback
  | n+1 => proposal.bind fun x => x.elim (cappedSample proposal fallback n) Prog.ret

/-- Any continuation after rejection depends only on the acceptance
subdistribution and its total mass. -/
theorem option_exp (O : Oracle Q) (proposal : Prog Q (Option Ω)) (c : ℝ) (f : Ω → ℝ) :
    proposal.exp O (fun x => x.elim c f) =
      proposal.exp O (acceptedTest f) + c*(1-proposal.exp O (acceptedTest (fun _ => 1))) := by
  have he : (fun x : Option Ω => x.elim c f) = fun x =>
      acceptedTest f x + (c + (-c)*acceptedTest (fun _ => 1) x) := by
    funext x
    cases x <;> simp [acceptedTest]
  rw [he, Prog.exp_add, Prog.exp_add, Prog.exp_const, Prog.exp_mul_left]
  ring

/-- The capped sampler is exactly a mixture of the target law and the fallback.
The fallback mass is the probability that every proposal is rejected. -/
theorem cappedSample_exp (O : Oracle Q) (proposal : Prog Q (Option Ω)) (fallback : Ω)
    (ν : Law Ω) (q : ℝ)
    (haccept : ∀ f, proposal.exp O (acceptedTest f) = q*ν.expectation f)
    (n : ℕ) (f : Ω → ℝ) :
    (cappedSample proposal fallback n).exp O f =
      (1-q)^n*f fallback + (1-(1-q)^n)*ν.expectation f := by
  have hq : proposal.exp O (acceptedTest (fun _ => 1)) = q := by
    rw [haccept]
    simp [Law.expectation, ν.sum_one]
  induction n with
  | zero => simp [cappedSample, Prog.exp]
  | succ n ih =>
    rw [cappedSample, Prog.exp_bind]
    have he : (fun x : Option Ω =>
        (x.elim (cappedSample proposal fallback n) Prog.ret).exp O f) =
        fun x => x.elim ((cappedSample proposal fallback n).exp O f) f := by
      funext x; cases x <;> rfl
    rw [he, option_exp, haccept, hq, ih, pow_succ]
    ring

/-- Eventwise total-variation bound for the capped sampler. -/
theorem cappedSample_error (O : Oracle Q) (proposal : Prog Q (Option Ω)) (fallback : Ω)
    (ν : Law Ω) {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1)
    (haccept : ∀ f, proposal.exp O (acceptedTest f) = q*ν.expectation f)
    (n : ℕ) (f : Ω → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |(cappedSample proposal fallback n).exp O f-ν.expectation f| ≤ (1-q)^n := by
  have hν0 : 0 ≤ ν.expectation f := Finset.sum_nonneg fun x _ => mul_nonneg (ν.nonneg x) (hf0 x)
  have hν1 : ν.expectation f ≤ 1 := by
    calc ν.expectation f ≤ ∑ x, ν.value x*1 :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hf1 x) (ν.nonneg x)
      _ = 1 := by simp [ν.sum_one]
  rw [cappedSample_exp O proposal fallback ν q haccept n f]
  have he : (1-q)^n*f fallback + (1-(1-q)^n)*ν.expectation f-ν.expectation f =
      (1-q)^n*(f fallback-ν.expectation f) := by ring
  rw [he, abs_mul, abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ 1-q) n)]
  have hab : |f fallback-ν.expectation f| ≤ 1 := abs_le.mpr ⟨by linarith [hf0 fallback], by linarith [hf1 fallback]⟩
  simpa using mul_le_mul_of_nonneg_left hab (pow_nonneg (by linarith : 0 ≤ 1-q) n)

/-- Conditioning the product measure on the witness union. -/
def unionLaw {I : Type} [Fintype I] (μ : Mass Ω) (A : I → Ω → Prop)
    (hZ : 0 < μ.unionMass A) : Law Ω where
  value x := (if 0 < Mass.multiplicity A x then μ.value x else 0)/μ.unionMass A
  nonneg x := div_nonneg (by split_ifs; exact μ.nonneg x; rfl) hZ.le
  sum_one := by rw [← Finset.sum_div]; exact div_self (ne_of_gt hZ)

/-- The generic rejection identity gives the conditional law needed by the
bounded sampler, with no dependence on how rare the union event is. -/
theorem correctedProposal_conditional {I : Type} [Fintype I]
    (O : Oracle Q) (μ : Mass Ω) (A : I → Ω → Prop) (w : I → ℝ)
    (proposal : I → Prog Q (Ω × ℝ)) (d : I) (H : RejectionSpec O μ A w proposal)
    (hZ : 0 < μ.unionMass A) (f : Ω → ℝ) :
    (correctedProposal μ A w proposal d).exp O (acceptedTest f) =
      (μ.unionMass A/(2*∑ i, w i))*(unionLaw μ A hZ).expectation f := by
  rw [correctedProposal_exp O μ A w proposal d H]
  unfold Law.expectation unionLaw
  change (∑ x, if 0 < Mass.multiplicity A x then μ.value x*f x else 0)/(2*∑ i, w i) =
    (μ.unionMass A/(2*∑ i, w i))*(∑ x, ((if 0 < Mass.multiplicity A x then μ.value x else 0)/μ.unionMass A)*f x)
  simp only [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs
  · field_simp
  · simp

/-- Each block of `d` proposals succeeds with probability at least one half
when the individual success probability is at least `1/d`. -/
theorem rejection_block {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {d : ℕ}
    (hd : 0 < d) (hqd : 1 ≤ (d : ℝ)*q) : (1-q)^d ≤ 1/2 := by
  by_cases hq : q = 1
  · simp [hq, ne_of_gt hd]
  have hqp : 0 < 1-q := sub_pos.mpr (lt_of_le_of_ne hq1 hq)
  have hfrac : 0 ≤ q/(1-q) := div_nonneg hq0 hqp.le
  have hb := one_add_mul_le_pow (a := q/(1-q)) (by linarith) d
  have hf : q ≤ q/(1-q) := (le_div_iff₀ hqp).mpr (by nlinarith [sq_nonneg q])
  have hh : 2 ≤ (1+q/(1-q))^d := by
    have := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg d)
    linarith
  have hid : 1+q/(1-q) = (1-q)⁻¹ := by field_simp; ring
  rw [hid, inv_pow] at hh
  have hp := pow_pos hqp d
  have ht : 2*(1-q)^d ≤ 1 := by
    have := (le_div_iff₀ hp).mp (show 2 ≤ 1/(1-q)^d by simpa using hh)
    exact this
  linarith

/-- A logarithmic number of blocks gives exponentially small timeout mass. -/
theorem rejection_timeout {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {d : ℕ}
    (hd : 0 < d) (hqd : 1 ≤ (d : ℝ)*q) (r : ℕ) :
    (1-q)^(d*r) ≤ (1/2 : ℝ)^r := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (pow_nonneg (by linarith) d) (rejection_block hq0 hq1 hd hqd) r

end
end DirectedCycleFPRAS
