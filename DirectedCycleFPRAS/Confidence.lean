module

public import DirectedCycleFPRAS.Reduction

@[expose] public section

/-!
# Arbitrary confidence by a median of independent runs

A randomized oracle program with real output that lands in an interval with
probability at least 3/4 is repeated `k` times with fresh randomness and the
median is returned. The failure probability drops to `(7/8)^k`. Applied to the
cycle algorithm this gives confidence `1 - δ` with `O(log (1/δ))` runs.
-/

namespace DirectedCycleFPRAS

open scoped BigOperators
open Classical

noncomputable section

/-- The outcomes of nested independent samples as a vector. -/
def samplesToFn {Ω : Type} : (n : ℕ) → Samples Ω n → Fin n → Ω
  | 0, _ => fun i => i.elim0
  | n + 1, xs => Fin.cons xs.1 (samplesToFn n xs.2)

/-- If the median misses an interval, at least half of the entries miss it;
this is the pointwise exponential-moment bound behind median amplification. -/
theorem median_indicator_le {k : ℕ} (v : Fin k → ℝ) {P : ℝ → Prop}
    (hP : ∀ a b c, P a → P c → a ≤ b → b ≤ c → P b) :
    (if P (median v) then (0 : ℝ) else 1) ≤ ∏ i, (if P (v i) then (1 / 2 : ℝ) else 2) := by
  have hprod0 : 0 ≤ ∏ i, (if P (v i) then (1 / 2 : ℝ) else 2) :=
    Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num
  split_ifs with hm
  · exact hprod0
  · rcases Nat.eq_zero_or_pos k with hk0 | hk
    · subst hk0
      simp
    · have hmaj : ¬ k < 2 * (Finset.univ.filter fun i => P (v i)).card :=
        fun hlt => hm (median_good hk _ hP hlt)
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin k))) (fun i => P (v i))
      simp only [Finset.card_univ, Fintype.card_fin] at hpart
      have hgb : (Finset.univ.filter fun i => P (v i)).card ≤
          (Finset.univ.filter fun i => ¬ P (v i)).card := by omega
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hgb
      rw [hd, pow_add, ← mul_assoc, ← mul_pow]
      norm_num
      exact one_le_pow₀ (by norm_num)

namespace Prog

variable {Q : Type}

theorem exp_add {α : Type} (O : Oracle Q) (m : Prog Q α) (f g : α → ℝ) :
    m.exp O (fun a => f a + g a) = m.exp O f + m.exp O g := by
  induction m with
  | ret a => rfl
  | query x k ih => simp only [exp, ih, mul_add, Finset.sum_add_distrib]
  | choose p k ih => simp only [exp, ih, mul_add, Finset.sum_add_distrib]
  | work c m ih => exact ih

/-- Independence of repetitions: the expectation of a product of per-run
factors is the power of the single-run expectation. -/
theorem exp_replicate_prod {Ω : Type} (O : Oracle Q) (m : Prog Q Ω) (h : Ω → ℝ) (k : ℕ) :
    (m.replicate k).exp O (fun xs => ∏ i, h (samplesToFn k xs i)) = (m.exp O h) ^ k := by
  induction k with
  | zero =>
    change (∏ i : Fin 0, h (samplesToFn 0 () i)) = _
    simp
  | succ k ih =>
    change (m.bind fun x => (m.replicate k).bind fun xs => Prog.ret (x, xs)).exp O
      (fun xs : Ω × Samples Ω k =>
        ∏ i : Fin (k + 1), h ((Fin.cons xs.1 (samplesToFn k xs.2) : Fin (k + 1) → Ω) i)) = _
    rw [exp_bind]
    have hinner : ∀ x, ((m.replicate k).bind fun xs => Prog.ret (x, xs)).exp O
        (fun xs : Ω × Samples Ω k =>
          ∏ i : Fin (k + 1), h ((Fin.cons xs.1 (samplesToFn k xs.2) : Fin (k + 1) → Ω) i)) =
        (m.exp O h) ^ k * h x := by
      intro x
      rw [exp_bind]
      simp only [exp, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [exp_mul_left, ih, mul_comm]
    simp_rw [hinner]
    rw [exp_mul_left, pow_succ]

/-- Run a real-valued program `k` times independently and return the median. -/
def medianOf (m : Prog Q ℝ) (k : ℕ) : Prog Q ℝ :=
  (m.replicate k).bind fun xs => .ret (median (samplesToFn k xs))

theorem medianOf_queryBound {m : Prog Q ℝ} {T : ℕ} (h : QueryBound m T) (k : ℕ) :
    QueryBound (m.medianOf k) (k * T) := by
  have hb := (h.replicate k).bind
    (g := fun xs => Prog.ret (median (samplesToFn k xs))) (b := 0) fun xs => .ret _ _
  unfold medianOf
  simpa using hb

/-- Confidence amplification for a program: failure at most 1/4 becomes at
most `(7/8)^k`. Every run makes its own oracle calls. -/
theorem medianOf_failure (O : Oracle Q) (m : Prog Q ℝ) (k : ℕ) {P : ℝ → Prop}
    (hP : ∀ a b c, P a → P c → a ≤ b → b ≤ c → P b)
    (hfail : m.exp O (fun z => if P z then 0 else 1) ≤ 1 / 4) :
    (m.medianOf k).exp O (fun z => if P z then 0 else 1) ≤ (7 / 8 : ℝ) ^ k := by
  let h : ℝ → ℝ := fun z => if P z then 1 / 2 else 2
  have hsplit : h = fun z => (1 / 2 : ℝ) + (3 / 2) * (if P z then 0 else 1) := by
    ext z
    simp only [h]
    split_ifs <;> norm_num
  have hmean : m.exp O h ≤ 7 / 8 := by
    rw [hsplit, exp_add, exp_const, exp_mul_left]
    linarith
  have hmean0 : 0 ≤ m.exp O h := exp_nonneg O m fun z => by
    simp only [h]
    split_ifs <;> norm_num
  calc (m.medianOf k).exp O (fun z => if P z then 0 else 1)
      = (m.replicate k).exp O
          (fun xs => if P (median (samplesToFn k xs)) then (0 : ℝ) else 1) := by
        unfold medianOf
        rw [exp_bind]
        rfl
    _ ≤ (m.replicate k).exp O (fun xs => ∏ i, h (samplesToFn k xs i)) :=
        exp_mono O _ fun xs => median_indicator_le _ hP
    _ = (m.exp O h) ^ k := exp_replicate_prod O m h k
    _ ≤ (7 / 8 : ℝ) ^ k := pow_le_pow_left₀ hmean0 hmean k

end Prog

/-- Number of independent runs for failure probability `δ`: logarithmic in `1/δ`. -/
def confidenceRuns (δ : ℝ) : ℕ := 6 * Nat.clog 2 ⌈1 / δ⌉₊

theorem confidenceRuns_bound {δ : ℝ} (hδ : 0 < δ) : (7 / 8 : ℝ) ^ confidenceRuns δ ≤ δ := by
  unfold confidenceRuns
  have h1 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ⌈1 / δ⌉₊ ≤ 2 ^ Nat.clog 2 ⌈1 / δ⌉₊ := Nat.le_pow_clog (by norm_num) _
  have h2' : (⌈1 / δ⌉₊ : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 ⌈1 / δ⌉₊ := by exact_mod_cast h2
  have hpow : (7 / 8 : ℝ) ^ (6 * Nat.clog 2 ⌈1 / δ⌉₊) ≤ (1 / 2) ^ Nat.clog 2 ⌈1 / δ⌉₊ := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hpos : (0 : ℝ) < (2 : ℝ) ^ Nat.clog 2 ⌈1 / δ⌉₊ := by positivity
  have h3 : 1 / δ ≤ (2 : ℝ) ^ Nat.clog 2 ⌈1 / δ⌉₊ := h1.trans h2'
  calc (7 / 8 : ℝ) ^ (6 * Nat.clog 2 ⌈1 / δ⌉₊) ≤ (1 / 2) ^ Nat.clog 2 ⌈1 / δ⌉₊ := hpow
    _ = 1 / (2 : ℝ) ^ Nat.clog 2 ⌈1 / δ⌉₊ := by rw [div_pow, one_pow]
    _ ≤ δ := by
      rw [div_le_iff₀ hpos]
      rw [div_le_iff₀ hδ] at h3
      linarith

namespace Digraph

variable {V E : Type} [Fintype E] [DecidableEq E] (G : Digraph V E) (p : E → ℝ)

/-- **The reduction at arbitrary confidence.** Under the constant-confidence
oracle contract of `cycle_fpras_of_constant_confidence`, the median of
`confidenceRuns δ` independent runs of the algorithm has relative error more
than `ε` with probability at most `δ`. It makes at most
`confidenceRuns δ * T` amplified oracle queries, `T = m + 2*m*n`. -/
theorem cycle_fpras_confidence (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (O : Oracle (Query V E)) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hO : ∀ x, G.Valid p x →
      (∑ s, if G.Accurate (ε / (128 * Fintype.card E * (Fintype.card E + 1))) x (O.answer x s)
        then 0 else (O.law x).value s) ≤ 1 / 4) :
    ((G.cycleAlgorithm p (bitBudget (Fintype.card E) ε)
        (reductionBudget (Fintype.card E) ε)).medianOf (confidenceRuns δ)).exp
        (O.amplify (amplifyRounds (Fintype.card E +
          reductionBudget (Fintype.card E) ε * (2 * Fintype.card E))))
        (fun z =>
          if ε * G.cycleMass (edgeLaw p hp0 hp1).toMass <
            |z - G.cycleMass (edgeLaw p hp0 hp1).toMass| then 1 else 0) ≤ δ := by
  set Z := G.cycleMass (edgeLaw p hp0 hp1).toMass with hZ
  have hZ0 : 0 ≤ Z := by
    rw [hZ, G.cycleMass_eq_unionMass]
    exact Mass.unionMass_nonneg _ G.event
  have hind : (fun z : ℝ => if ε * Z < |z - Z| then (1 : ℝ) else 0) =
      fun z => if |z - Z| ≤ ε * Z then 0 else 1 := by
    ext z
    by_cases h : ε * Z < |z - Z|
    · rw [ite_eq_left h, ite_eq_right (not_le.mpr h)]
    · rw [ite_eq_right h, ite_eq_left (not_lt.mp h)]
  have hsingle := G.cycle_fpras_of_constant_confidence p hp0 hp1 O hε hε1 hO
  rw [← hZ, hind] at hsingle
  rw [hind]
  refine le_trans (Prog.medianOf_failure _ _ _ ?_ hsingle) (confidenceRuns_bound hδ)
  intro a b c ha hc hab hbc
  rw [abs_le] at *
  exact ⟨by linarith [ha.1], by linarith [hc.2]⟩

end Digraph
end
end DirectedCycleFPRAS
