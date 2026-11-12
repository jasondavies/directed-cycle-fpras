module

public import DirectedCycleFPRAS.OracleProgram

@[expose] public section

/-!
# Median amplification of a randomized oracle

An oracle whose answer lies in an interval with probability at least 3/4 is
amplified by taking the median of `k` independent runs. The amplified oracle
fails with probability at most `(7/8)^k`, by an exponential-moment bound
carried out on the explicit finite product law of the `k` seeds.
-/

namespace DirectedCycleFPRAS

open scoped BigOperators
open Classical

noncomputable section

/-- The law of `k` independent draws. -/
def Law.pow {S : Type} [Fintype S] (ρ : Law S) (k : ℕ) : Law (Fin k → S) where
  value s := ∏ i, ρ.value (s i)
  nonneg s := Finset.prod_nonneg fun i _ => ρ.nonneg (s i)
  sum_one := by
    rw [← Fintype.prod_sum (fun (_ : Fin k) (x : S) => ρ.value x)]
    simp [ρ.sum_one]

/-- Independence: the expectation of a product of per-draw factors is the
power of the single-draw expectation. -/
theorem Law.pow_prod {S : Type} [Fintype S] (ρ : Law S) (k : ℕ) (h : S → ℝ) :
    (∑ s : Fin k → S, (ρ.pow k).value s * ∏ i, h (s i)) = (∑ x, ρ.value x * h x) ^ k := by
  have hmul : ∀ s : Fin k → S,
      (ρ.pow k).value s * ∏ i, h (s i) = ∏ i, ρ.value (s i) * h (s i) := by
    intro s
    change (∏ i, ρ.value (s i)) * ∏ i, h (s i) = _
    rw [Finset.prod_mul_distrib]
  simp_rw [hmul]
  rw [← Fintype.prod_sum (fun (_ : Fin k) (x : S) => ρ.value x * h x)]
  simp

/-- At most half of the entries lie strictly on either side of `m`. -/
def IsMedian {k : ℕ} (v : Fin k → ℝ) (m : ℝ) : Prop :=
  2 * (Finset.univ.filter fun i => v i < m).card ≤ k ∧
    2 * (Finset.univ.filter fun i => m < v i).card ≤ k

theorem exists_median {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) : ∃ m, IsMedian v m := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let c : ℝ → ℕ := fun r => (Finset.univ.filter fun i => v i ≤ r).card
  let S : Finset ℝ := Finset.univ.image v
  have hS : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  let T : Finset ℝ := S.filter fun r => k < 2 * c r
  have hT : T.Nonempty := by
    refine ⟨S.max' hS, Finset.mem_filter.mpr ⟨Finset.max'_mem S hS, ?_⟩⟩
    have hall : (Finset.univ.filter fun i => v i ≤ S.max' hS) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      exact Finset.le_max' S (v i) (Finset.mem_image_of_mem v (Finset.mem_univ i))
    simp only [c, hall, Finset.card_univ, Fintype.card_fin]
    omega
  refine ⟨T.min' hT, ?_, ?_⟩
  · by_contra hcon
    have hlt : k < 2 * (Finset.univ.filter fun i => v i < T.min' hT).card := not_le.mp hcon
    have hne : (Finset.univ.filter fun i => v i < T.min' hT).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨i₀, hi₀⟩ := hne
    have hi₀' : v i₀ < T.min' hT := (Finset.mem_filter.mp hi₀).2
    let S' : Finset ℝ := S.filter fun r => r < T.min' hT
    have hS' : S'.Nonempty :=
      ⟨v i₀, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem v (Finset.mem_univ _), hi₀'⟩⟩
    have hr' := Finset.max'_mem S' hS'
    have hr'S : S'.max' hS' ∈ S := (Finset.mem_filter.mp hr').1
    have hr'lt : S'.max' hS' < T.min' hT := (Finset.mem_filter.mp hr').2
    have hsub : (Finset.univ.filter fun i => v i < T.min' hT) ⊆
        (Finset.univ.filter fun i => v i ≤ S'.max' hS') := by
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Finset.le_max' S' (v i)
        (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem v (Finset.mem_univ i), hi'⟩)⟩
    have hcard := Finset.card_le_card hsub
    have hmemT : S'.max' hS' ∈ T :=
      Finset.mem_filter.mpr ⟨hr'S, lt_of_lt_of_le hlt (Nat.mul_le_mul_left 2 hcard)⟩
    exact absurd (Finset.min'_le T _ hmemT) (not_le.mpr hr'lt)
  · have hmem := Finset.min'_mem T hT
    have hc : k < 2 * (Finset.univ.filter fun i => v i ≤ T.min' hT).card :=
      (Finset.mem_filter.mp hmem).2
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin k))) (fun i => v i ≤ T.min' hT)
    simp only [not_le, Finset.card_univ, Fintype.card_fin] at hpart
    omega

/-- Some median of the entries, selected by its characterising property; for an
even number of entries any point between the two middle values may be chosen.
With no entries every real is a median and the value is irrelevant. -/
def median {k : ℕ} (v : Fin k → ℝ) : ℝ :=
  if h : ∃ m, IsMedian v m then Classical.choose h else 0

theorem median_isMedian {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) : IsMedian v (median v) := by
  have hex := exists_median hk v
  unfold median
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

/-- If a strict majority of the entries satisfy an interval property, so does
the median. -/
theorem median_good {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) {P : ℝ → Prop}
    (hP : ∀ a b c, P a → P c → a ≤ b → b ≤ c → P b)
    (hmaj : k < 2 * (Finset.univ.filter fun i => P (v i)).card) : P (median v) := by
  obtain ⟨hlo, hhi⟩ := median_isMedian hk v
  have h1 : ∃ i, P (v i) ∧ v i ≤ median v := by
    by_contra hcon
    have hsub : (Finset.univ.filter fun i => P (v i)) ⊆
        (Finset.univ.filter fun i => median v < v i) := by
      intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      by_contra hle
      exact hcon ⟨i, (Finset.mem_filter.mp hi).2, not_lt.mp hle⟩
    have := Finset.card_le_card hsub
    omega
  have h2 : ∃ j, P (v j) ∧ median v ≤ v j := by
    by_contra hcon
    have hsub : (Finset.univ.filter fun i => P (v i)) ⊆
        (Finset.univ.filter fun i => v i < median v) := by
      intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      by_contra hle
      exact hcon ⟨i, (Finset.mem_filter.mp hi).2, not_lt.mp hle⟩
    have := Finset.card_le_card hsub
    omega
  obtain ⟨i, hPi, hi⟩ := h1
  obtain ⟨j, hPj, hj⟩ := h2
  exact hP _ _ _ hPi hPj hi hj

/-- Answer with the median of `k` independent runs of the oracle. -/
def Oracle.amplify {Q : Type} (O : Oracle Q) (k : ℕ) : Oracle Q where
  Seed := Fin k → O.Seed
  fintype := inferInstance
  law x := (O.law x).pow k
  answer x s := median fun i => O.answer x (s i)

/-- Median amplification: per-call failure probability at most 1/4 becomes at
most `(7/8)^k`. The acceptable answers must form an interval. -/
theorem Oracle.amplify_failure {Q : Type} (O : Oracle Q) (k : ℕ) (x : Q) {P : ℝ → Prop}
    (hP : ∀ a b c, P a → P c → a ≤ b → b ≤ c → P b)
    (hfail : (∑ s, if P (O.answer x s) then 0 else (O.law x).value s) ≤ 1 / 4) :
    (∑ s, if P ((O.amplify k).answer x s) then 0 else ((O.amplify k).law x).value s) ≤
      (7 / 8 : ℝ) ^ k := by
  change (∑ s : Fin k → O.Seed, if P (median fun i => O.answer x (s i)) then 0
    else ((O.law x).pow k).value s) ≤ _
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    calc _ ≤ ∑ s : Fin 0 → O.Seed, ((O.law x).pow 0).value s :=
          Finset.sum_le_sum fun s _ => by
            split_ifs
            · exact ((O.law x).pow 0).nonneg s
            · exact le_refl _
      _ = 1 := ((O.law x).pow 0).sum_one
      _ = (7 / 8 : ℝ) ^ 0 := (pow_zero _).symm
  let h : O.Seed → ℝ := fun t => if P (O.answer x t) then 1 / 2 else 2
  have hh0 : ∀ t, 0 ≤ h t := by
    intro t
    simp only [h]
    split_ifs <;> norm_num
  have hterm : ∀ s : Fin k → O.Seed,
      (if P (median fun i => O.answer x (s i)) then 0 else ((O.law x).pow k).value s) ≤
        ((O.law x).pow k).value s * ∏ i, h (s i) := by
    intro s
    have hv := ((O.law x).pow k).nonneg s
    have hprod0 : 0 ≤ ∏ i, h (s i) := Finset.prod_nonneg fun i _ => hh0 (s i)
    split_ifs with hm
    · exact mul_nonneg hv hprod0
    · have hmaj : ¬ k < 2 * (Finset.univ.filter fun i => P (O.answer x (s i))).card :=
        fun hlt => hm (median_good hk _ hP hlt)
      have hone : 1 ≤ ∏ i, h (s i) := by
        simp only [h]
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
        have hpart := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin k))) (fun i => P (O.answer x (s i)))
        simp only [Finset.card_univ, Fintype.card_fin] at hpart
        have hgb : (Finset.univ.filter fun i => P (O.answer x (s i))).card ≤
            (Finset.univ.filter fun i => ¬ P (O.answer x (s i))).card := by omega
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hgb
        rw [hd, pow_add, ← mul_assoc, ← mul_pow]
        norm_num
        exact one_le_pow₀ (by norm_num)
      calc ((O.law x).pow k).value s = ((O.law x).pow k).value s * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hone hv
  calc _ ≤ ∑ s : Fin k → O.Seed, ((O.law x).pow k).value s * ∏ i, h (s i) :=
        Finset.sum_le_sum fun s _ => hterm s
    _ = (∑ t, (O.law x).value t * h t) ^ k := Law.pow_prod _ _ _
    _ ≤ (7 / 8 : ℝ) ^ k := by
      apply pow_le_pow_left₀
      · exact Finset.sum_nonneg fun t _ => mul_nonneg ((O.law x).nonneg t) (hh0 t)
      · have hsplit : ∀ t, (O.law x).value t * h t = (1 / 2) * (O.law x).value t +
            (3 / 2) * (if P (O.answer x t) then 0 else (O.law x).value t) := by
          intro t
          simp only [h]
          split_ifs <;> ring
        simp_rw [hsplit]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Law.sum_one]
        linarith

/-- A logarithmic number of repetitions suffices for `T` calls. -/
def amplifyRounds (T : ℕ) : ℕ := 6 * Nat.clog 2 (8 * T)

theorem amplifyRounds_bound (T : ℕ) :
    (T : ℝ) * (7 / 8 : ℝ) ^ amplifyRounds T ≤ 1 / 8 := by
  unfold amplifyRounds
  have h8 : 8 * T ≤ 2 ^ Nat.clog 2 (8 * T) := Nat.le_pow_clog (by norm_num) _
  have h8' : (8 : ℝ) * T ≤ 2 ^ Nat.clog 2 (8 * T) := by exact_mod_cast h8
  have hpow : (7 / 8 : ℝ) ^ (6 * Nat.clog 2 (8 * T)) ≤ (1 / 2) ^ Nat.clog 2 (8 * T) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hpos : (0 : ℝ) < 2 ^ Nat.clog 2 (8 * T) := by positivity
  calc (T : ℝ) * (7 / 8 : ℝ) ^ (6 * Nat.clog 2 (8 * T))
      ≤ T * (1 / 2) ^ Nat.clog 2 (8 * T) := mul_le_mul_of_nonneg_left hpow hT0
    _ = T / 2 ^ Nat.clog 2 (8 * T) := by rw [one_div, inv_pow, div_eq_mul_inv]
    _ ≤ 1 / 8 := by
      rw [div_le_iff₀ hpos]
      linarith

end
end DirectedCycleFPRAS
