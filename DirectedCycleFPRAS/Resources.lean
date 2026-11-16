module

public import DirectedCycleFPRAS.Reliability
public import DirectedCycleFPRAS.RandomBits

@[expose] public section

/-! Resource predicates and rational height arithmetic shared by the reduction
and the concrete reliability oracle. -/

namespace DirectedCycleFPRAS

open scoped BigOperators Nat
open Classical

noncomputable section

namespace Prog

variable {Q α β : Type}

/-- At most the stated number of charged local operations on every path. -/
inductive WorkBound : Prog Q α → ℕ → Prop
  | ret (a : α) (n : ℕ) : WorkBound (.ret a) n
  | query (x : Q) (k : ℝ → Prog Q α) (n : ℕ) :
      (∀ r, WorkBound (k r) n) → WorkBound (.query x k) n
  | choose {ι : Type} [Fintype ι] (p : Law ι) (k : ι → Prog Q α) (n : ℕ) :
      (∀ i, WorkBound (k i) n) → WorkBound (.choose p k) n
  | work (c : ℕ) (m : Prog Q α) (n : ℕ) : WorkBound m n → WorkBound (.work c m) (c + n)

theorem WorkBound.mono {m : Prog Q α} {a b : ℕ} (h : WorkBound m a) (hab : a ≤ b) :
    WorkBound m b := by
  induction h generalizing b with
  | ret a n => exact .ret a b
  | query x k n _ ih => exact .query x k b fun r => ih r hab
  | choose p k n _ ih => exact .choose p k b fun i => ih i hab
  | work c m n _ ih =>
    obtain ⟨b', rfl⟩ : ∃ b', b = c + b' := ⟨b - c, by omega⟩
    exact .work c m b' (ih (by omega))

theorem WorkBound.bind {m : Prog Q α} {g : α → Prog Q β} {a b : ℕ}
    (hm : WorkBound m a) (hg : ∀ x, WorkBound (g x) b) : WorkBound (m.bind g) (a + b) := by
  induction hm with
  | ret x n => exact (hg x).mono (by omega)
  | query x k n _ ih => exact .query x _ _ ih
  | choose p k n _ ih => exact .choose p _ _ ih
  | work c m n _ ih =>
    rw [Nat.add_assoc]
    exact .work c _ _ ih

theorem WorkBound.guarded {c : Prop} {x : Q} {k : ℝ → Prog Q α} {n : ℕ}
    (h : ∀ r, WorkBound (k r) n) : WorkBound (Prog.guarded c x k) (1 + n) := by
  unfold Prog.guarded
  refine .work _ _ _ ?_
  split_ifs
  · exact .query x k n h
  · exact h 0

theorem WorkBound.draw {ι : Type} [Fintype ι] {b : ℕ} {p : Law ι} {k : ι → Prog Q α} {n : ℕ}
    (h : ∀ i, WorkBound (k i) n) : WorkBound (Prog.draw b p k) (Fintype.card ι + n) :=
  .work _ _ _ (.choose _ _ _ fun u => h (decode b p u))

theorem WorkBound.replicate {Ω : Type} {m : Prog Q Ω} {a : ℕ} (h : WorkBound m a) (n : ℕ) :
    WorkBound (m.replicate n) (n * a) := by
  induction n with
  | zero => exact .ret _ _
  | succ n ih =>
    have hb : WorkBound (m.replicate (n + 1)) (a + (n * a + 0)) :=
      h.bind fun x => ih.bind fun xs => .ret _ 0
    exact hb.mono (by rw [Nat.succ_mul]; omega)

/-- On every path whose oracle answers satisfy `A`, every query asked
satisfies `Qp` and the result satisfies `R`. -/
inductive Sat (A : ℝ → Prop) (Qp : Q → Prop) (R : α → Prop) : Prog Q α → Prop
  | ret (a : α) : R a → Sat A Qp R (.ret a)
  | query (x : Q) (k : ℝ → Prog Q α) :
      Qp x → (∀ r, A r → Sat A Qp R (k r)) → Sat A Qp R (.query x k)
  | choose {ι : Type} [Fintype ι] (p : Law ι) (k : ι → Prog Q α) :
      (∀ i, Sat A Qp R (k i)) → Sat A Qp R (.choose p k)
  | work (c : ℕ) (m : Prog Q α) : Sat A Qp R m → Sat A Qp R (.work c m)

variable {A : ℝ → Prop} {Qp : Q → Prop}

theorem Sat.bind {R' : α → Prop} {R : β → Prop} {m : Prog Q α} {g : α → Prog Q β}
    (hm : Sat A Qp R' m) (hg : ∀ a, R' a → Sat A Qp R (g a)) : Sat A Qp R (m.bind g) := by
  induction hm with
  | ret a ha => exact hg a ha
  | query x k hx _ ih => exact .query x _ hx ih
  | choose p k _ ih => exact .choose p _ ih
  | work c m _ ih => exact .work c _ ih

theorem Sat.guarded {R : α → Prop} {c : Prop} {x : Q} {k : ℝ → Prog Q α}
    (hx : c → Qp x) (h0 : A 0) (h : ∀ r, A r → Sat A Qp R (k r)) :
    Sat A Qp R (Prog.guarded c x k) := by
  unfold Prog.guarded
  refine .work _ _ ?_
  split_ifs with hc
  · exact .query x k (hx hc) h
  · exact h 0 h0

theorem Sat.draw {R : α → Prop} {ι : Type} [Fintype ι] {b : ℕ} {p : Law ι}
    {k : ι → Prog Q α} (h : ∀ i, Sat A Qp R (k i)) : Sat A Qp R (Prog.draw b p k) :=
  .work _ _ (.choose _ _ fun u => h (decode b p u))

theorem Sat.replicate {Ω : Type} {m : Prog Q Ω} (h : Sat A Qp (fun _ => True) m) (n : ℕ) :
    Sat A Qp (fun _ => True) (m.replicate n) := by
  induction n with
  | zero => exact .ret _ trivial
  | succ n ih => exact h.bind fun x _ => ih.bind fun xs _ => .ret _ trivial

end Prog

/-! ## Rational numbers of bounded size -/

/-- `x` is a fraction whose numerator, in absolute value, and denominator are
at most `H`. Its binary description has about `2 * log₂ H` bits. -/
def Height (H : ℕ) (x : ℝ) : Prop :=
  ∃ (a : ℤ) (d : ℕ), 0 < d ∧ x = a / d ∧ a.natAbs ≤ H ∧ d ≤ H

theorem Height.mono {H H' : ℕ} {x : ℝ} (h : Height H x) (hH : H ≤ H') : Height H' x := by
  obtain ⟨a, d, hd, hx, ha, hdH⟩ := h
  exact ⟨a, d, hd, hx, ha.trans hH, hdH.trans hH⟩

theorem height_zero {H : ℕ} (hH : 1 ≤ H) : Height H 0 :=
  ⟨0, 1, one_pos, by simp, by simp, hH⟩

theorem height_one {H : ℕ} (hH : 1 ≤ H) : Height H 1 :=
  ⟨1, 1, one_pos, by simp, by simpa using hH, hH⟩

theorem Height.mul {H₁ H₂ : ℕ} {x y : ℝ} (hx : Height H₁ x) (hy : Height H₂ y) :
    Height (H₁ * H₂) (x * y) := by
  obtain ⟨a, d, hd, rfl, ha, hdH⟩ := hx
  obtain ⟨a', d', hd', rfl, ha', hdH'⟩ := hy
  refine ⟨a * a', d * d', Nat.mul_pos hd hd', ?_, ?_, Nat.mul_le_mul hdH hdH'⟩
  · push_cast
    rw [div_mul_div_comm]
  · rw [Int.natAbs_mul]
    exact Nat.mul_le_mul ha ha'

theorem Height.add {H₁ H₂ : ℕ} {x y : ℝ} (hx : Height H₁ x) (hy : Height H₂ y) :
    Height (2 * (H₁ * H₂)) (x + y) := by
  obtain ⟨a, d, hd, rfl, ha, hdH⟩ := hx
  obtain ⟨a', d', hd', rfl, ha', hdH'⟩ := hy
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdR' : (d' : ℝ) ≠ 0 := by exact_mod_cast hd'.ne'
  refine ⟨a * d' + a' * d, d * d', Nat.mul_pos hd hd', ?_, ?_, ?_⟩
  · push_cast
    field_simp
  · have h1 : (a * d' + a' * d).natAbs ≤ a.natAbs * d' + a'.natAbs * d := by
      refine (Int.natAbs_add_le _ _).trans ?_
      simp [Int.natAbs_mul]
    have h2 := Nat.mul_le_mul ha hdH'
    have h3 := Nat.mul_le_mul ha' hdH
    nlinarith
  · have := Nat.mul_le_mul hdH hdH'
    omega

theorem Height.one_sub {H : ℕ} {x : ℝ} (hx : Height H x) : Height (2 * H) (1 - x) := by
  obtain ⟨a, d, hd, rfl, ha, hdH⟩ := hx
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  refine ⟨d - a, d, hd, ?_, ?_, by omega⟩
  · push_cast
    field_simp
  · have h := Int.natAbs_sub_le (d : ℤ) a
    simp only [Int.natAbs_natCast] at h
    omega

/-- A sum of `k` fractions of size `H` has size at most `(2H)^k`. -/
theorem height_sum {ι : Type} (s : Finset ι) (f : ι → ℝ) {H : ℕ}
    (hf : ∀ i ∈ s, Height H (f i)) : Height ((2 * H) ^ s.card) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using height_zero (le_refl 1)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    have h1 := hf i (Finset.mem_insert_self i s)
    have h2 := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    refine (h1.add h2).mono (le_of_eq ?_)
    ring

/-! ## Selection without division -/

/-- For normalised weights, deciding which alternative a `b`-bit integer
selects needs only partial sums of the weights, one multiplication by the
total and comparisons: no division is performed. -/
theorem hit_normLaw_iff {ι : Type} [Fintype ι] (b : ℕ) (w : ι → ℝ) (d : ι)
    (h0 : ∀ i, 0 ≤ w i) (hpos : 0 < ∑ i, w i) (u : ℕ) (i : ι) :
    Hit b (normLaw w d) u i ↔
      (2 : ℝ) ^ b * (∑ j, if position j < position i then w j else 0) ≤ u * ∑ j, w j ∧
      (u : ℝ) * ∑ j, w j <
        (2 : ℝ) ^ b * (∑ j, if position j < position i + 1 then w j else 0) := by
  have hcum : ∀ n, cumulative (normLaw w d) n =
      (∑ j, if position j < n then w j else 0) / ∑ j, w j := by
    intro n
    unfold cumulative
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [normLaw_value w d h0 hpos]
    split_ifs
    · rfl
    · simp
  unfold Hit
  rw [hcum, hcum, ← mul_div_assoc, ← mul_div_assoc, div_le_iff₀ hpos, lt_div_iff₀ hpos]

/-! ## Averages with a common denominator -/

/-- The sum of `n` values with common denominator `F` has numerator at most `n * F`. -/
theorem sampleSum_common_denominator {Ω : Type} (f : Ω → ℝ) (F : ℕ)
    (hf : ∀ x, ∃ c : ℕ, c ≤ F ∧ f x = (c : ℝ) / F) (n : ℕ) (xs : Samples Ω n) :
    ∃ C : ℕ, C ≤ n * F ∧ Law.sampleSum f n xs = (C : ℝ) / F := by
  induction n with
  | zero => exact ⟨0, by simp, by simp [Law.sampleSum]⟩
  | succ n ih =>
    obtain ⟨c, hc, hfc⟩ := hf xs.1
    obtain ⟨C, hC, hsum⟩ := ih xs.2
    refine ⟨c + C, by rw [Nat.succ_mul]; omega, ?_⟩
    change f xs.1 + Law.sampleSum f n xs.2 = _
    rw [hfc, hsum]
    push_cast
    ring


end
end DirectedCycleFPRAS
