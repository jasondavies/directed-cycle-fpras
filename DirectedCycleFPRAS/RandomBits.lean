module

public import DirectedCycleFPRAS.OracleProgram

@[expose] public section

/-!
# Discrete choices from a fixed budget of uniform random bits

A choice among finitely many alternatives with arbitrary real probabilities is
implemented by drawing a uniform `b`-bit integer `u` and selecting the
alternative whose cumulative-probability interval contains `u / 2^b`. The
induced law `bitLaw` differs from the intended one by at most `2^(-b)` on
every alternative, so by at most `k / 2^b` in L1 for `k` alternatives.

`Prog.BitBound` records that every internal random choice of a program is such
a uniform `b`-bit draw, and bounds their number on every execution path.
-/

namespace DirectedCycleFPRAS

open scoped BigOperators
open Classical

noncomputable section

/-- The uniform law on `b`-bit integers. -/
def uniformLaw (b : ℕ) : Law (Fin (2 ^ b)) where
  value _ := 1 / (2 : ℝ) ^ b
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp

section Decode

variable {ι : Type} [Fintype ι]

/-- Position of an alternative in a fixed enumeration. -/
def position (i : ι) : ℕ := (Fintype.equivFin ι i : ℕ)

theorem position_lt (i : ι) : position i < Fintype.card ι := (Fintype.equivFin ι i).isLt

theorem position_injective : Function.Injective (position : ι → ℕ) :=
  fun _ _ h => (Fintype.equivFin ι).injective (Fin.ext h)

theorem exists_position {n : ℕ} (h : n < Fintype.card ι) : ∃ i : ι, position i = n :=
  ⟨(Fintype.equivFin ι).symm ⟨n, h⟩, by simp [position]⟩

/-- Total probability of the alternatives before position `n`. -/
def cumulative (p : Law ι) (n : ℕ) : ℝ := ∑ j, if position j < n then p.value j else 0

theorem cumulative_zero (p : Law ι) : cumulative p 0 = 0 := by simp [cumulative]

theorem cumulative_mono (p : Law ι) {n n' : ℕ} (h : n ≤ n') :
    cumulative p n ≤ cumulative p n' := by
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : position j < n
  · rw [ite_eq_left hj, ite_eq_left (lt_of_lt_of_le hj h)]
  · rw [ite_eq_right hj]
    split_ifs
    · exact p.nonneg j
    · exact le_refl _

theorem cumulative_nonneg (p : Law ι) (n : ℕ) : 0 ≤ cumulative p n := by
  rw [← cumulative_zero p]
  exact cumulative_mono p (Nat.zero_le n)

theorem cumulative_card (p : Law ι) : cumulative p (Fintype.card ι) = 1 := by
  rw [← p.sum_one]
  apply Finset.sum_congr rfl
  intro j _
  rw [ite_eq_left (position_lt j)]

theorem cumulative_le_one (p : Law ι) (n : ℕ) : cumulative p n ≤ 1 := by
  rw [← p.sum_one]
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_refl _
  · exact p.nonneg j

theorem cumulative_succ (p : Law ι) (i : ι) :
    cumulative p (position i + 1) = cumulative p (position i) + p.value i := by
  unfold cumulative
  have hterm : ∀ j, (if position j < position i + 1 then p.value j else 0) =
      (if position j < position i then p.value j else 0) + (if j = i then p.value i else 0) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp
    · have hne : position j ≠ position i := fun h => hji (position_injective h)
      rw [ite_eq_right hji, add_zero]
      by_cases hlt : position j < position i
      · rw [ite_eq_left hlt, ite_eq_left (by omega)]
      · rw [ite_eq_right hlt, ite_eq_right (by omega)]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp

/-- The integer `u` falls in the scaled cumulative interval of alternative `i`. -/
def Hit (b : ℕ) (p : Law ι) (u : ℕ) (i : ι) : Prop :=
  (2 : ℝ) ^ b * cumulative p (position i) ≤ u ∧
    (u : ℝ) < (2 : ℝ) ^ b * cumulative p (position i + 1)

theorem card_pos_of_law (p : Law ι) : 0 < Fintype.card ι := by
  by_contra h
  have hE : IsEmpty ι := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h)
  have hs := p.sum_one
  simp at hs

theorem exists_hit (b : ℕ) (p : Law ι) {u : ℕ} (hu : u < 2 ^ b) : ∃ i, Hit b p u i := by
  have hc := card_pos_of_law p
  have huR : (u : ℝ) < (2 : ℝ) ^ b := by exact_mod_cast hu
  have hlast : (u : ℝ) < (2 : ℝ) ^ b * cumulative p (Fintype.card ι - 1 + 1) := by
    rw [Nat.sub_add_cancel hc, cumulative_card, mul_one]
    exact huR
  have hex : ∃ n, (u : ℝ) < (2 : ℝ) ^ b * cumulative p (n + 1) := ⟨_, hlast⟩
  have hfind := Nat.find_spec hex
  have hle : Nat.find hex ≤ Fintype.card ι - 1 := Nat.find_min' hex hlast
  obtain ⟨i, hi⟩ := exists_position (ι := ι) (n := Nat.find hex) (by omega)
  refine ⟨i, ?_, by rw [hi]; exact hfind⟩
  rw [hi]
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, cumulative_zero, mul_zero]
    exact Nat.cast_nonneg u
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    rw [Nat.sub_add_cancel hpos] at hmin
    exact not_lt.mp hmin

theorem hit_unique {b : ℕ} {p : Law ι} {u : ℕ} {i i' : ι}
    (h : Hit b p u i) (h' : Hit b p u i') : i = i' := by
  apply position_injective
  by_contra hne
  have key : ∀ {a c : ι}, Hit b p u a → Hit b p u c → position a < position c → False := by
    intro a c ha hc hlt
    have hmono := cumulative_mono p (show position a + 1 ≤ position c by omega)
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ b := by positivity
    have := mul_le_mul_of_nonneg_left hmono h2
    linarith [ha.2, hc.1]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact key h h' hlt
  · exact key h' h hgt

/-- The alternative selected by the `b`-bit integer `u`. -/
def decode (b : ℕ) (p : Law ι) (u : Fin (2 ^ b)) : ι :=
  Classical.choose (exists_hit b p u.isLt)

theorem decode_eq_iff (b : ℕ) (p : Law ι) (u : Fin (2 ^ b)) (i : ι) :
    decode b p u = i ↔ Hit b p u i := by
  have hspec := Classical.choose_spec (exists_hit b p u.isLt)
  constructor
  · rintro rfl
    exact hspec
  · intro h
    exact hit_unique hspec h

/-- The law of the alternative decoded from a uniform `b`-bit integer. -/
def bitLaw (b : ℕ) (p : Law ι) : Law ι where
  value i := ∑ u, (uniformLaw b).value u * (if decode b p u = i then 1 else 0)
  nonneg i := Finset.sum_nonneg fun u _ =>
    mul_nonneg ((uniformLaw b).nonneg u) (by split_ifs <;> norm_num)
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_one]
    exact (uniformLaw b).sum_one

/-- Integers in a real interval, counted by ceilings. -/
theorem count_interval (N : ℕ) {A C : ℝ} (hC : C ≤ N) :
    (∑ u : Fin N, if A ≤ ((u : ℕ) : ℝ) ∧ ((u : ℕ) : ℝ) < C then (1 : ℝ) else 0) =
      ((⌈C⌉₊ - ⌈A⌉₊ : ℕ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => if A ≤ (n : ℝ) ∧ (n : ℝ) < C then (1 : ℝ) else 0) N]
  rw [Finset.sum_boole]
  congr 1
  rw [← Nat.card_Ico]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil]
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    have hlt : (n : ℝ) < N := lt_of_lt_of_le h2 hC
    exact_mod_cast hlt

/-- Each alternative's assigned mass differs from its exact mass by at most `2^(-b)`. -/
theorem bitLaw_error (b : ℕ) (p : Law ι) (i : ι) :
    |(bitLaw b p).value i - p.value i| ≤ 1 / (2 : ℝ) ^ b := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  set A := (2 : ℝ) ^ b * cumulative p (position i) with hA
  set C := (2 : ℝ) ^ b * cumulative p (position i + 1) with hC
  have hA0 : 0 ≤ A := mul_nonneg h2.le (cumulative_nonneg p _)
  have hCA : C = A + (2 : ℝ) ^ b * p.value i := by rw [hC, cumulative_succ, mul_add]
  have hAC : A ≤ C := by
    rw [hCA]
    have := mul_nonneg h2.le (p.nonneg i)
    linarith
  have hCN : C ≤ ((2 ^ b : ℕ) : ℝ) := by
    push_cast
    calc C ≤ (2 : ℝ) ^ b * 1 := mul_le_mul_of_nonneg_left (cumulative_le_one p _) h2.le
      _ = (2 : ℝ) ^ b := mul_one _
  have hval : (bitLaw b p).value i = (1 / (2 : ℝ) ^ b) * ((⌈C⌉₊ - ⌈A⌉₊ : ℕ) : ℝ) := by
    rw [← count_interval (2 ^ b) hCN, Finset.mul_sum]
    change (∑ u, (uniformLaw b).value u * (if decode b p u = i then 1 else 0)) = _
    apply Finset.sum_congr rfl
    intro u _
    change 1 / (2 : ℝ) ^ b * (if decode b p u = i then 1 else 0) = _
    simp only [decode_eq_iff, Hit, ← hA, ← hC]
  have hcA := Nat.le_ceil A
  have hcA' := Nat.ceil_lt_add_one hA0
  have hcC := Nat.le_ceil C
  have hcC' := Nat.ceil_lt_add_one (hA0.trans hAC)
  have hsub : ((⌈C⌉₊ - ⌈A⌉₊ : ℕ) : ℝ) = (⌈C⌉₊ : ℝ) - ⌈A⌉₊ := Nat.cast_sub (Nat.ceil_mono hAC)
  have hp : p.value i = (C - A) / (2 : ℝ) ^ b := by
    rw [hCA]
    field_simp
    ring
  have hdiff : (bitLaw b p).value i - p.value i =
      ((⌈C⌉₊ : ℝ) - ⌈A⌉₊ - (C - A)) / (2 : ℝ) ^ b := by
    rw [hval, hsub, hp]
    ring
  rw [hdiff, abs_div, abs_of_pos h2]
  apply div_le_div_of_nonneg_right _ h2.le
  rw [abs_le]
  constructor <;> linarith

/-- Total rounding error of a `b`-bit choice among `k` alternatives. -/
theorem bitLaw_l1 (b : ℕ) (p : Law ι) :
    l1 (bitLaw b p).value p.value ≤ Fintype.card ι / (2 : ℝ) ^ b := by
  calc l1 (bitLaw b p).value p.value ≤ ∑ _i : ι, 1 / (2 : ℝ) ^ b :=
        Finset.sum_le_sum fun i _ => bitLaw_error b p i
    _ = Fintype.card ι / (2 : ℝ) ^ b := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end Decode

namespace Prog

variable {Q α β : Type} {ι : Type} [Fintype ι]

/-- Choose an alternative approximately according to `p` using exactly `b`
uniform random bits. Locating the drawn integer among the cumulative intervals
is charged as one local operation per alternative. -/
def draw (b : ℕ) (p : Law ι) (k : ι → Prog Q α) : Prog Q α :=
  .work (Fintype.card ι) (.choose (uniformLaw b) fun u => k (decode b p u))

theorem QueryBound.draw {b : ℕ} {p : Law ι} {k : ι → Prog Q α} {n : ℕ}
    (h : ∀ i, QueryBound (k i) n) : QueryBound (Prog.draw b p k) n :=
  .work _ _ _ (.choose _ _ _ fun u => h (decode b p u))

theorem exp_draw (O : Oracle Q) (b : ℕ) (p : Law ι) (k : ι → Prog Q α) (f : α → ℝ) :
    (draw b p k).exp O f = ∑ i, (bitLaw b p).value i * (k i).exp O f := by
  change (∑ u, (uniformLaw b).value u * (k (decode b p u)).exp O f) =
    ∑ i, (∑ u, (uniformLaw b).value u * (if decode b p u = i then 1 else 0)) * (k i).exp O f
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp

/-- Every internal random choice is a uniform `b`-bit draw, and at most the
stated number of draws occur on any execution path. -/
inductive BitBound (b : ℕ) : Prog Q α → ℕ → Prop
  | ret (a : α) (n : ℕ) : BitBound b (.ret a) n
  | query (x : Q) (k : ℝ → Prog Q α) (n : ℕ) :
      (∀ r, BitBound b (k r) n) → BitBound b (.query x k) n
  | draw (k : Fin (2 ^ b) → Prog Q α) (n : ℕ) :
      (∀ u, BitBound b (k u) n) → BitBound b (.choose (uniformLaw b) k) (n + 1)
  | work (c : ℕ) (m : Prog Q α) (n : ℕ) : BitBound b m n → BitBound b (.work c m) n

theorem BitBound.mono {b : ℕ} {m : Prog Q α} {c d : ℕ} (h : BitBound b m c) (hcd : c ≤ d) :
    BitBound b m d := by
  induction h generalizing d with
  | ret a n => exact .ret a d
  | query x k n _ ih => exact .query x k d fun r => ih r hcd
  | draw k n _ ih =>
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    exact .draw k d' fun u => ih u (by omega)
  | work c m n _ ih => exact .work c m d (ih hcd)

theorem BitBound.bind {b : ℕ} {m : Prog Q α} {g : α → Prog Q β} {c d : ℕ}
    (hm : BitBound b m c) (hg : ∀ x, BitBound b (g x) d) :
    BitBound b (m.bind g) (c + d) := by
  induction hm with
  | ret x n => exact (hg x).mono (by omega)
  | query x k n _ ih => exact .query x _ _ ih
  | draw k n _ ih =>
    have hn : n + 1 + d = (n + d) + 1 := by omega
    rw [hn]
    exact .draw _ _ ih
  | work c m n _ ih => exact .work c _ _ ih

theorem BitBound.guarded {b : ℕ} {c : Prop} {x : Q} {k : ℝ → Prog Q α} {n : ℕ}
    (h : ∀ r, BitBound b (k r) n) : BitBound b (Prog.guarded c x k) n := by
  unfold Prog.guarded
  refine .work _ _ _ ?_
  split_ifs
  · exact .query x k n h
  · exact h 0

theorem BitBound.ofDraw {b : ℕ} {p : Law ι} {k : ι → Prog Q α} {n : ℕ}
    (h : ∀ i, BitBound b (k i) n) : BitBound b (Prog.draw b p k) (n + 1) :=
  .work _ _ _ (.draw _ n fun u => h (decode b p u))

theorem BitBound.replicate {b : ℕ} {Ω : Type} {m : Prog Q Ω} {c : ℕ} (h : BitBound b m c)
    (n : ℕ) : BitBound b (m.replicate n) (n * c) := by
  induction n with
  | zero => exact .ret _ _
  | succ n ih =>
    have hb : BitBound b (m.replicate (n + 1)) (c + (n * c + 0)) :=
      h.bind fun x => ih.bind fun xs => .ret _ 0
    exact hb.mono (by rw [Nat.succ_mul]; omega)

end Prog

end
end DirectedCycleFPRAS
