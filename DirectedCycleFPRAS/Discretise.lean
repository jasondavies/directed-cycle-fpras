module

public import DirectedCycleFPRAS.RandomBits

@[expose] public section

/-!
# Replacing exact discrete choices by fixed-bit draws

`Prog.discretise b` replaces every exact random choice of a program by the
`b`-bit cumulative-interval draw of `RandomBits`. `Prog.exp_discretise_le`
bounds the effect: if along every execution path the numbers of alternatives
of the choices sum to at most `N`, then the probability of any event, and more
generally the expectation of any `[0,1]`-valued function of the result,
changes by at most `N / 2^b`. Choices may depend on the whole history; this is
the sequential coupling argument.

This is the generic half of the argument in research/DISCRETISATION.md that an
algorithm stated with exact rational-probability choices can be run on fair
random bits.
-/

namespace DirectedCycleFPRAS

open scoped BigOperators
open Classical

noncomputable section

namespace Prog

variable {Q α : Type}

/-- Replace every exact choice by a `b`-bit draw. -/
def discretise (b : ℕ) : Prog Q α → Prog Q α
  | .ret a => .ret a
  | .query x k => .query x fun r => (k r).discretise b
  | @Prog.choose _ _ _ _ p k => Prog.draw b p fun i => (k i).discretise b
  | .work c m => .work c (m.discretise b)

/-- Along every execution path, the numbers of alternatives of the random
choices sum to at most the stated bound. -/
inductive ChoiceBound : Prog Q α → ℕ → Prop
  | ret (a : α) (n : ℕ) : ChoiceBound (.ret a) n
  | query (x : Q) (k : ℝ → Prog Q α) (n : ℕ) :
      (∀ r, ChoiceBound (k r) n) → ChoiceBound (.query x k) n
  | choose {ι : Type} [Fintype ι] (p : Law ι) (k : ι → Prog Q α) (n : ℕ) :
      (∀ i, ChoiceBound (k i) n) → ChoiceBound (.choose p k) (Fintype.card ι + n)
  | work (c : ℕ) (m : Prog Q α) (n : ℕ) : ChoiceBound m n → ChoiceBound (.work c m) n

/-- After discretisation every random choice is a uniform `b`-bit draw. -/
theorem discretise_bitBound (b : ℕ) {m : Prog Q α} {N : ℕ} (h : ChoiceBound m N) :
    BitBound b (m.discretise b) N := by
  induction h with
  | ret a n => exact .ret a n
  | query x k n _ ih => exact .query x _ n ih
  | @choose ι _ p k n _ ih =>
    have hd : BitBound b (Prog.draw b p fun i => (k i).discretise b) (n + 1) :=
      BitBound.ofDraw ih
    have hc := card_pos_of_law p
    exact hd.mono (by omega)
  | work c m n _ ih => exact .work c _ n ih

/-- **Discretisation error.** Running a program on `b`-bit draws instead of
exact choices changes the expectation of a `[0,1]`-valued function of the
result by at most `N / 2^b`, where `N` bounds the total number of alternatives
along any path. The oracle and its randomness are unchanged. -/
theorem exp_discretise_le (O : Oracle Q) (b : ℕ) {f : α → ℝ} (hf0 : ∀ a, 0 ≤ f a)
    (hf1 : ∀ a, f a ≤ 1) {m : Prog Q α} {N : ℕ} (h : ChoiceBound m N) :
    |(m.discretise b).exp O f - m.exp O f| ≤ (N : ℝ) / (2 : ℝ) ^ b := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  induction h with
  | ret a n =>
    change |f a - f a| ≤ _
    rw [sub_self, abs_zero]
    positivity
  | query x k n _ ih =>
    change |(∑ s, (O.law x).value s * ((k (O.answer x s)).discretise b).exp O f) -
      ∑ s, (O.law x).value s * (k (O.answer x s)).exp O f| ≤ _
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ s, |(O.law x).value s * ((k (O.answer x s)).discretise b).exp O f -
            (O.law x).value s * (k (O.answer x s)).exp O f| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, (O.law x).value s * ((n : ℝ) / (2 : ℝ) ^ b) := by
        apply Finset.sum_le_sum
        intro s _
        rw [← mul_sub, abs_mul, abs_of_nonneg ((O.law x).nonneg s)]
        exact mul_le_mul_of_nonneg_left (ih _) ((O.law x).nonneg s)
      _ = (n : ℝ) / (2 : ℝ) ^ b := by rw [← Finset.sum_mul, Law.sum_one, one_mul]
  | @choose ι _ p k n _ ih =>
    change |(Prog.draw b p fun i => (k i).discretise b).exp O f -
      ∑ i, p.value i * (k i).exp O f| ≤ _
    rw [exp_draw]
    have hsplit : (∑ i, (bitLaw b p).value i * ((k i).discretise b).exp O f) -
        ∑ i, p.value i * (k i).exp O f =
        (∑ i, ((bitLaw b p).value i - p.value i) * ((k i).discretise b).exp O f) +
        ∑ i, p.value i * (((k i).discretise b).exp O f - (k i).exp O f) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h1 : |∑ i, ((bitLaw b p).value i - p.value i) * ((k i).discretise b).exp O f| ≤
        (Fintype.card ι : ℝ) / (2 : ℝ) ^ b := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ (bitLaw_l1 b p))
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have he0 : 0 ≤ ((k i).discretise b).exp O f := exp_nonneg O _ hf0
      have he1 : ((k i).discretise b).exp O f ≤ 1 := exp_le_of_le O _ hf1
      rw [abs_of_nonneg he0]
      exact mul_le_of_le_one_right (abs_nonneg _) he1
    have h2' : |∑ i, p.value i * (((k i).discretise b).exp O f - (k i).exp O f)| ≤
        (n : ℝ) / (2 : ℝ) ^ b := by
      calc _ ≤ ∑ i, |p.value i * (((k i).discretise b).exp O f - (k i).exp O f)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, p.value i * ((n : ℝ) / (2 : ℝ) ^ b) := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_mul, abs_of_nonneg (p.nonneg i)]
          exact mul_le_mul_of_nonneg_left (ih i) (p.nonneg i)
        _ = (n : ℝ) / (2 : ℝ) ^ b := by rw [← Finset.sum_mul, Law.sum_one, one_mul]
    rw [hsplit]
    calc _ ≤ _ + _ := abs_add_le _ _
      _ ≤ (Fintype.card ι : ℝ) / (2 : ℝ) ^ b + (n : ℝ) / (2 : ℝ) ^ b := add_le_add h1 h2'
      _ = ((Fintype.card ι + n : ℕ) : ℝ) / (2 : ℝ) ^ b := by
        push_cast
        ring
  | work c m n _ ih => exact ih

end Prog

end
end DirectedCycleFPRAS
