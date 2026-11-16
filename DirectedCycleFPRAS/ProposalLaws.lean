module

public import DirectedCycleFPRAS.ProgramComposition

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false

/-- Relative-error normalization preserves support and loses at most a factor
1-2a on each positive choice. This multiplicative bound avoids a TV loss. -/
theorem normalized_lower {I : Type} [Fintype I] (t w : I → ℝ) (d : I)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (ht0 : ∀ i, 0 ≤ t i)
    (ht : 0 < ∑ i, t i) (hw : ∀ i, |w i - t i| ≤ a * t i) :
    (∀ i, 0 ≤ w i) ∧ 0 < ∑ i, w i ∧
    (∀ i, (normLaw w d).value i = 0 ↔ t i = 0) ∧
    (∀ i, (1 - 2*a) * (t i / ∑ j, t j) ≤ (normLaw w d).value i) := by
  have hlo (i : I) : (1-a)*t i ≤ w i := by have h := (abs_le.mp (hw i)).1; nlinarith
  have hhi (i : I) : w i ≤ (1+a)*t i := by have h := (abs_le.mp (hw i)).2; nlinarith
  have hw0 (i : I) : 0 ≤ w i := le_trans (mul_nonneg (by linarith) (ht0 i)) (hlo i)
  have hslo : (1-a)*(∑ i, t i) ≤ ∑ i, w i := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hlo i
  have hshi : (∑ i, w i) ≤ (1+a)*(∑ i, t i) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hhi i
  have hws : 0 < ∑ i, w i := lt_of_lt_of_le (mul_pos (by linarith) ht) hslo
  refine ⟨hw0, hws, ?_, ?_⟩
  · intro i
    rw [normLaw_value w d hw0 hws, div_eq_zero_iff]
    constructor
    · rintro (hz | hz)
      · have := hlo i; have := ht0 i; nlinarith
      · exact False.elim ((ne_of_gt hws) hz)
    · intro hz; left; have := hhi i; have := hw0 i; nlinarith
  · intro i
    rw [normLaw_value w d hw0 hws]
    have hr : (1-2*a)*(1+a) ≤ 1-a := by nlinarith [sq_nonneg a]
    have hp : 0 < 1+a := by linarith
    calc
      (1-2*a)*(t i / ∑ j, t j) ≤ ((1-a)*t i) / ((1+a)*(∑ j, t j)) := by
        apply (le_div_iff₀ (mul_pos hp ht)).mpr
        have he : (1-2*a)*(t i / ∑ j, t j)*((1+a)*(∑ j, t j)) =
            ((1-2*a)*(1+a))*t i := by field_simp
        rw [he]
        exact mul_le_mul_of_nonneg_right hr (ht0 i)
      _ ≤ w i / ∑ j, w j := div_le_div₀ (hw0 i) (hlo i) hws hshi

theorem Law.nonempty {I : Type} [Fintype I] (p : Law I) : Nonempty I := by
  by_contra h
  have : IsEmpty I := not_nonempty_iff.mp h
  have hs := p.sum_one
  simp at hs

namespace Prog
variable {Q α β : Type}

/-- Supported output invariants for a program with a fixed randomized oracle.
Both oracle and internal choices ignore only probability-zero branches. -/
inductive Holds (O : Oracle Q) (P : α → Prop) : Prog Q α → Prop
  | ret (a : α) : P a → Holds O P (.ret a)
  | query (x : Q) (k : ℝ → Prog Q α) :
      (∀ s, (O.law x).value s ≠ 0 → Holds O P (k (O.answer x s))) → Holds O P (.query x k)
  | choose {I : Type} [Fintype I] (p : Law I) (k : I → Prog Q α) :
      (∀ i, p.value i ≠ 0 → Holds O P (k i)) → Holds O P (.choose p k)
  | work (c : ℕ) (m : Prog Q α) : Holds O P m → Holds O P (.work c m)

theorem Holds.bind {O : Oracle Q} {P : α → Prop} {R : β → Prop} {m : Prog Q α}
    (h : Holds O P m) {g : α → Prog Q β} (hg : ∀ x, P x → Holds O R (g x)) :
    Holds O R (m.bind g) := by
  induction h with
  | ret x hx => exact hg x hx
  | query x k h ih => exact .query x _ ih
  | choose p k h ih => exact .choose p _ ih
  | work c m h ih => exact .work c _ ih

theorem Holds.guarded {O : Oracle Q} {P : α → Prop} (c : Prop) (x : Q)
    (k : ℝ → Prog Q α)
    (h : ∀ s, Holds O P (k (if c then O.answer x s else 0))) :
    Holds O P (Prog.guarded c x k) := by
  unfold Prog.guarded
  refine .work _ _ ?_
  by_cases hc : c
  · simp only [ite_eq_left hc]
    exact .query x k fun s _ => by simpa [hc] using h s
  · simp only [ite_eq_right hc]
    simpa [hc] using h (Classical.choice (O.law x).nonempty)

theorem Holds.imp {O : Oracle Q} {P R : α → Prop} {m : Prog Q α}
    (h : Holds O P m) (hPR : ∀ x, P x → R x) : Holds O R m := by
  induction h with
  | ret x hx => exact .ret x (hPR x hx)
  | query x k h ih => exact .query x _ ih
  | choose p k h ih => exact .choose p _ ih
  | work c m h ih => exact .work c _ ih

theorem Holds.exp_congr {O : Oracle Q} {P : α → Prop} {m : Prog Q α}
    (h : Holds O P m) {f g : α → ℝ} (hfg : ∀ x, P x → f x = g x) :
    m.exp O f = m.exp O g := by
  induction h with
  | ret x hx => exact hfg x hx
  | query x k h ih =>
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : (O.law x).value s = 0
    · simp [hs]
    · rw [ih s hs]
  | choose p k h ih =>
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p.value i = 0
    · simp [hi]
    · rw [ih i hi]
  | work c m h ih => exact ih

end Prog
end
end DirectedCycleFPRAS
