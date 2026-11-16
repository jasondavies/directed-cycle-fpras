module

public import DirectedCycleFPRAS.ProgramComposition

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section

/-- Normalization commutes with an injective reindexing when omitted
alternatives have weight zero and the fallback is retained. -/
theorem normLaw_reindex {A B : Type} [Fintype A] [Fintype B]
    (e : A → B) (he : Function.Injective e) (w : B → ℝ) (v : A → ℝ) (d : A)
    (hw : ∀ a, v a = w (e a)) (hz : ∀ b ∉ Set.range e, w b = 0)
    (f : B → ℝ) (g : A → ℝ) (hfg : ∀ a, f (e a) = g a) :
    (∑ b, (normLaw w (e d)).value b * f b) = ∑ a, (normLaw v d).value a * g a := by
  have hsum := Fintype.sum_of_injective e he v w hz hw
  have hnonneg : (∀ a, 0 ≤ v a) ↔ ∀ b, 0 ≤ w b := by
    constructor
    · intro h b
      by_cases hb : b ∈ Set.range e
      · obtain ⟨a, rfl⟩ := hb
        simpa [← hw a] using h a
      · rw [hz b hb]
    · intro h a; rw [hw a]; exact h _
  by_cases hv : (∀ a, 0 ≤ v a) ∧ 0 < ∑ a, v a
  · have hw' : (∀ b, 0 ≤ w b) ∧ 0 < ∑ b, w b := ⟨hnonneg.mp hv.1, hsum ▸ hv.2⟩
    simp_rw [normLaw_value _ _ hw'.1 hw'.2, normLaw_value _ _ hv.1 hv.2]
    symm
    apply Fintype.sum_of_injective e he
    · intro b hb; rw [hz b hb]; simp
    · intro a; rw [hw a, hsum, hfg a]
  · have hw' : ¬ ((∀ b, 0 ≤ w b) ∧ 0 < ∑ b, w b) := by
      intro h; exact hv ⟨hnonneg.mpr h.1, hsum.symm ▸ h.2⟩
    simp only [normLaw, dite_eq_right hv, dite_eq_right hw']
    simpa using hfg d

end
end DirectedCycleFPRAS
