module

public import DirectedCycleFPRAS.RationalProgram

@[expose] public section
namespace DirectedCycleFPRAS.RatProg
variable {α β : Type}

theorem ChoiceBound.mono {m : RatProg α} {a b : ℕ} (h : ChoiceBound m a) (hab : a ≤ b) :
    ChoiceBound m b := by
  induction h generalizing b with
  | ret a n => exact .ret a b
  | @choose n p k N h ih =>
    obtain ⟨b',rfl⟩ : ∃ b', b=n+b' := ⟨b-n, by omega⟩
    exact .choose p k b' (fun i => ih i (by omega))

theorem ChoiceBound.bind {m : RatProg α} {g : α → RatProg β} {a b : ℕ}
    (hm : ChoiceBound m a) (hg : ∀ x, ChoiceBound (g x) b) : ChoiceBound (m.bind g) (a+b) := by
  induction hm with
  | ret x n => exact (hg x).mono (by omega)
  | choose p k n h ih =>
    simpa only [RatProg.bind,Nat.add_assoc] using ChoiceBound.choose p _ (n+b) ih

theorem ChoiceBound.weighted {n : ℕ} (w : Fin n → ℚ) (d : Fin n)
    (k : Fin n → RatProg α) {N : ℕ} (h : ∀ i, ChoiceBound (k i) N) :
    ChoiceBound (RatProg.weighted w d k) (n+N) := .choose _ _ _ h

theorem ChoiceBound.weightedEquiv {ι : Type} {n : ℕ} (e : Fin n ≃ ι)
    (w : ι → ℚ) (d : ι) (k : ι → RatProg α) {N : ℕ} (h : ∀ i, ChoiceBound (k i) N) :
    ChoiceBound (RatProg.weightedEquiv e w d k) (n+N) := .choose _ _ _ (fun i => h (e i))

end DirectedCycleFPRAS.RatProg
