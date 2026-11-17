module

public import DirectedCycleFPRAS.RationalCycle
public import DirectedCycleFPRAS.WitnessAlgorithm

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
set_option linter.unusedSectionVars false

/-- Computable lower median, with zero for an empty vector. -/
def rationalMedianValues {k : ℕ} (v : Fin k → ℚ) : Finset ℚ :=
  (Finset.univ.image v).filter fun m =>
    2*(Finset.univ.filter fun i => v i < m).card ≤ k ∧
      2*(Finset.univ.filter fun i => m < v i).card ≤ k

def rationalMedian {k : ℕ} (v : Fin k → ℚ) : ℚ :=
  if h : (rationalMedianValues v).Nonempty then (rationalMedianValues v).min' h else 0

theorem rationalMedianValues_cast {k : ℕ} (v : Fin k → ℚ) :
    (rationalMedianValues v).image (fun x : ℚ => (x : ℝ)) = medianValues (fun i => (v i : ℝ)) := by
  classical
  ext x
  simp only [rationalMedianValues,medianValues,Finset.mem_image,Finset.mem_filter,IsMedian]
  constructor
  · rintro ⟨q,⟨⟨i,hi,he⟩,hlo,hhi⟩,rfl⟩
    refine ⟨⟨i,hi,by exact_mod_cast he⟩,?_,?_⟩
    · simpa using hlo
    · simpa using hhi
  · rintro ⟨⟨i,hi,rfl⟩,hlo,hhi⟩
    refine ⟨v i,⟨⟨i,hi,rfl⟩,?_,?_⟩,rfl⟩
    · simpa using hlo
    · simpa using hhi

theorem rationalMedian_cast {k : ℕ} (v : Fin k → ℚ) :
    (rationalMedian v : ℝ) = median (fun i => (v i : ℝ)) := by
  classical
  have hm : Monotone (fun x : ℚ => (x : ℝ)) := by intro a b h; change (a : ℝ) ≤ (b : ℝ); exact_mod_cast h
  have he := rationalMedianValues_cast v
  unfold rationalMedian median
  by_cases h : (rationalMedianValues v).Nonempty
  · have h' : (medianValues (fun i => (v i : ℝ))).Nonempty := he ▸ h.image _
    rw [dite_eq_left h,dite_eq_left h']
    simpa only [he] using hm.map_finset_min' h
  · have h' : ¬(medianValues (fun i => (v i : ℝ))).Nonempty := by
      rw [← he, Finset.image_nonempty]
      exact h
    simp only [dite_eq_right h,dite_eq_right h',Rat.cast_zero]

namespace RatProg
variable {α β Q : Type}

def mapSamples (cast : α → β) : (n : ℕ) → Samples α n → Samples β n
  | 0, _ => ()
  | n+1, xs => (cast xs.1,mapSamples cast n xs.2)

theorem Refines.replicate {O : Oracle Q} {m : RatProg α} {M : Prog Q β}
    {cast : α → β} (h : Refines O m M cast) (n : ℕ) :
    Refines O (m.replicate n) (M.replicate n) (mapSamples cast n) := by
  induction n with
  | zero => exact Refines.ret O () (mapSamples cast 0)
  | succ n ih =>
    unfold RatProg.replicate Prog.replicate
    apply h.bind
    intro a
    apply ih.bind
    intro xs
    exact Refines.ret O (a,xs) (mapSamples cast (n+1))

theorem mapSamples_toFn (cast : α → β) (n : ℕ) (xs : Samples α n) :
    samplesToFn n (mapSamples cast n xs) = fun i => cast (samplesToFn n xs i) := by
  induction n with
  | zero => funext i; exact i.elim0
  | succ n ih =>
    funext i
    exact Fin.cases rfl (fun j => congrFun (ih xs.2) j) i

def medianOf (m : RatProg ℚ) (k : ℕ) : RatProg ℚ :=
  (m.replicate k).bind fun xs => .ret (rationalMedian (samplesToFn k xs))

theorem Refines.medianOf {O : Oracle Q} {m : RatProg ℚ} {M : Prog Q ℝ}
    (h : Refines O m M Rat.cast) (k : ℕ) :
    Refines O (m.medianOf k) (M.medianOf k) Rat.cast := by
  unfold RatProg.medianOf Prog.medianOf
  apply (h.replicate k).bind
  intro xs
  have he := rationalMedian_cast (samplesToFn k xs)
  rw [mapSamples_toFn]
  simpa only [he] using Refines.ret O (rationalMedian (samplesToFn k xs)) (fun x : ℚ => (x : ℝ))

end RatProg

end DirectedCycleFPRAS
