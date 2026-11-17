module

public import DirectedCycleFPRAS.RationalCounting

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section

/-- Finite seed representation of a rational program, viewed as real output. -/
def rationalRand (m : RatProg ℚ) : RandReal :=
  (m.nominal.bind fun r => Prog.ret (r : ℝ)).toRand

def randExpectation (r : RandReal) (f : ℝ → ℝ) : ℝ := ∑ s, r.law.value s*f (r.value s)

theorem rationalRand_exp (m : RatProg ℚ) (f : ℝ → ℝ) :
    randExpectation (rationalRand m) f = m.nominal.exp noOracle (fun r => f (r : ℝ)) := by
  rw [randExpectation,rationalRand,← Prog.exp_eq_toRand noOracle]
  simp only [Prog.exp_bind,Prog.exp]

variable {I E : Type}

/-- Extension used solely in proofs. Executable programs always call `base`
on rational inputs. Irrational queries receive the supplied exact fallback. -/
def rationalQueryRand (base : I → (E → ℚ) → RatProg ℚ)
    (fallback : I → (E → ℝ) → ℝ) (x : I × (E → ℝ)) : RandReal :=
  if h : ∃ p : E → ℚ, (fun e => (p e : ℝ)) = x.2 then
    rationalRand (base x.1 (Classical.choose h))
  else (Prog.ret (Q := Empty) (fallback x.1 x.2)).toRand

def liftRationalOracle (base : I → (E → ℚ) → RatProg ℚ)
    (fallback : I → (E → ℝ) → ℝ) : Oracle (I × (E → ℝ)) where
  Seed x := (rationalQueryRand base fallback x).Seed
  law x := (rationalQueryRand base fallback x).law
  answer x := (rationalQueryRand base fallback x).value

theorem rationalQueryRand_cast (base : I → (E → ℚ) → RatProg ℚ)
    (fallback : I → (E → ℝ) → ℝ) (i : I) (p : E → ℚ) :
    rationalQueryRand base fallback (i,fun e => (p e : ℝ)) = rationalRand (base i p) := by
  have h : ∃ q : E → ℚ, (fun e => (q e : ℝ)) = (fun e => (p e : ℝ)) := ⟨p,rfl⟩
  rw [rationalQueryRand,dite_eq_left h]
  have he : Classical.choose h = p := by
    funext e
    have he := congrFun (Classical.choose_spec h) e
    exact_mod_cast he
  rw [he]

theorem liftRationalOracle_refines (base : I → (E → ℚ) → RatProg ℚ)
    (fallback : I → (E → ℝ) → ℝ) (i : I) (p : E → ℚ) :
    RatProg.Refines (liftRationalOracle base fallback) (base i p)
      (.query (i,fun e => (p e : ℝ)) Prog.ret) Rat.cast := by
  intro f
  change _ = randExpectation (rationalQueryRand base fallback (i,fun e => (p e : ℝ))) f
  rw [rationalQueryRand_cast,rationalRand_exp]

theorem liftRationalOracle_failure (base : I → (E → ℚ) → RatProg ℚ)
    (fallback : I → (E → ℝ) → ℝ) (P : I → (E → ℝ) → ℝ → Prop)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hf : ∀ i q, P i q (fallback i q))
    (hb : ∀ i p, (base i p).nominal.exp noOracle
      (fun r => if P i (fun e => (p e : ℝ)) (r : ℝ) then 0 else 1) ≤ γ)
    (x : I × (E → ℝ)) :
    (∑ s, if P x.1 x.2 ((liftRationalOracle base fallback).answer x s)
      then 0 else ((liftRationalOracle base fallback).law x).value s) ≤ γ := by
  have he : (∑ s, if P x.1 x.2 ((liftRationalOracle base fallback).answer x s)
      then 0 else ((liftRationalOracle base fallback).law x).value s) =
      randExpectation (rationalQueryRand base fallback x)
        (fun r => if P x.1 x.2 r then 0 else 1) := by
    simp only [randExpectation,liftRationalOracle,mul_ite,mul_zero,mul_one]
    rfl
  rw [he]
  by_cases h : ∃ p : E → ℚ, (fun e => (p e : ℝ)) = x.2
  · rw [rationalQueryRand,dite_eq_left h,rationalRand_exp]
    have he := Classical.choose_spec h
    simpa only [he] using hb x.1 (Classical.choose h)
  · rw [rationalQueryRand,dite_eq_right h]
    simpa [randExpectation,Prog.toRand,unitLaw,hf] using hγ

namespace RatProg

theorem castNominal_refines (m : RatProg ℚ) :
    Refines noOracle m (m.nominal.bind fun r => .ret (r : ℝ)) Rat.cast := by
  intro f
  simp only [Prog.exp_bind,Prog.exp]

theorem medianOf_failure (m : RatProg ℚ) (k : ℕ) (P : ℝ → Prop)
    (hP : ∀ a b c, P a → P c → a ≤ b → b ≤ c → P b)
    (hfail : m.nominal.exp noOracle (fun r => if P (r : ℝ) then 0 else 1) ≤ 1/4) :
    (m.medianOf k).nominal.exp noOracle (fun r => if P (r : ℝ) then 0 else 1) ≤ (7/8 : ℝ)^k := by
  rw [(castNominal_refines m).medianOf k (fun r => if P r then 0 else 1)]
  apply Prog.medianOf_failure noOracle _ k hP
  simpa only [Prog.exp_bind,Prog.exp] using hfail

end RatProg

end
end DirectedCycleFPRAS
