module

public import DirectedCycleFPRAS.RationalProgram
public import DirectedCycleFPRAS.RecordedExposure

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
set_option linter.unusedSectionVars false

namespace RatProg
variable {Q α β γ δ : Type}

/-- Exact agreement of nominal laws through an explicit result conversion. -/
def Refines (O : Oracle Q) (m : RatProg α) (M : Prog Q β) (cast : α → β) : Prop :=
  ∀ f : β → ℝ, m.nominal.exp noOracle (fun a => f (cast a)) = M.exp O f

theorem Refines.ret (O : Oracle Q) (a : α) (cast : α → β) :
    Refines O (.ret a) (.ret (cast a)) cast := fun _ => rfl

theorem Refines.bind {O : Oracle Q} {m : RatProg α} {M : Prog Q β}
    {cast : α → β} (h : Refines O m M cast) {k : α → RatProg γ} {K : β → Prog Q δ}
    {out : γ → δ} (hk : ∀ a, Refines O (k a) (K (cast a)) out) :
    Refines O (m.bind k) (M.bind K) out := by
  intro f
  rw [nominal_bind,Prog.exp_bind,Prog.exp_bind]
  simp_rw [hk _ f]
  exact h (fun b => (K b).exp O f)

theorem Refines.weightedEquiv {O : Oracle Q} {ι : Type} [Fintype ι] {n : ℕ}
    (e : Fin n ≃ ι) (w : ι → ℚ) (d : ι) {k : ι → RatProg α} {K : ι → Prog Q β}
    {cast : α → β} (hk : ∀ i, Refines O (k i) (K i) cast) :
    Refines O (weightedEquiv e w d k) (.choose (normLaw (fun i => (w i : ℝ)) d) K) cast := by
  intro f
  rw [weightedEquiv_exp]
  change (∑ i, _ * _) = ∑ i, _ * _
  simp_rw [hk _ f]

end RatProg

variable {E : Type} [Fintype E] [DecidableEq E]

def rationalPin (p : E → ℚ) (e : E) (b : Bool) : E → ℚ :=
  Function.update p e (if b then 1 else 0)

theorem rationalPin_cast (p : E → ℚ) (e : E) (b : Bool) :
    (fun j => (rationalPin p e b j : ℝ)) = pin (fun j => (p j : ℝ)) e b := by
  funext j
  by_cases h : j=e <;> cases b <;> simp [rationalPin,pin,h]

def rationalPinned (p : E → ℚ) : E → Bool := fun e => decide (p e = 1)

theorem rationalPinned_cast (p : E → ℚ) : rationalPinned p = pinned (fun e => (p e : ℝ)) := by
  funext e
  unfold rationalPinned pinned
  congr 1
  apply propext
  dsimp only
  constructor <;> intro h <;> exact_mod_cast h

/-- The normalized nominal bias is retained exactly, before rounding. -/
def rationalNormValue {ι : Type} [Fintype ι] [DecidableEq ι]
    (w : ι → ℚ) (d i : ι) : ℚ :=
  if (∀ j, 0 ≤ w j) ∧ 0 < ∑ j, w j then w i / ∑ j, w j else if i=d then 1 else 0

theorem rationalNormValue_cast {ι : Type} [Fintype ι] [DecidableEq ι]
    (w : ι → ℚ) (d i : ι) :
    (rationalNormValue w d i : ℝ) = (normLaw (fun j => (w j : ℝ)) d).value i := by
  have he : ((∀ j, (0 : ℚ) ≤ w j) ∧ 0 < ∑ j, w j) ↔
      ((∀ j, (0 : ℝ) ≤ (w j : ℝ)) ∧ 0 < ∑ j, (w j : ℝ)) := by
    constructor <;> rintro ⟨ha,hb⟩ <;> constructor
    · intro j; exact_mod_cast ha j
    · exact_mod_cast hb
    · intro j; exact_mod_cast ha j
    · exact_mod_cast hb
  unfold rationalNormValue normLaw
  by_cases h : (∀ j, (0 : ℚ) ≤ w j) ∧ 0 < ∑ j, w j
  · rw [ite_eq_left h,dite_eq_left (he.mp h)]
    simp
  · rw [ite_eq_right h,dite_eq_right (fun hh => h (he.mpr hh))]
    dsimp only
    split_ifs <;> simp

/-- A computable guard prevents calls on impossible residual events. -/
def rationalGuard (feas : (E → ℚ) → Bool) (oracle : (E → ℚ) → RatProg ℚ)
    (p : E → ℚ) : RatProg ℚ :=
  if feas p then oracle p else .ret 0

/-- Rational exposure keeps the nominal proposal product alongside the sample. -/
def rationalRecordedExpose (feas : (E → ℚ) → Bool) (oracle : (E → ℚ) → RatProg ℚ) :
    List E → (E → ℚ) → RatProg ((E → Bool) × ℚ)
  | [], p => .ret (rationalPinned p, 1)
  | e::l, p =>
    (rationalGuard feas oracle (rationalPin p e true)).bind fun r₁ =>
    (rationalGuard feas oracle (rationalPin p e false)).bind fun r₀ =>
      let w := fun b : Bool => if b then p e*r₁ else (1-p e)*r₀
      RatProg.weightedEquiv finTwoEquiv w true fun b =>
        (rationalRecordedExpose feas oracle l (rationalPin p e b)).bind fun r =>
          .ret (r.1,rationalNormValue w true b*r.2)

namespace RatProg
variable {Q : Type} (O : Oracle Q) (mk : (E → ℝ) → Q)
    (feas : (E → ℚ) → Bool) (F : (E → ℝ) → Prop)
    (oracle : (E → ℚ) → RatProg ℚ)

theorem rationalGuard_refines
    (hf : ∀ p, feas p = true ↔ F (fun e => (p e : ℝ)))
    (ho : ∀ p, Refines O (oracle p) (.query (mk (fun e => (p e : ℝ))) Prog.ret) Rat.cast)
    (p : E → ℚ) :
    Refines O (rationalGuard feas oracle p)
      (Prog.guarded (F (fun e => (p e : ℝ))) (mk (fun e => (p e : ℝ))) Prog.ret) Rat.cast := by
  classical
  intro f
  by_cases h : feas p = true
  · simpa [rationalGuard,h,Prog.guarded,(hf p).mp h,Prog.exp] using ho p f
  · simp [rationalGuard,h,Prog.guarded,mt (hf p).mpr h,nominal,Prog.exp]

theorem rationalRecordedExpose_refines
    (hf : ∀ p, feas p = true ↔ F (fun e => (p e : ℝ)))
    (ho : ∀ p, Refines O (oracle p) (.query (mk (fun e => (p e : ℝ))) Prog.ret) Rat.cast)
    (l : List E) (p : E → ℚ) :
    Refines O (rationalRecordedExpose feas oracle l p)
      (recordedExpose mk F l (fun e => (p e : ℝ)))
      (fun r => (r.1,(r.2 : ℝ))) := by
  induction l generalizing p with
  | nil =>
    simpa only [rationalRecordedExpose,recordedExpose,rationalPinned_cast,Rat.cast_one] using
      Refines.ret O (rationalPinned p, (1 : ℚ)) (fun r => (r.1,(r.2 : ℝ)))
  | cons e l ih =>
    unfold rationalRecordedExpose recordedExpose
    have hg (b : Bool) := rationalGuard_refines O mk feas F oracle hf ho (rationalPin p e b)
    simp only [rationalPin_cast] at hg
    -- Express the real guards as binds to expose their continuation.
    have guard_bind (c : Prop) (q : Q) (k : ℝ → Prog Q ((E → Bool) × ℝ)) :
        Prog.guarded c q k = (Prog.guarded c q Prog.ret).bind k := by
      classical
      by_cases h : c <;> simp [Prog.guarded,h,Prog.bind]
    rw [guard_bind]
    apply (hg true).bind
    intro r₁
    rw [guard_bind]
    apply (hg false).bind
    intro r₀
    dsimp only
    have hw : (fun b : Bool => ((if b then p e*r₁ else (1-p e)*r₀ : ℚ) : ℝ)) =
        (fun b : Bool => if b then (p e : ℝ)*(r₁ : ℝ) else (1-(p e : ℝ))*(r₀ : ℝ)) := by
      funext b; cases b <;> simp
    rw [← hw]
    apply Refines.weightedEquiv
    intro b
    have hi := ih (rationalPin p e b)
    simp only [rationalPin_cast] at hi
    apply hi.bind
    intro r
    have hv := rationalNormValue_cast (fun b : Bool => if b then p e*r₁ else (1-p e)*r₀) true b
    simpa only [Rat.cast_mul,hv,hw] using
      Refines.ret O (r.1,rationalNormValue (fun b : Bool => if b then p e*r₁ else (1-p e)*r₀) true b*r.2)
        (fun r => (r.1,(r.2 : ℝ)))

end RatProg
end DirectedCycleFPRAS
