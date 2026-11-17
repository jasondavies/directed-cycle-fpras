module

public import DirectedCycleFPRAS.RationalExecution
public import DirectedCycleFPRAS.ReindexLaw

@[expose] public section

/-! Rational programs with exact nominal semantics and compilation to an
executable bit-tape program. The approximation theorem is independent of the
ordering used by the real model's decoder. -/
namespace DirectedCycleFPRAS
open scoped BigOperators

inductive RatProg (α : Type) where
  | ret : α → RatProg α
  | choose {n : ℕ} : RatLaw n → (Fin n → RatProg α) → RatProg α

namespace RatProg
variable {α β : Type}

def bind : RatProg α → (α → RatProg β) → RatProg β
  | .ret a, f => f a
  | .choose p k, f => .choose p fun i => (k i).bind f

def weighted {n : ℕ} (w : Fin n → ℚ) (d : Fin n) (k : Fin n → RatProg α) : RatProg α :=
  .choose (RatLaw.norm w d) k

def weightedEquiv {ι : Type} {n : ℕ} (e : Fin n ≃ ι)
    (w : ι → ℚ) (d : ι) (k : ι → RatProg α) : RatProg α :=
  weighted (fun i => w (e i)) (e.symm d) (fun i => k (e i))

noncomputable def nominal : RatProg α → Prog Empty α
  | .ret a => .ret a
  | .choose p k => .choose p.toLaw fun i => (k i).nominal

/-- Compile by introducing a finite-bit draw at each rational choice. -/
def compile (b : ℕ) : RatProg α → BitProg α
  | .ret a => .ret a
  | .choose p k => BitProg.choose b p fun i => (k i).compile b

theorem nominal_bind (m : RatProg α) (f : α → RatProg β) :
    (m.bind f).nominal = m.nominal.bind (fun a => (f a).nominal) := by
  induction m with
  | ret a => rfl
  | choose p k ih => simp only [bind,nominal,Prog.bind,ih]

theorem compile_bind (b : ℕ) (m : RatProg α) (f : α → RatProg β) :
    (m.bind f).compile b = (m.compile b).bind (fun a => (f a).compile b) := by
  induction m with
  | ret a => rfl
  | choose p k ih => simp only [bind,compile,BitProg.choose,BitProg.bind,ih]

theorem weighted_exp {n : ℕ} (w : Fin n → ℚ) (d : Fin n) (k : Fin n → RatProg α)
    (f : α → ℝ) :
    (weighted w d k).nominal.exp noOracle f =
      ∑ i, (normLaw (fun j => (w j : ℝ)) d).value i*(k i).nominal.exp noOracle f := by
  simp only [weighted,nominal,Prog.exp,RatLaw.toLaw,RatLaw.norm_value_cast]

theorem weightedEquiv_exp {ι : Type} [Fintype ι] {n : ℕ} (e : Fin n ≃ ι)
    (w : ι → ℚ) (d : ι) (k : ι → RatProg α) (f : α → ℝ) :
    (weightedEquiv e w d k).nominal.exp noOracle f =
      ∑ i, (normLaw (fun j => (w j : ℝ)) d).value i*(k i).nominal.exp noOracle f := by
  rw [weightedEquiv,weighted_exp]
  have h := normLaw_reindex e e.injective (fun i => (w i : ℝ))
    (fun i => (w (e i) : ℝ)) (e.symm d) (fun i => rfl)
    (fun i hi => False.elim (hi (e.surjective i)))
    (fun i => (k i).nominal.exp noOracle f)
    (fun i => (k (e i)).nominal.exp noOracle f) (fun i => rfl)
  simpa using h.symm

/-- Sum of numbers of alternatives along a path. -/
inductive ChoiceBound : RatProg α → ℕ → Prop
  | ret (a : α) (N : ℕ) : ChoiceBound (.ret a) N
  | choose {n : ℕ} (p : RatLaw n) (k : Fin n → RatProg α) (N : ℕ) :
      (∀ i, ChoiceBound (k i) N) → ChoiceBound (.choose p k) (n+N)

theorem ChoiceBound.nominal {m : RatProg α} {N : ℕ} (h : ChoiceBound m N) :
    Prog.ChoiceBound m.nominal N := by
  induction h with
  | ret a N => exact .ret a N
  | @choose n p k N h ih =>
    simpa only [RatProg.nominal,Fintype.card_fin] using Prog.ChoiceBound.choose p.toLaw _ N ih

theorem ChoiceBound.compile {m : RatProg α} {N : ℕ} (h : ChoiceBound m N) (b : ℕ) :
    BitProg.Bits (m.compile b) (b*N) := by
  induction h with
  | ret a N => exact .ret a _
  | @choose n p k N h ih =>
    have hc : b+b*N ≤ b*(n+N) := by
      have hn := p.card_pos
      have hmul := Nat.mul_le_mul_left b hn
      simpa [Nat.mul_add] using Nat.add_le_add_right hmul (b*N)
    exact (BitProg.Bits.draw b (b*N) _ (fun u => ih (p.select b u))).mono hc

/-- Adaptive rational choices compile with total rounding error at most
`N / 2^b`, measured against the exact nominal program. -/
theorem compile_error (b : ℕ) {m : RatProg α} {N : ℕ} (h : ChoiceBound m N)
    (f : α → ℝ) (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) :
    |(m.compile b).toProg.exp noOracle f-m.nominal.exp noOracle f| ≤ (N : ℝ)/(2 : ℝ)^b := by
  induction h with
  | ret a N => simp only [compile,BitProg.toProg,nominal,Prog.exp,sub_self,abs_zero]; positivity
  | @choose n p k N h ih =>
    let g := fun i => ((k i).compile b).toProg.exp noOracle f
    let r := fun i => (k i).nominal.exp noOracle f
    have hg0 : ∀ i, 0 ≤ g i := fun i => Prog.exp_nonneg noOracle _ hf0
    have hg1 : ∀ i, g i ≤ 1 := fun i => Prog.exp_le_of_le noOracle _ hf1
    have he : |(∑ i, (p.value i : ℝ)*g i)-(∑ i, (p.value i : ℝ)*r i)| ≤
        (N : ℝ)/(2 : ℝ)^b := by
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ i, |(p.value i : ℝ)*g i-(p.value i : ℝ)*r i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (p.value i : ℝ)*((N : ℝ)/(2 : ℝ)^b) := by
          apply Finset.sum_le_sum
          intro i _
          rw [← mul_sub,abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ p.value i by exact_mod_cast p.nonneg i)]
          exact mul_le_mul_of_nonneg_left (ih i) (p.toLaw.nonneg i)
        _ = (N : ℝ)/(2 : ℝ)^b := by
          rw [← Finset.sum_mul]
          have hs : ∑ i, (p.value i : ℝ) = 1 := p.toLaw.sum_one
          rw [hs,one_mul]
    change |(∑ u, (uniformLaw b).value u*g (p.select b u))-∑ i, (p.value i : ℝ)*r i| ≤ _
    calc
      _ ≤ |(∑ u, (uniformLaw b).value u*g (p.select b u))-∑ i, (p.value i : ℝ)*g i| +
          |(∑ i, (p.value i : ℝ)*g i)-∑ i, (p.value i : ℝ)*r i| := abs_sub_le _ _ _
      _ ≤ (n : ℝ)/(2 : ℝ)^b+(N : ℝ)/(2 : ℝ)^b := add_le_add (p.select_error b g hg0 hg1) he
      _ = ((n+N : ℕ) : ℝ)/(2 : ℝ)^b := by push_cast; ring

end RatProg
end DirectedCycleFPRAS
