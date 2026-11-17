module

public import DirectedCycleFPRAS.ProgramComposition

@[expose] public section

/-! Executable rational finite choices and finite-bit programs. Computation
uses rationals and explicit finite indices. The real-valued definitions occur
only in the denotation and its correctness proof. Bit counts measure random
bits consumed; they do not charge the computation of continuation functions. -/
namespace DirectedCycleFPRAS
open scoped BigOperators

/-- An explicitly indexed rational probability vector. -/
structure RatLaw (n : ℕ) where
  value : Fin n → ℚ
  nonneg : ∀ i, 0 ≤ value i
  sum_one : ∑ i, value i = 1

namespace RatLaw
variable {n : ℕ}

def cumulative (p : RatLaw n) (j : ℕ) : ℚ :=
  ∑ i, if i.val < j then p.value i else 0

theorem cumulative_zero (p : RatLaw n) : p.cumulative 0 = 0 := by simp [cumulative]
theorem cumulative_card (p : RatLaw n) : p.cumulative n = 1 := by
  simpa [cumulative] using p.sum_one

theorem card_pos (p : RatLaw n) : 0 < n := by
  by_contra h
  have hn : n = 0 := by omega
  subst n
  have h := p.sum_one
  simp at h

theorem exists_upper (p : RatLaw n) (b : ℕ) (u : Fin (2^b)) :
    ∃ j, (u.val : ℚ) < (2 : ℚ)^b * p.cumulative (j+1) := by
  refine ⟨n-1, ?_⟩
  rw [Nat.sub_add_cancel p.card_pos, p.cumulative_card, mul_one]
  exact_mod_cast u.isLt

/-- Bounded cumulative-interval search. The second component counts the
rational threshold tests actually performed; exhausted fuel returns `j`. -/
def searchUpper (p : RatLaw n) (b : ℕ) (u : Fin (2^b)) : ℕ → ℕ → ℕ × ℕ
  | 0,j => (j,0)
  | f+1,j =>
    if (u.val : ℚ) < (2 : ℚ)^b*p.cumulative (j+1) then (j,1)
    else let r := searchUpper p b u f (j+1); (r.1,r.2+1)

theorem searchUpper_calls (p : RatLaw n) (b : ℕ) (u : Fin (2^b)) (f j : ℕ) :
    (p.searchUpper b u f j).2 ≤ f := by
  induction f generalizing j with
  | zero => exact le_rfl
  | succ f ih =>
    simp only [searchUpper]
    split_ifs
    · omega
    · exact Nat.add_le_add_right (ih _) 1

theorem searchUpper_eq_find (p : RatLaw n) (b : ℕ) (u : Fin (2^b)) (f j : ℕ)
    (hj : j ≤ Nat.find (p.exists_upper b u))
    (hf : Nat.find (p.exists_upper b u) < j+f) :
    (p.searchUpper b u f j).1=Nat.find (p.exists_upper b u) := by
  induction f generalizing j with
  | zero => omega
  | succ f ih =>
    simp only [searchUpper]
    split_ifs with h
    · exact le_antisymm hj (Nat.find_min' (p.exists_upper b u) h)
    · apply ih
      · have he : j ≠ Nat.find (p.exists_upper b u) := by
          intro he
          exact h (he ▸ Nat.find_spec (p.exists_upper b u))
        omega
      · omega

theorem find_upper_lt (p : RatLaw n) (b : ℕ) (u : Fin (2^b)) :
    Nat.find (p.exists_upper b u) < n := by
    have h := Nat.find_min' (p.exists_upper b u)
      (show (u.val : ℚ) < (2 : ℚ)^b*p.cumulative (n-1+1) by
        rw [Nat.sub_add_cancel p.card_pos, p.cumulative_card, mul_one]
        exact_mod_cast u.isLt)
    have hn := p.card_pos
    omega

/-- The executable selector has a fixed bound of `n` threshold tests. -/
def select (p : RatLaw n) (b : ℕ) (u : Fin (2^b)) : Fin n :=
  ⟨(p.searchUpper b u n 0).1, by
    rw [p.searchUpper_eq_find b u n 0 (by omega) (by simpa using p.find_upper_lt b u)]
    exact p.find_upper_lt b u⟩

theorem select_eq_find (p : RatLaw n) (b : ℕ) (u : Fin (2^b)) :
    (p.select b u).val=Nat.find (p.exists_upper b u) :=
  p.searchUpper_eq_find b u n 0 (by omega) (by simpa using p.find_upper_lt b u)

theorem select_interval (p : RatLaw n) (b : ℕ) (u : Fin (2^b)) :
    (2 : ℚ)^b*p.cumulative (p.select b u).val ≤ u.val ∧
      (u.val : ℚ) < (2 : ℚ)^b*p.cumulative ((p.select b u).val+1) := by
  simp only [select_eq_find]
  constructor
  · by_cases h : Nat.find (p.exists_upper b u) = 0
    · rw [h,p.cumulative_zero,mul_zero]
      positivity
    · have hm := Nat.find_min (p.exists_upper b u)
        (m := Nat.find (p.exists_upper b u)-1) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find (p.exists_upper b u))] at hm
      exact le_of_not_gt hm
  · exact Nat.find_spec (p.exists_upper b u)

/-- The direct real interpretation of the rational probability vector. -/
noncomputable def toLaw (p : RatLaw n) : Law (Fin n) where
  value i := p.value i
  nonneg i := by exact_mod_cast p.nonneg i
  sum_one := by exact_mod_cast p.sum_one

noncomputable def order (n : ℕ) : Fin n ≃ Fin n :=
  (Fintype.equivFin (Fin n)).trans (finCongr (Fintype.card_fin n))

theorem order_position (i : Fin n) : (order n i).val = position i := rfl

/-- Reindex so the existing real decoder uses the explicit rational order. -/
noncomputable def orderedLaw (p : RatLaw n) : Law (Fin n) where
  value i := p.value (order n i)
  nonneg i := by exact_mod_cast p.nonneg (order n i)
  sum_one := by
    apply ((order n).sum_comp (fun i => (p.value i : ℝ))).trans
    exact_mod_cast p.sum_one

theorem ordered_cumulative (p : RatLaw n) (j : ℕ) :
    DirectedCycleFPRAS.cumulative p.orderedLaw j = (p.cumulative j : ℝ) := by
  unfold DirectedCycleFPRAS.cumulative orderedLaw cumulative
  simp only [Rat.cast_sum, apply_ite, Rat.cast_zero]
  exact (order n).sum_comp
    (fun i => if i.val < j then (p.value i : ℝ) else 0)

/-- Rational selection implements the existing finite-bit decoder after the
explicit permutation of indices. -/
theorem select_eq_decode (p : RatLaw n) (b : ℕ) (u : Fin (2^b)) :
    p.select b u = order n (decode b p.orderedLaw u) := by
  let e := order n
  have h := p.select_interval b u
  have hd : decode b p.orderedLaw u = e.symm (p.select b u) := by
    apply (decode_eq_iff _ _ _ _).mpr
    simp only [Hit, ordered_cumulative]
    have he : position (e.symm (p.select b u)) = (p.select b u).val := by
      change (e (e.symm (p.select b u))).val = _
      rw [e.apply_symm_apply]
    rw [he]
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  rw [hd]
  exact (e.apply_symm_apply _).symm

/-- Total normalization with the same fallback convention as `normLaw`. -/
def norm (w : Fin n → ℚ) (d : Fin n) : RatLaw n :=
  if h : (∀ i, 0 ≤ w i) ∧ 0 < ∑ i, w i then
    { value := fun i => w i / ∑ j, w j
      nonneg := fun i => div_nonneg (h.1 i) h.2.le
      sum_one := by rw [← Finset.sum_div, div_self (ne_of_gt h.2)] }
  else
    { value := fun i => if i=d then 1 else 0
      nonneg := fun i => by split_ifs <;> norm_num
      sum_one := by simp }

theorem norm_value_cast (w : Fin n → ℚ) (d i : Fin n) :
    ((norm w d).value i : ℝ) = (normLaw (fun j => (w j : ℝ)) d).value i := by
  have he : ((∀ j, (0 : ℚ) ≤ w j) ∧ 0 < ∑ j, w j) ↔
      ((∀ j, (0 : ℝ) ≤ (w j : ℝ)) ∧ 0 < ∑ j, (w j : ℝ)) := by
    constructor <;> rintro ⟨ha,hb⟩ <;> constructor
    · intro j; exact_mod_cast ha j
    · exact_mod_cast hb
    · intro j; exact_mod_cast ha j
    · exact_mod_cast hb
  unfold norm normLaw
  by_cases h : (∀ j, (0 : ℚ) ≤ w j) ∧ 0 < ∑ j, w j
  · rw [dite_eq_left h,dite_eq_left (he.mp h)]
    simp
  · rw [dite_eq_right h,dite_eq_right (fun hh => h (he.mpr hh))]
    dsimp only
    split_ifs <;> simp

/-- The explicit-index sampler has the usual finite-grid coupling bound. -/
theorem select_error (p : RatLaw n) (b : ℕ) (g : Fin n → ℝ)
    (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1) :
    |(∑ u : Fin (2^b), (uniformLaw b).value u*g (p.select b u)) -
      ∑ i, (p.value i : ℝ)*g i| ≤ (n : ℝ)/(2 : ℝ)^b := by
  let m : Prog Empty (Fin n) := .choose p.orderedLaw fun i => .ret (order n i)
  have hm : Prog.ChoiceBound m (n+0) := by
    have h := Prog.ChoiceBound.choose p.orderedLaw (fun i => Prog.ret (Q := Empty) (order n i)) 0
      (fun i => Prog.ChoiceBound.ret _ 0)
    simpa only [Fintype.card_fin] using h
  have h := Prog.exp_discretise_le noOracle b hg0 hg1 hm
  have he : m.exp noOracle g = ∑ i, (p.value i : ℝ)*g i := by
    change (∑ i, (p.value (order n i) : ℝ)*g (order n i)) = _
    exact (order n).sum_comp (fun i => (p.value i : ℝ)*g i)
  rw [he] at h
  simp only [m,Prog.discretise,Prog.draw,Prog.exp,← p.select_eq_decode] at h
  simpa using h

end RatLaw

/-- A lazy program driven by explicit uniform bit blocks. Only the selected
continuation is evaluated; no full decision tree is materialized. -/
inductive BitProg (α : Type) where
  | ret : α → BitProg α
  | draw (b : ℕ) : (Fin (2^b) → BitProg α) → BitProg α

namespace BitProg
variable {α β : Type}

def bind : BitProg α → (α → BitProg β) → BitProg β
  | .ret a, f => f a
  | .draw b k, f => .draw b fun u => (k u).bind f

/-- A rational finite choice followed by its selected continuation. -/
def choose {n : ℕ} (b : ℕ) (p : RatLaw n) (k : Fin n → BitProg α) : BitProg α :=
  .draw b fun u => k (p.select b u)

/-- Choose among arbitrary rational weights, with a specified fallback. -/
def weighted {n : ℕ} (b : ℕ) (w : Fin n → ℚ) (d : Fin n)
    (k : Fin n → BitProg α) : BitProg α :=
  choose b (RatLaw.norm w d) k

/-- A finite type can use any supplied executable enumeration. -/
def weightedEquiv {ι : Type} {n : ℕ} (b : ℕ) (e : Fin n ≃ ι)
    (w : ι → ℚ) (d : ι) (k : ι → BitProg α) : BitProg α :=
  weighted b (fun i => w (e i)) (e.symm d) (fun i => k (e i))

/-- Read a block, with the first supplied bit least significant. -/
def readBlock : (b : ℕ) → (Fin b → Bool) → Fin (2^b)
  | 0, _ => ⟨0, by simp⟩
  | b+1, bits =>
    let rest := readBlock b (fun i => bits i.succ)
    ⟨2*rest.val+(if bits 0 then 1 else 0), by
      have h := rest.isLt
      rw [pow_succ]
      split_ifs <;> omega⟩

theorem readBlock_injective (b : ℕ) : Function.Injective (readBlock b) := by
  induction b with
  | zero => intro x y _; funext i; exact i.elim0
  | succ b ih =>
    intro x y h
    have he := congrArg Fin.val h
    change 2*(readBlock b (fun i => x i.succ)).val+(if x 0 then 1 else 0) =
      2*(readBlock b (fun i => y i.succ)).val+(if y 0 then 1 else 0) at he
    have h0 : x 0 = y 0 := by
      cases hx : x 0 <;> cases hy : y 0 <;> simp_all <;> omega
    have hr : readBlock b (fun i => x i.succ) = readBlock b (fun i => y i.succ) := by
      apply Fin.ext
      rw [h0] at he
      omega
    have ht := ih hr
    funext i
    exact Fin.cases h0 (fun j => congrFun ht j) i

theorem readBlock_bijective (b : ℕ) : Function.Bijective (readBlock b) := by
  have e : (Fin b → Bool) ≃ Fin (2^b) := Fintype.equivOfCardEq (by simp)
  exact ⟨readBlock_injective b,
    (Finite.injective_iff_surjective_of_equiv e).mp (readBlock_injective b)⟩

/-- Independent fair bits form exactly the uniform integer used in the
program denotation; this is an equality, not a limiting approximation. -/
theorem readBlock_uniform (b : ℕ) (f : Fin (2^b) → ℝ) :
    (∑ bits : Fin b → Bool, (1/(2 : ℝ)^b)*f (readBlock b bits)) =
      ∑ u, (uniformLaw b).value u*f u := by
  exact Fintype.sum_bijective (readBlock b) (readBlock_bijective b) _ _ (fun _ => rfl)

/-- Run against an explicit bit tape, returning the result and next position. -/
def run : BitProg α → (ℕ → Bool) → ℕ → α × ℕ
  | .ret a, _, offset => (a,offset)
  | .draw b k, tape, offset =>
    (k (readBlock b (fun i => tape (offset+i.val)))).run tape (offset+b)

theorem run_bind (m : BitProg α) (f : α → BitProg β) (tape : ℕ → Bool) (offset : ℕ) :
    (m.bind f).run tape offset =
      let r := m.run tape offset
      (f r.1).run tape r.2 := by
  induction m generalizing offset with
  | ret a => rfl
  | draw b k ih => exact ih _ _

/-- A worst-case bound on consumed random bits, independent of the tape. -/
inductive Bits : BitProg α → ℕ → Prop
  | ret (a : α) (N : ℕ) : Bits (.ret a) N
  | draw (b N : ℕ) (k : Fin (2^b) → BitProg α) :
      (∀ u, Bits (k u) N) → Bits (.draw b k) (b+N)

theorem run_bits {m : BitProg α} {N : ℕ} (h : Bits m N) (tape : ℕ → Bool) (offset : ℕ) :
    (m.run tape offset).2 ≤ offset+N := by
  induction h generalizing offset with
  | ret a N => simp [run]
  | draw b N k h ih =>
    simp only [run]
    exact (ih _ _).trans_eq (by omega)

/-- Bits beyond the worst-case consumption bound cannot affect execution. -/
theorem run_congr {m : BitProg α} {N : ℕ} (h : Bits m N) (t₁ t₂ : ℕ → Bool) (offset : ℕ)
    (ht : ∀ j, offset ≤ j → j < offset+N → t₁ j = t₂ j) :
    m.run t₁ offset = m.run t₂ offset := by
  induction h generalizing offset with
  | ret a N => rfl
  | draw b N k h ih =>
    have hx : (fun i : Fin b => t₁ (offset+i.val)) = (fun i : Fin b => t₂ (offset+i.val)) := by
      funext i
      apply ht <;> omega
    simp only [run,hx]
    apply ih
    intro j hj hj'
    apply ht <;> omega

theorem Bits.mono {m : BitProg α} {N M : ℕ} (h : Bits m N) (hNM : N ≤ M) : Bits m M := by
  induction h generalizing M with
  | ret a N => exact .ret a M
  | draw b N k h ih =>
    have hb : b ≤ M := by omega
    simpa only [Nat.add_sub_of_le hb] using
      Bits.draw b (M-b) k (fun u => ih u (by omega))

theorem Bits.bind {m : BitProg α} {f : α → BitProg β} {N K : ℕ}
    (h : Bits m N) (hf : ∀ a, Bits (f a) K) : Bits (m.bind f) (N+K) := by
  induction h with
  | ret a N => exact (hf a).mono (by omega)
  | draw b N k h ih => simpa only [BitProg.bind,Nat.add_assoc] using Bits.draw b (N+K) _ ih

noncomputable def toProg : BitProg α → Prog Empty α
  | .ret a => .ret a
  | .draw b k => .choose (uniformLaw b) fun u => (k u).toProg

theorem bits_toProg {m : BitProg α} {N : ℕ} (h : Bits m N) :
    Prog.BitCost (fun _ : Empty => 0) m.toProg N := by
  induction h with
  | ret a N => exact .ret a N
  | draw b N k h ih => exact .draw b _ N ih

/-- Finite transcripts of the draws actually encountered, not an enumeration
of unvisited branches. This is the sample space used only in the proof. -/
def Seed : BitProg α → Type
  | .ret _ => Unit
  | .draw b k => Σ u : Fin (2^b), (k u).Seed

noncomputable instance seedFintype (m : BitProg α) : Fintype m.Seed := by
  induction m with
  | ret a => exact inferInstanceAs (Fintype Unit)
  | draw b k ih => letI := ih; exact inferInstanceAs (Fintype (Σ u, (k u).Seed))

def result : (m : BitProg α) → m.Seed → α
  | .ret a, _ => a
  | .draw _ k, ⟨u,s⟩ => (k u).result s

/-- Record exactly the bit blocks consumed by a run. -/
def trace : (m : BitProg α) → (ℕ → Bool) → ℕ → m.Seed
  | .ret _, _, _ => ()
  | .draw b k, tape, offset =>
    let u := readBlock b (fun i => tape (offset+i.val))
    ⟨u,(k u).trace tape (offset+b)⟩

theorem trace_result (m : BitProg α) (tape : ℕ → Bool) (offset : ℕ) :
    m.result (m.trace tape offset) = (m.run tape offset).1 := by
  induction m generalizing offset with
  | ret a => rfl
  | draw b k ih => exact ih _ _

noncomputable def seedLaw : (m : BitProg α) → Law m.Seed
  | .ret _ => unitLaw
  | .draw b k => (uniformLaw b).sigma fun u => (k u).seedLaw

/-- Exact law correspondence between the executable transcript evaluator and
`Prog.exp`, including adaptive widths and branches. -/
theorem result_law (m : BitProg α) (f : α → ℝ) :
    (∑ s, m.seedLaw.value s*f (m.result s)) = m.toProg.exp noOracle f := by
  induction m with
  | ret a =>
    change (∑ _s : Unit, (1 : ℝ)*f a) = f a
    simp
  | draw b k ih =>
    change (∑ s : Σ u : Fin (2^b), (k u).Seed,
      ((uniformLaw b).value s.1 * (k s.1).seedLaw.value s.2) *
        f ((k s.1).result s.2)) =
      ∑ u, (uniformLaw b).value u * (k u).toProg.exp noOracle f
    rw [Fintype.sum_sigma]
    simp_rw [mul_assoc, ← Finset.mul_sum, ih]

end BitProg
end DirectedCycleFPRAS
