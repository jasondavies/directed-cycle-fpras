module

public import DirectedCycleFPRAS.RationalExecution

@[expose] public section

/-! The executable interpreter on a uniformly random fixed-length bit tape
has exactly its denotational law. Unused suffix bits are integrated out. -/
namespace DirectedCycleFPRAS.BitProg
open scoped BigOperators
variable {α : Type}

/-- A finite tape, extended deterministically beyond its allocated budget. -/
def zeroExtend {N : ℕ} (bits : Fin N → Bool) (i : ℕ) : Bool :=
  if h : i<N then bits ⟨i,h⟩ else false

/-- Concatenate independent prefix and suffix bit blocks. -/
def joinBits {b N : ℕ} (x : Fin b → Bool) (y : Fin N → Bool) (i : Fin (b+N)) : Bool :=
  if h : i.val<b then x ⟨i.val,h⟩ else y ⟨i.val-b,by have := i.isLt; omega⟩

def splitBitsEquiv (b N : ℕ) : (Fin (b+N) → Bool) ≃ (Fin b → Bool) × (Fin N → Bool) where
  toFun f := (fun i => f ⟨i.val,by have := i.isLt; omega⟩,
    fun i => f ⟨b+i.val,by have := i.isLt; omega⟩)
  invFun xy := joinBits xy.1 xy.2
  left_inv f := by
    funext i
    dsimp only
    unfold joinBits
    split_ifs with h
    · rfl
    · dsimp only
      apply congrArg f
      apply Fin.ext
      change b+(i.val-b)=i.val
      omega
  right_inv xy := by
    apply Prod.ext <;> funext i
    · simp [joinBits,i.isLt]
    · simp [joinBits]

@[simp] theorem zeroExtend_join_left {b N : ℕ} (x : Fin b → Bool) (y : Fin N → Bool) (i : Fin b) :
    zeroExtend (joinBits x y) i.val = x i := by
  have hi : i.val<b+N := by have := i.isLt; omega
  simp [zeroExtend,joinBits,hi,i.isLt]

@[simp] theorem zeroExtend_join_right {b N : ℕ} (x : Fin b → Bool) (y : Fin N → Bool) (j : ℕ) :
    zeroExtend (joinBits x y) (b+j) = zeroExtend y j := by
  by_cases hj : j<N
  · simp [zeroExtend,joinBits,hj,show b+j<b+N by omega]
  · simp [zeroExtend,hj,show ¬b+j<b+N by omega]

/-- Moving the tape origin preserves the returned value. -/
theorem run_shift (m : BitProg α) (tape : ℕ → Bool) (offset start : ℕ) :
    (m.run tape (offset+start)).1=(m.run (fun i => tape (offset+i)) start).1 := by
  induction m generalizing start with
  | ret a => rfl
  | draw b k ih =>
    simp only [run,Nat.add_assoc]
    exact ih _ (start+b)

/-- After consuming a prefix, the continuation reads exactly the suffix. -/
theorem run_join (m : BitProg α) {N b : ℕ}
    (x : Fin b → Bool) (y : Fin N → Bool) :
    (m.run (zeroExtend (joinBits x y)) b).1=(m.run (zeroExtend y) 0).1 := by
  have hs := run_shift m (zeroExtend (joinBits x y)) b 0
  simp only [Nat.add_zero] at hs
  rw [hs]
  simp only [zeroExtend_join_right]

/-- Every bounded adaptive bit program has the law of its actual run on `N`
independent fair bits; branches may consume different numbers of bits. -/
theorem run_uniform {m : BitProg α} {N : ℕ} (h : Bits m N) (f : α → ℝ) :
    (∑ bits : Fin N → Bool, (1/(2 : ℝ)^N)*f ((m.run (zeroExtend bits) 0).1)) =
      m.toProg.exp noOracle f := by
  classical
  induction h with
  | ret a N =>
    simp only [run,toProg,Prog.exp,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
      Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  | draw b N k hk ih =>
    rw [← (splitBitsEquiv b N).symm.sum_comp]
    rw [Fintype.sum_prod_type]
    have he (x : Fin b → Bool) (y : Fin N → Bool) :
        ((BitProg.draw b k).run (zeroExtend ((splitBitsEquiv b N).symm (x,y))) 0).1 =
          ((k (readBlock b x)).run (zeroExtend y) 0).1 := by
      change ((BitProg.draw b k).run (zeroExtend (joinBits x y)) 0).1 = _
      simp only [run,Nat.zero_add,zeroExtend_join_left]
      exact run_join _ x y
    simp_rw [he]
    have hw : (1 : ℝ)/2^(b+N) = (1/2^b)*(1/2^N) := by rw [pow_add]; ring
    calc
      _ = ∑ x : Fin b → Bool, (1/(2 : ℝ)^b)*
          (∑ y : Fin N → Bool, (1/(2 : ℝ)^N)*f (((k (readBlock b x)).run (zeroExtend y) 0).1)) := by
            simp_rw [hw,Finset.mul_sum,mul_assoc]
      _ = ∑ x : Fin b → Bool, (1/(2 : ℝ)^b)*((k (readBlock b x)).toProg.exp noOracle f) := by
        simp_rw [ih]
      _ = _ := readBlock_uniform b (fun u => (k u).toProg.exp noOracle f)

end DirectedCycleFPRAS.BitProg
