module

public import DirectedCycleFPRAS.AlgorithmSEstimator

@[expose] public section

namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section

/-- Taking a sample median never increases the height, even for an empty sample. -/
theorem median_height {k H : ℕ} (hH : 1 ≤ H) (v : Fin k → ℝ)
    (hv : ∀ i, Height H (v i)) : Height H (median v) :=
  median_property (height_zero hH) v hv

theorem Oracle.amplify_height {Q : Type} (O : Oracle Q) {H : ℕ} (hH : 1 ≤ H)
    (k : ℕ) (x : Q) (hx : ∀ s, Height H (O.answer x s))
    (s : (O.amplify k).Seed x) : Height H ((O.amplify k).answer x s) :=
  median_height hH _ fun i => hx (s i)

namespace Prog
variable {Q α β : Type}

/-- Replace each oracle query by a program using only internal randomness. -/
def inline (S : Q → Prog Empty ℝ) : Prog Q α → Prog Empty α
  | .ret a => .ret a
  | .query x k => (S x).bind fun r => (k r).inline S
  | @Prog.choose _ _ ι inst p k => @Prog.choose _ _ ι inst p fun i => (k i).inline S
  | .work c m => .work c (m.inline S)

/-- The finite-law oracle represented by the query programs. -/
def programOracle (S : Q → Prog Empty ℝ) : Oracle Q where
  Seed x := (S x).toRand.Seed
  law x := (S x).toRand.law
  answer x := (S x).toRand.value

theorem exp_inline (S : Q → Prog Empty ℝ) (m : Prog Q α) (f : α → ℝ) :
    (m.inline S).exp noOracle f = m.exp (programOracle S) f := by
  induction m with
  | ret a => rfl
  | query x k ih =>
    simp only [inline, exp_bind, ih]
    exact exp_eq_toRand noOracle (S x) _
  | choose p k ih => simp only [inline, exp, ih]
  | work c m ih => exact ih

theorem Sat.inline {A : ℝ → Prop} {Qp : Q → Prop} {R : α → Prop}
    {m : Prog Q α} (h : Sat A Qp R m) (S : Q → Prog Empty ℝ)
    (hS : ∀ x, Qp x → Sat (fun _ => True) (fun _ => True) A (S x)) :
    Sat (fun _ => True) (fun _ => True) R (m.inline S) := by
  induction h with
  | ret a ha => exact .ret a ha
  | query x k hx _ ih => exact (hS x hx).bind ih
  | choose p k _ ih => exact .choose p _ ih
  | work c m _ ih => exact .work c _ ih

/-- Preserve a property of every entry through independent repetition. -/
theorem Sat.replicate_values {A : ℝ → Prop} {Qp : Q → Prop} {P : α → Prop}
    {m : Prog Q α} (h : Sat A Qp P m) (k : ℕ) :
    Sat A Qp (fun xs => ∀ i, P (samplesToFn k xs i)) (m.replicate k) := by
  induction k with
  | zero => exact .ret _ (fun i => i.elim0)
  | succ k ih =>
    refine h.bind fun x hx => ih.bind fun xs hxs => .ret _ ?_
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hx
    · exact hxs j

theorem Sat.medianOf {A : ℝ → Prop} {Qp : Q → Prop} {P : ℝ → Prop}
    {m : Prog Q ℝ} (h : Sat A Qp P m) (h0 : P 0) (k : ℕ) :
    Sat A Qp P (m.medianOf k) :=
  (h.replicate_values k).bind fun _xs hxs => .ret _ (median_property h0 _ hxs)

theorem BitBound.medianOf {b c : ℕ} {m : Prog Q ℝ} (h : BitBound b m c) (k : ℕ) :
    BitBound b (m.medianOf k) (k * c) := by
  exact ((h.replicate k).bind (d := 0) fun _ => .ret _ 0).mono (by omega)

/-- A total count of fair bits, allowing different widths at different draws.
Queries are charged by the supplied bound, so oracle randomness is included. -/
inductive BitCost (queryCost : Q → ℕ) : Prog Q α → ℕ → Prop
  | ret (a : α) (n : ℕ) : BitCost queryCost (.ret a) n
  | query (x : Q) (k : ℝ → Prog Q α) (n : ℕ) :
      (∀ r, BitCost queryCost (k r) n) → BitCost queryCost (.query x k) (queryCost x + n)
  | draw (b : ℕ) (k : Fin (2 ^ b) → Prog Q α) (n : ℕ) :
      (∀ u, BitCost queryCost (k u) n) → BitCost queryCost (.choose (uniformLaw b) k) (b + n)
  | work (c : ℕ) (m : Prog Q α) (n : ℕ) :
      BitCost queryCost m n → BitCost queryCost (.work c m) n

theorem BitCost.mono {q : Q → ℕ} {m : Prog Q α} {n n' : ℕ}
    (h : BitCost q m n) (hn : n ≤ n') : BitCost q m n' := by
  induction h generalizing n' with
  | ret a n => exact .ret a n'
  | query x k n _ ih =>
    obtain ⟨d, rfl⟩ : ∃ d, n' = q x + d := ⟨n' - q x, by omega⟩
    exact .query x k d fun r => ih r (by omega)
  | draw b k n _ ih =>
    obtain ⟨d, rfl⟩ : ∃ d, n' = b + d := ⟨n' - b, by omega⟩
    exact .draw b k d fun u => ih u (by omega)
  | work c m n _ ih => exact .work c m n' (ih hn)

theorem BitCost.bind {q : Q → ℕ} {m : Prog Q α} {g : α → Prog Q β} {a b : ℕ}
    (hm : BitCost q m a) (hg : ∀ x, BitCost q (g x) b) :
    BitCost q (m.bind g) (a + b) := by
  induction hm with
  | ret x n => exact (hg x).mono (by omega)
  | query x k n _ ih => simpa [Prog.bind, Nat.add_assoc] using BitCost.query x _ (n + b) ih
  | draw bits k n _ ih => simpa [Prog.bind, Nat.add_assoc] using BitCost.draw bits _ (n + b) ih
  | work c m n _ ih => exact .work c _ _ ih

theorem BitBound.bitCost {m : Prog Q α} {b c T D : ℕ} (h : BitBound b m c)
    (hq : QueryBound m T) : BitCost (fun _ => D) m (b * c + T * D) := by
  induction h generalizing T with
  | ret a n => exact .ret a _
  | query x k n _ ih =>
    cases hq with
    | query _ _ t ht =>
      have h := BitCost.query x k (b * n + t * D) fun r => ih r (ht r)
      exact h.mono (by simp only [Nat.succ_mul]; omega)
  | draw k n _ ih =>
    cases hq with
    | choose _ _ _ ht =>
      have h := BitCost.draw b k (b * n + T * D) fun u => ih u (ht u)
      exact h.mono (by simp only [Nat.mul_succ]; omega)
  | work c m n _ ih =>
    cases hq with
    | work _ _ _ hm => exact .work c m _ (ih hm)

theorem BitCost.inline {q : Q → ℕ} {m : Prog Q α} {n : ℕ} (h : BitCost q m n)
    (S : Q → Prog Empty ℝ) (hS : ∀ x, BitCost (fun _ : Empty => 0) (S x) (q x)) :
    BitCost (fun _ : Empty => 0) (m.inline S) n := by
  induction h with
  | ret a n => exact .ret a n
  | query x k n _ ih => exact (hS x).bind ih
  | draw b k n _ ih => exact .draw b _ n ih
  | work c m n _ ih => exact .work c _ n ih

/-- Call-free programs have no oracle queries on any branch. -/
theorem queryBound_empty (m : Prog Empty α) : QueryBound m 0 := by
  induction m with
  | ret a => exact .ret a 0
  | query x k ih => exact x.elim
  | choose p k ih => exact .choose p k 0 ih
  | work c m ih => exact .work c m 0 ih

theorem BitBound.fairBitCost {m : Prog Empty α} {b c : ℕ} (h : BitBound b m c) :
    BitCost (fun _ : Empty => 0) m (b * c) := by
  simpa using h.bitCost (D := 0) (queryBound_empty m)

theorem BitCost.replicate {q : Q → ℕ} {m : Prog Q α} {c : ℕ}
    (h : BitCost q m c) (k : ℕ) : BitCost q (m.replicate k) (k * c) := by
  induction k with
  | zero => simpa [Prog.replicate] using BitCost.ret (queryCost := q) (α := Samples α 0) () 0
  | succ k ih =>
    exact (h.bind fun _ => ih.bind (b := 0) fun _ => .ret _ 0).mono (by simp only [Nat.succ_mul]; omega)

theorem BitCost.medianOf {q : Q → ℕ} {m : Prog Q ℝ} {c : ℕ}
    (h : BitCost q m c) (k : ℕ) : BitCost q (m.medianOf k) (k * c) := by
  exact ((h.replicate k).bind (b := 0) fun _ => .ret _ 0).mono (by omega)

/-- Replace continuations using an invariant proved on every program branch. -/
theorem Sat.bind_congr {A : ℝ → Prop} {Qp : Q → Prop} {R : α → Prop}
    {m : Prog Q α} (h : Sat A Qp R m) {g g' : α → Prog Q β}
    (hA : ∀ r, A r) (hg : ∀ a, R a → g a = g' a) : m.bind g = m.bind g' := by
  induction h with
  | ret a ha => exact hg a ha
  | query x k hx hk ih =>
    exact congrArg (Prog.query x) (funext fun r => ih r (hA r))
  | choose p k hk ih => exact congrArg (Prog.choose p) (funext ih)
  | work c m hm ih => exact congrArg (Prog.work c) ih

private def vectorConsEquiv (S : Type) (k : ℕ) :
    (Fin (k + 1) → S) ≃ S × (Fin k → S) where
  toFun v := (v 0, Fin.tail v)
  invFun v := Fin.cons v.1 v.2
  left_inv := Fin.cons_self_tail
  right_inv v := by cases v; rfl

/-- Repeated call-free runs have the independent product law of their seeds. -/
theorem exp_replicate_seeds (m : Prog Empty ℝ) (k : ℕ) (g : (Fin k → ℝ) → ℝ) :
    (m.replicate k).exp noOracle (fun xs => g (samplesToFn k xs)) =
      ∑ z : Fin k → m.toRand.Seed, (m.toRand.law.pow k).value z *
        g (fun i => m.toRand.value (z i)) := by
  induction k with
  | zero =>
    simp only [replicate, exp, Law.pow, Fintype.prod_empty, Fintype.sum_unique, one_mul]
    congr 1
    funext i
    exact i.elim0
  | succ k ih =>
    rw [replicate, exp_bind]
    have hrhs := Fintype.sum_equiv (vectorConsEquiv m.toRand.Seed k)
      (fun z => (m.toRand.law.pow (k + 1)).value z * g (fun i => m.toRand.value (z i)))
      (fun z => m.toRand.law.value z.1 * (m.toRand.law.pow k).value z.2 *
        g (Fin.cons (m.toRand.value z.1) (fun i => m.toRand.value (z.2 i)))) ?_
    · rw [hrhs, Fintype.sum_prod_type]
      have inner : ∀ x, ((m.replicate k).bind fun xs => ret (x, xs)).exp noOracle
          (fun xs => g (samplesToFn (k + 1) xs)) =
          ∑ z : Fin k → m.toRand.Seed, (m.toRand.law.pow k).value z *
            g (Fin.cons x (fun i => m.toRand.value (z i))) := by
        intro x
        rw [exp_bind]
        exact ih (fun v => g (Fin.cons x v))
      trans m.exp noOracle (fun x => ∑ z : Fin k → m.toRand.Seed,
        (m.toRand.law.pow k).value z * g (Fin.cons x (fun i => m.toRand.value (z i))))
      · exact congrArg (m.exp noOracle) (funext inner)
      rw [exp_eq_toRand]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro zs _
      ring
    · intro z
      have hcons : Fin.cons (m.toRand.value (z 0))
          (fun i => m.toRand.value (z i.succ)) = fun i => m.toRand.value (z i) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      simp only [Law.pow, Fin.prod_univ_succ, vectorConsEquiv, Equiv.coe_fn_mk,
        Fin.tail_def, hcons]

/-- Inlining a repeated query has exactly the law of oracle amplification. -/
theorem exp_inline_amplify (S : Q → Prog Empty ℝ) (k : ℕ) (m : Prog Q α) (f : α → ℝ) :
    (m.inline (fun x => (S x).medianOf k)).exp noOracle f =
      m.exp ((programOracle S).amplify k) f := by
  induction m with
  | ret a => rfl
  | query x cont ih =>
    change (((S x).medianOf k).bind fun r =>
      (cont r).inline (fun x => (S x).medianOf k)).exp noOracle f = _
    rw [exp_bind, medianOf, exp_bind]
    change ((S x).replicate k).exp noOracle (fun xs =>
      ((cont (median (samplesToFn k xs))).inline (fun x => (S x).medianOf k)).exp noOracle f) = _
    simp_rw [ih]
    exact exp_replicate_seeds (S x) k
      (fun v => (cont (median v)).exp ((programOracle S).amplify k) f)
  | choose p cont ih => simp only [inline, exp, ih]
  | work c m ih => exact ih

/-- An invariant on positive-probability branches of a call-free program. -/
inductive Supported (P : α → Prop) : Prog Empty α → Prop
  | ret (a : α) : P a → Supported P (.ret a)
  | choose {ι : Type} [Fintype ι] (p : Law ι) (k : ι → Prog Empty α) :
      (∀ i, p.value i ≠ 0 → Supported P (k i)) → Supported P (.choose p k)
  | work (c : ℕ) (m : Prog Empty α) : Supported P m → Supported P (.work c m)

theorem Sat.supported {P : α → Prop} {m : Prog Empty α}
    (h : Sat (fun _ => True) (fun _ => True) P m) : Supported P m := by
  induction h with
  | ret a ha => exact .ret a ha
  | query x k hx hk ih => exact x.elim
  | choose p k hk ih => exact .choose p k fun i _ => ih i
  | work c m hm ih => exact .work c m ih

theorem Supported.bind {P : α → Prop} {R : β → Prop} {m : Prog Empty α}
    (h : Supported P m) {g : α → Prog Empty β}
    (hg : ∀ a, P a → Supported R (g a)) : Supported R (m.bind g) := by
  induction h with
  | ret a ha => exact hg a ha
  | choose p k hk ih => exact .choose p _ ih
  | work c m hm ih => exact .work c _ ih

theorem Supported.imp {P R : α → Prop} {m : Prog Empty α}
    (h : Supported P m) (hPR : ∀ a, P a → R a) : Supported R m := by
  induction h with
  | ret a ha => exact .ret a (hPR a ha)
  | choose p k hk ih => exact .choose p _ ih
  | work c m hm ih => exact .work c _ ih

theorem Supported.exp_congr {P : α → Prop} {m : Prog Empty α} (h : Supported P m)
    {f g : α → ℝ} (hfg : ∀ a, P a → f a = g a) : m.exp noOracle f = m.exp noOracle g := by
  induction h with
  | ret a ha => exact hfg a ha
  | choose p k hk ih =>
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p.value i = 0
    · simp [hi]
    · rw [ih i hi]
  | work c m hm ih => exact ih

/-- Law equality is preserved by a continuation, with its equality needed only
on the supported values of the left-hand program. -/
theorem Supported.exp_bind_congr {P : α → Prop} {m m' : Prog Empty α}
    (h : Supported P m) (heq : ∀ f, m.exp noOracle f = m'.exp noOracle f)
    {g g' : α → Prog Empty β} (hg : ∀ a, P a → ∀ f,
      (g a).exp noOracle f = (g' a).exp noOracle f) (f : β → ℝ) :
    (m.bind g).exp noOracle f = (m'.bind g').exp noOracle f := by
  rw [exp_bind, exp_bind]
  exact (h.exp_congr (fun a ha => hg a ha f)).trans (heq _)

end Prog
end
end DirectedCycleFPRAS
