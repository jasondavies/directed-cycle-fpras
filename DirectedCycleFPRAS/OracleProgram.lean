module

public import DirectedCycleFPRAS.IndependentSamples

@[expose] public section

/-!
# Randomized programs with a randomized oracle

A program is a finite decision tree whose nodes are oracle queries with real
answers and internal random choices. The next query may depend on the entire
history, so adaptivity is built in. An oracle answers each query using a fresh
finite random seed, independently of everything that happened before; this is
what the recursive definition of `Prog.exp` expresses.

The main result is `Prog.exp_le_repair`: a program making at most `T` queries
cannot distinguish an oracle from its repaired version, in which every
unacceptable answer is replaced by a designated acceptable one, except with
probability `T` times the per-call failure probability. No conditioning on the
success of all calls is involved.
-/

namespace DirectedCycleFPRAS

open scoped BigOperators
open Classical

noncomputable section

/-- Normalise a weight vector into a law. If the weights are not nonnegative
with positive sum, fall back to a point mass on the default alternative. -/
def normLaw {ι : Type} [Fintype ι] (w : ι → ℝ) (d : ι) : Law ι :=
  if h : (∀ i, 0 ≤ w i) ∧ 0 < ∑ i, w i then
    { value := fun i => w i / ∑ j, w j
      nonneg := fun i => div_nonneg (h.1 i) h.2.le
      sum_one := by rw [← Finset.sum_div, div_self (ne_of_gt h.2)] }
  else
    { value := fun i => if i = d then 1 else 0
      nonneg := fun i => by split_ifs <;> norm_num
      sum_one := by simp }

theorem normLaw_value {ι : Type} [Fintype ι] (w : ι → ℝ) (d : ι)
    (h0 : ∀ i, 0 ≤ w i) (hpos : 0 < ∑ i, w i) (i : ι) :
    (normLaw w d).value i = w i / ∑ j, w j := by
  rw [normLaw, dite_eq_left ⟨h0, hpos⟩]

/-- A randomized oracle: each call draws a fresh seed from a finite law that
may depend on the query, and returns a real answer. -/
structure Oracle (Q : Type) where
  Seed : Type
  [fintype : Fintype Seed]
  law : Q → Law Seed
  answer : Q → Seed → ℝ

attribute [instance] Oracle.fintype

/-- Randomized oracle programs with queries in `Q` and results in `α`. -/
inductive Prog (Q : Type) (α : Type) : Type 1 where
  | ret : α → Prog Q α
  | query : Q → (ℝ → Prog Q α) → Prog Q α
  | choose : {ι : Type} → [Fintype ι] → Law ι → (ι → Prog Q α) → Prog Q α
  /-- Charge the given number of local operations. It has no effect on the
  result; it exists so that local computation can be counted. -/
  | work : ℕ → Prog Q α → Prog Q α

namespace Prog

variable {Q α β : Type}

/-- Sequential composition. -/
def bind : Prog Q α → (α → Prog Q β) → Prog Q β
  | .ret a, g => g a
  | .query x k, g => .query x fun r => (k r).bind g
  | @Prog.choose _ _ ι inst p k, g => @Prog.choose _ _ ι inst p fun i => (k i).bind g
  | .work c m, g => .work c (m.bind g)

/-- Expected value of a function of the result, when every query is answered
with fresh oracle randomness. -/
def exp (O : Oracle Q) : Prog Q α → (α → ℝ) → ℝ
  | .ret a, f => f a
  | .query x k, f => ∑ s, (O.law x).value s * (k (O.answer x s)).exp O f
  | @Prog.choose _ _ _ _ p k, f => ∑ i, p.value i * (k i).exp O f
  | .work _ m, f => m.exp O f

theorem exp_bind (O : Oracle Q) (m : Prog Q α) (g : α → Prog Q β) (f : β → ℝ) :
    (m.bind g).exp O f = m.exp O (fun a => (g a).exp O f) := by
  induction m with
  | ret a => rfl
  | query x k ih => simp only [bind, exp, ih]
  | choose p k ih => simp only [bind, exp, ih]
  | work c m ih => simp only [bind, exp, ih]

theorem exp_mono (O : Oracle Q) (m : Prog Q α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    m.exp O f ≤ m.exp O g := by
  induction m with
  | ret a => exact h a
  | query x k ih =>
    exact Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (ih _) ((O.law x).nonneg s)
  | choose p k ih =>
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ih _) (p.nonneg i)
  | work c m ih => exact ih

theorem exp_const (O : Oracle Q) (m : Prog Q α) (c : ℝ) : m.exp O (fun _ => c) = c := by
  induction m with
  | ret a => rfl
  | query x k ih => simp only [exp, ih, ← Finset.sum_mul, Law.sum_one, one_mul]
  | choose p k ih => simp only [exp, ih, ← Finset.sum_mul, Law.sum_one, one_mul]
  | work c m ih => exact ih

theorem exp_nonneg (O : Oracle Q) (m : Prog Q α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ m.exp O f := by
  have := exp_mono O m h
  rwa [exp_const] at this

theorem exp_le_of_le (O : Oracle Q) (m : Prog Q α) {f : α → ℝ} {c : ℝ} (h : ∀ a, f a ≤ c) :
    m.exp O f ≤ c := by
  have := exp_mono O m h
  rwa [exp_const] at this

theorem exp_mul_left (O : Oracle Q) (m : Prog Q α) (c : ℝ) (f : α → ℝ) :
    m.exp O (fun a => c * f a) = c * m.exp O f := by
  induction m with
  | ret a => rfl
  | query x k ih =>
    simp only [exp, ih, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  | choose p k ih =>
    simp only [exp, ih, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  | work c m ih => exact ih

theorem exp_sum (O : Oracle Q) (m : Prog Q α) {ι : Type} (s : Finset ι) (f : ι → α → ℝ) :
    m.exp O (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, m.exp O (f i) := by
  induction m with
  | ret a => rfl
  | query x k ih =>
    simp only [exp, ih, Finset.mul_sum]
    rw [Finset.sum_comm]
  | choose p k ih =>
    simp only [exp, ih, Finset.mul_sum]
    rw [Finset.sum_comm]
  | work c m ih => exact ih

/-- The output law of a program with finitely many possible results. -/
def law (O : Oracle Q) {Ω : Type} [Fintype Ω] (m : Prog Q Ω) : Law Ω where
  value ω := m.exp O (fun a => if a = ω then 1 else 0)
  nonneg ω := exp_nonneg O m fun a => by split_ifs <;> norm_num
  sum_one := by
    rw [← exp_sum]
    simp [exp_const]

theorem exp_eq_sum_law (O : Oracle Q) {Ω : Type} [Fintype Ω] (m : Prog Q Ω) (g : Ω → ℝ) :
    m.exp O g = ∑ ω, (m.law O).value ω * g ω := by
  have h : ∀ ω, (m.law O).value ω * g ω =
      m.exp O (fun a => g ω * if a = ω then 1 else 0) := by
    intro ω
    rw [exp_mul_left, mul_comm]
    rfl
  simp_rw [h]
  rw [← exp_sum]
  congr 1
  ext a
  simp

/-- Independent repetitions of a program; every repetition makes its own
oracle calls with fresh randomness. -/
def replicate {Ω : Type} (m : Prog Q Ω) : (n : ℕ) → Prog Q (Samples Ω n)
  | 0 => .ret ()
  | n + 1 => m.bind fun x => (replicate m n).bind fun xs => .ret (x, xs)

/-- Repetitions of a program are distributed as the explicit product law of
its output law. -/
theorem exp_replicate (O : Oracle Q) {Ω : Type} [Fintype Ω] (m : Prog Q Ω) (n : ℕ)
    (g : Samples Ω n → ℝ) :
    (m.replicate n).exp O g = ∑ xs, ((m.law O).samples n).value xs * g xs := by
  induction n with
  | zero =>
    change g () = ∑ xs : Unit, (1 : ℝ) * g xs
    rw [Fintype.sum_unique, one_mul]
  | succ n ih =>
    have key : ∀ g : Ω × Samples Ω n → ℝ,
        (m.bind fun x => (replicate m n).bind fun xs => .ret (x, xs)).exp O g =
          ∑ xs : Ω × Samples Ω n,
            ((m.law O).value xs.1 * ((m.law O).samples n).value xs.2) * g xs := by
      intro g
      rw [exp_bind, Fintype.sum_prod_type, exp_eq_sum_law]
      apply Finset.sum_congr rfl
      intro x _
      rw [exp_bind, ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro xs _
      simp only [exp]
      ring
    exact key g

/-- Ask the oracle only when the exact feasibility test `c` succeeds;
otherwise continue with the answer zero and make no call. The test is charged
as one local operation. -/
def guarded (c : Prop) (x : Q) (k : ℝ → Prog Q α) : Prog Q α :=
  .work 1 (if c then .query x k else k 0)

theorem exp_guarded (O : Oracle Q) (c : Prop) (x : Q) (k : ℝ → Prog Q α) (f : α → ℝ) :
    (guarded c x k).exp O f =
      ∑ s, (O.law x).value s * (k (if c then O.answer x s else 0)).exp O f := by
  by_cases h : c
  · simp only [guarded, ite_eq_left h]
    rfl
  · simp only [guarded, ite_eq_right h, exp, ← Finset.sum_mul, Law.sum_one, one_mul]

/-- Every execution path makes at most the stated number of oracle calls. -/
inductive QueryBound : Prog Q α → ℕ → Prop
  | ret (a : α) (n : ℕ) : QueryBound (.ret a) n
  | query (x : Q) (k : ℝ → Prog Q α) (n : ℕ) :
      (∀ r, QueryBound (k r) n) → QueryBound (.query x k) (n + 1)
  | choose {ι : Type} [Fintype ι] (p : Law ι) (k : ι → Prog Q α) (n : ℕ) :
      (∀ i, QueryBound (k i) n) → QueryBound (.choose p k) n
  | work (c : ℕ) (m : Prog Q α) (n : ℕ) : QueryBound m n → QueryBound (.work c m) n

theorem QueryBound.mono {m : Prog Q α} {a b : ℕ} (h : QueryBound m a) (hab : a ≤ b) :
    QueryBound m b := by
  induction h generalizing b with
  | ret a n => exact .ret a b
  | query x k n _ ih =>
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    exact .query x k b' fun r => ih r (by omega)
  | choose p k n _ ih => exact .choose p k b fun i => ih i hab
  | work c m n _ ih => exact .work c m b (ih hab)

theorem QueryBound.bind {m : Prog Q α} {g : α → Prog Q β} {a b : ℕ}
    (hm : QueryBound m a) (hg : ∀ x, QueryBound (g x) b) :
    QueryBound (m.bind g) (a + b) := by
  induction hm with
  | ret x n => exact (hg x).mono (by omega)
  | query x k n _ ih =>
    have hn : n + 1 + b = (n + b) + 1 := by omega
    rw [hn]
    exact .query x _ _ ih
  | choose p k n _ ih => exact .choose p _ _ ih
  | work c m n _ ih => exact .work c _ _ ih

theorem QueryBound.guarded {c : Prop} {x : Q} {k : ℝ → Prog Q α} {n : ℕ}
    (h : ∀ r, QueryBound (k r) n) : QueryBound (Prog.guarded c x k) (n + 1) := by
  unfold Prog.guarded
  refine .work _ _ _ ?_
  split_ifs
  · exact .query x k n h
  · exact (h 0).mono (by omega)

theorem QueryBound.replicate {Ω : Type} {m : Prog Q Ω} {a : ℕ} (h : QueryBound m a)
    (n : ℕ) : QueryBound (m.replicate n) (n * a) := by
  induction n with
  | zero => exact .ret _ _
  | succ n ih =>
    have hb : QueryBound (m.replicate (n + 1)) (a + (n * a + 0)) :=
      h.bind fun x => ih.bind fun xs => .ret _ 0
    exact hb.mono (by rw [Nat.succ_mul]; omega)

end Prog

/-- Replace every unacceptable answer by a designated acceptable one. The
seed law is unchanged, so the repaired oracle is still randomized. -/
def Oracle.repair {Q : Type} (O : Oracle Q) (good : Q → ℝ → Prop) (fix : Q → ℝ) : Oracle Q where
  Seed := O.Seed
  fintype := O.fintype
  law := O.law
  answer x s := if good x (O.answer x s) then O.answer x s else fix x

theorem Oracle.repair_good {Q : Type} (O : Oracle Q) (good : Q → ℝ → Prop) (fix : Q → ℝ)
    (hfix : ∀ x, good x (fix x)) (x : Q) (s : O.Seed) :
    good x ((O.repair good fix).answer x s) := by
  change good x (if good x (O.answer x s) then O.answer x s else fix x)
  split_ifs with h
  · exact h
  · exact hfix x

namespace Prog

variable {Q α : Type}

/-- Good-oracle coupling for adaptive queries. If each call returns an
unacceptable answer with probability at most `γ`, a program making at most `T`
calls has expected `[0,1]`-valued loss at most `T * γ` above its loss with the
repaired oracle. The proof is the union bound along the execution tree; each
query is a fixed input to a fresh oracle run given the history. -/
theorem exp_le_repair (O : Oracle Q) (good : Q → ℝ → Prop) (fix : Q → ℝ) {γ : ℝ}
    (hγ0 : 0 ≤ γ)
    (hγ : ∀ x, (∑ s, if good x (O.answer x s) then 0 else (O.law x).value s) ≤ γ)
    {f : α → ℝ} (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1)
    {m : Prog Q α} {T : ℕ} (hT : QueryBound m T) :
    m.exp O f ≤ m.exp (O.repair good fix) f + T * γ := by
  induction hT with
  | ret a n =>
    have : 0 ≤ (n : ℝ) * γ := mul_nonneg (Nat.cast_nonneg n) hγ0
    change f a ≤ f a + n * γ
    linarith
  | query x k n _ ih =>
    have hnγ : 0 ≤ (n : ℝ) * γ := mul_nonneg (Nat.cast_nonneg n) hγ0
    have hterm : ∀ s : O.Seed, (O.law x).value s * (k (O.answer x s)).exp O f ≤
        (O.law x).value s *
          ((k ((O.repair good fix).answer x s)).exp (O.repair good fix) f + n * γ) +
        (if good x (O.answer x s) then 0 else (O.law x).value s) := by
      intro s
      have hρ := (O.law x).nonneg s
      by_cases hg : good x (O.answer x s)
      · have ha : (O.repair good fix).answer x s = O.answer x s := by
          change (if good x (O.answer x s) then O.answer x s else fix x) = _
          rw [ite_eq_left hg]
        rw [ha, ite_eq_left hg, add_zero]
        exact mul_le_mul_of_nonneg_left (ih _) hρ
      · rw [ite_eq_right hg]
        have h1 : (k (O.answer x s)).exp O f ≤ 1 := exp_le_of_le O _ hf1
        have h0 : 0 ≤ (k ((O.repair good fix).answer x s)).exp (O.repair good fix) f :=
          exp_nonneg _ _ hf0
        have hmul := mul_le_mul_of_nonneg_left h1 hρ
        have hrest := mul_nonneg hρ (add_nonneg h0 hnγ)
        linarith
    calc (Prog.query x k).exp O f
        = ∑ s : O.Seed, (O.law x).value s * (k (O.answer x s)).exp O f := rfl
      _ ≤ ∑ s : O.Seed, ((O.law x).value s *
            ((k ((O.repair good fix).answer x s)).exp (O.repair good fix) f + n * γ) +
          (if good x (O.answer x s) then 0 else (O.law x).value s)) :=
        Finset.sum_le_sum fun s _ => hterm s
      _ = (Prog.query x k).exp (O.repair good fix) f + n * γ +
          ∑ s : O.Seed, (if good x (O.answer x s) then 0 else (O.law x).value s) := by
        rw [Finset.sum_add_distrib]
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, Law.sum_one, one_mul]
        rfl
      _ ≤ (Prog.query x k).exp (O.repair good fix) f + (n + 1 : ℕ) * γ := by
        push_cast
        linarith [hγ x]
  | choose p k n _ ih =>
    calc (Prog.choose p k).exp O f = ∑ i, p.value i * (k i).exp O f := rfl
      _ ≤ ∑ i, p.value i * ((k i).exp (O.repair good fix) f + n * γ) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ih i) (p.nonneg i)
      _ = (Prog.choose p k).exp (O.repair good fix) f + n * γ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, Law.sum_one, one_mul]
        rfl
  | work c m n _ ih => exact ih

end Prog

end
end DirectedCycleFPRAS
