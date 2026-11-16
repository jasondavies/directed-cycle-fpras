module

public import DirectedCycleFPRAS.FirstOpen
public import DirectedCycleFPRAS.ProgramComposition

@[expose] public section

/-! Deferred decisions for finite adaptive explorations of independent edges.
The read-once invariant is checked on every branch, including zero-mass ones. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false

inductive EdgeTree (E α : Type) where
  | ret : α → EdgeTree E α
  | read : E → (Bool → EdgeTree E α) → EdgeTree E α

namespace EdgeTree
variable {E α β : Type}

def bind : EdgeTree E α → (α → EdgeTree E β) → EdgeTree E β
  | .ret a, k => k a
  | .read e k, g => .read e (fun b => (k b).bind g)

def eval (ω : E → Bool) : EdgeTree E α → α
  | .ret a => a
  | .read e k => eval ω (k (ω e))

def run (p : E → ℝ) (pre : E → Option Bool) : EdgeTree E α → Prog Empty α
  | .ret a => .ret a
  | .read e k => ((pre e).elim (Prog.choose (Digraph.coin (p e)) Prog.ret) Prog.ret).bind
      (fun b => run p pre (k b))

theorem run_bind (p : E → ℝ) (pre : E → Option Bool) (t : EdgeTree E α) (g : α → EdgeTree E β) :
    (t.bind g).run p pre = (t.run p pre).bind (fun a => (g a).run p pre) := by
  induction t with
  | ret a => rfl
  | read e k ih =>
    simp only [bind, run, ih]
    cases pre e <;> rfl

theorem eval_bind (ω : E → Bool) (t : EdgeTree E α) (g : α → EdgeTree E β) :
    (t.bind g).eval ω = (g (t.eval ω)).eval ω := by
  induction t with
  | ret a => rfl
  | read e k ih => exact ih (ω e)

/-- A fully specified graph leaves no random choices. -/
theorem run_fixed (t : EdgeTree E α) (p : E → ℝ) (ω : E → Bool) :
    t.run p (fun e => some (ω e)) = Prog.ret (t.eval ω) := by
  induction t with
  | ret a => rfl
  | read e k ih => exact ih (ω e)

variable [DecidableEq E]

/-- `S` contains the edges already read. The postcondition can mention both
the final read set and the returned value, so sequential composition preserves
freshness without discarding information. -/
inductive Once (P : Finset E → α → Prop) : Finset E → EdgeTree E α → Prop
  | ret (S : Finset E) (a : α) : P S a → Once P S (.ret a)
  | read (S : Finset E) (e : E) (k : Bool → EdgeTree E α) : e ∉ S →
      (∀ b, Once P (insert e S) (k b)) → Once P S (.read e k)

theorem Once.bind {P : Finset E → α → Prop} {R : Finset E → β → Prop}
    {S : Finset E} {t : EdgeTree E α} (h : Once P S t) (g : α → EdgeTree E β)
    (hg : ∀ S a, P S a → Once R S (g a)) : Once R S (t.bind g) := by
  induction h with
  | ret S a ha => exact hg S a ha
  | read S e k he hk ih => exact .read S e _ he ih

theorem Once.imp {P R : Finset E → α → Prop} {S : Finset E} {t : EdgeTree E α}
    (h : Once P S t) (hPR : ∀ S a, P S a → R S a) : Once R S t := by
  induction h with
  | ret S a ha => exact .ret S a (hPR S a ha)
  | read S e k he hk ih => exact .read S e k he ih

/-- The read-once invariant's postcondition holds for every fixed graph. -/
theorem Once.eval_post {P : Finset E → α → Prop} {S : Finset E} {t : EdgeTree E α}
    (h : Once P S t) (ω : E → Bool) : ∃ S', P S' (t.eval ω) := by
  induction h with
  | ret S a ha => exact ⟨S,ha⟩
  | read S e k he hk ih => exact ih (ω e)

/-- Already exposed coordinates are irrelevant to the remaining program. -/
theorem Once.run_congr {P : Finset E → α → Prop} {S : Finset E} {t : EdgeTree E α}
    (h : Once P S t) (p q : E → ℝ) (pre : E → Option Bool)
    (hpq : ∀ e, e ∉ S → p e = q e) : t.run p pre = t.run q pre := by
  induction h with
  | ret S a ha => rfl
  | read S e k he hk ih =>
    simp only [run, hpq e he]
    congr 1
    funext b
    exact ih b (fun j hj => hpq j (fun h => hj (Finset.mem_insert_of_mem h)))

theorem coin_expectation (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    (∑ b, (Digraph.coin p).value b*f b) = p*f true+(1-p)*f false := by
  have h0 (b : Bool) : 0 ≤ (if b then p else 1-p) := by cases b <;> simp_all
  have hs : 0 < ∑ b : Bool, (if b then p else 1-p) := by simp
  simp_rw [Digraph.coin, normLaw_value _ _ h0 hs]
  simp

variable [Fintype E]

/-- Product-law decomposition at the next adaptively selected edge. -/
theorem weighted_read (p : E → ℝ) (e : E) (k : Bool → EdgeTree E α) (f : α → ℝ) :
    (∑ ω, edgeWeight p ω*f ((EdgeTree.read e k).eval ω)) =
      p e*(∑ ω, edgeWeight (pin p e true) ω*f ((k true).eval ω)) +
      (1-p e)*(∑ ω, edgeWeight (pin p e false) ω*f ((k false).eval ω)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  rw [edgeWeight_eq_mul_rest p e, edgeWeight_pin, edgeWeight_pin]
  cases h : ω e <;> simp [eval, h] <;> ring

/-- Reading independent edges lazily has exactly the pushforward law of a
single product-distributed retained graph. No approximation or conditioning
on a positive-probability transcript is used. -/
theorem Once.deferred {P : Finset E → α → Prop} {S : Finset E} {t : EdgeTree E α}
    (h : Once P S t) (p : E → ℝ) (hp : Prob01 p) (f : α → ℝ) :
    (t.run p (fun _ => none)).exp noOracle f = ∑ ω, edgeWeight p ω*f (t.eval ω) := by
  induction h generalizing p with
  | ret S a ha => simp [run, eval, Prog.exp, ← Finset.sum_mul, edgeWeight_sum]
  | read S e k he hk ih =>
    rw [weighted_read]
    change (∑ b, (Digraph.coin (p e)).value b * ((k b).run p (fun _ => none)).exp noOracle f) = _
    rw [coin_expectation _ (hp e).1 (hp e).2]
    have hc (b : Bool) : (k b).run p (fun _ => none) = (k b).run (pin p e b) (fun _ => none) := by
      apply (hk b).run_congr
      intro j hj
      exact (pin_of_ne p b (fun heq => hj (by simp [heq]))).symm
    rw [hc true, hc false, ih true _ (prob01_pin hp e true), ih false _ (prob01_pin hp e false)]

/-- Forcing some coordinates is the same as replacing their retention
parameters by zero or one, at the level of the complete output law. -/
theorem run_force (t : EdgeTree E α) (p : E → ℝ)
    (pre : E → Option Bool) (f : α → ℝ) :
    (t.run p pre).exp noOracle f = (t.run (forceProb p pre) (fun _ => none)).exp noOracle f := by
  induction t with
  | ret a => rfl
  | read e k ih =>
    simp only [run, Prog.exp_bind]
    cases he : pre e with
    | none =>
      simp only [Option.elim_none, Prog.exp]
      have hp' : forceProb p pre e = p e := by simp [forceProb, he]
      rw [hp']
      exact Finset.sum_congr rfl (fun b _ => by rw [ih b])
    | some b =>
      simp only [Option.elim_some, Option.elim_none, Prog.exp]
      have hp' : forceProb p pre e = if b then 1 else 0 := by simp [forceProb, he]
      rw [hp']
      rw [coin_expectation _ (by cases b <;> norm_num) (by cases b <;> norm_num)]
      cases b <;> simpa using ih _

theorem forceProb_prob01 (p : E → ℝ) (hp : Prob01 p) (pre : E → Option Bool) :
    Prob01 (forceProb p pre) := by
  intro e
  cases he : pre e with
  | none => simpa [forceProb, he] using hp e
  | some b => cases b <;> simp [forceProb, he]

theorem Once.deferred_forced {P : Finset E → α → Prop} {S : Finset E} {t : EdgeTree E α}
    (h : Once P S t) (p : E → ℝ) (hp : Prob01 p) (pre : E → Option Bool) (f : α → ℝ) :
    (t.run p pre).exp noOracle f = ∑ ω, edgeWeight (forceProb p pre) ω*f (t.eval ω) := by
  rw [run_force t p pre f]
  exact h.deferred _ (forceProb_prob01 p hp pre) f

end EdgeTree
end
end DirectedCycleFPRAS
