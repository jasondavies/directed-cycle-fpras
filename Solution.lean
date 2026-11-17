module

public import DirectedCycleFPRAS

@[expose] public section

/-! Proved implementations of the independent statements in Challenge.lean. -/

open scoped BigOperators
open Classical

namespace DirectedCycleFPRAS

namespace Publication

/-- Alternatives used by `inner` repetitions of Algorithm S on the split graph.
The sample budget is `4096*(n+1)^3*m*(m+1)^2`. This counts finite choices,
not machine instructions. -/
def oracleChoices (n m inner : ℕ) : ℕ :=
  let M := 4096*(n+1)^3*m*(m+1)^2
  inner*((n+1)*(M*((n+1+1)+((M+1)+((m+1)+(n+1+1)*(2*m))))))

/-- Number of fair input bits for counting with relative error `1/r` and
failure at most `2⁻ᵈ`, using a supplied feedback set of size `k`. -/
def countBits (n m k r d : ℕ) : ℕ :=
  let D := 64*k*r^2
  let T := k+2*m*D
  let inner := 6*(Nat.clog 2 (max 1 T)+4)
  let A := 6*(d+1)*(T*oracleChoices n m inner+D*(k+2*m+2))
  (Nat.clog 2 (max 1 A)+(d+1))*A

/-- Number of fair input bits for conditional sampling within total variation
`2⁻ᵈ`. The proposal cap is `4*k*(d+2)`. -/
def sampleBits (n m k d : ℕ) : ℕ :=
  let D := 4*k*(d+2)
  let T := k+2*m*D
  let inner := 6*(Nat.clog 2 (max 1 T)+(d+2))
  let A := T*oracleChoices n m inner+D*(k+2*m+2)
  (Nat.clog 2 (max 1 A)+(d+2))*A

/-- The rational estimate returned by the counting implementation on a finite tape.
The Solution supplies the actual algorithm; its accuracy and exact-zero behavior
are constrained by the theorems below. `w` enumerates the feedback set. -/
def count {n m k : ℕ} (G : Digraph (Fin n) (Fin m)) (U : Finset (Fin n))
    (w : Fin k ≃ U) (p : Fin m → ℚ) (r d : ℕ)
    (tape : Fin (countBits n m k r d) → Bool) : ℚ := ((G.executableFPRAS U (Equiv.refl _) (Equiv.refl _) w p r d).run
    (BitProg.zeroExtend tape) 0).1

/-- The retained configuration returned by the conditional sampler on a finite tape.
The Solution supplies the actual algorithm. Accuracy is asserted only when
cyclicity has positive probability; `hk` supplies a nonempty witness family. -/
def sample {n m k : ℕ} (G : Digraph (Fin n) (Fin m)) (U : Finset (Fin n))
    (w : Fin k ≃ U) (hk : 0<k) (p : Fin m → ℚ) (d : ℕ)
    (tape : Fin (sampleBits n m k d) → Bool) : Fin m → Bool := ((G.executableConditionalSampler U (Equiv.refl _) (Equiv.refl _) w hk p d).run
    (BitProg.zeroExtend tape) 0).1

/-- Cycle membership of a vertex is a two-terminal reliability event on the
split graph, without duplicating any random edge variable. -/
theorem vertex_reliability {V E : Type} [DecidableEq V] (G : Digraph V E)
    (v : V) (S : Set E) :
    Relation.TransGen (G.Adj S) v v ↔
      Relation.ReflTransGen ((G.splitVertex v).Adj S) (some v) none := by exact G.vertexWitness_iff_split v S

/-- Every cycle in the support meets a vertex of the supplied feedback set. -/
theorem feedback_cover {V E : Type} [DecidableEq V] (G : Digraph V E)
    (U : Finset V) (S : Set E) (hU : G.Feedback U S) :
    G.Cyclic S ↔ ∃ v ∈ U, Relation.TransGen (G.Adj S) v v := by exact G.feedback_cover U S hU

/-- Relative counting accuracy on a uniformly random finite fair-bit tape.
All reliability calls are implemented by Algorithm S; there is no oracle premise. -/
theorem count_correct {n m k : ℕ} (G : Digraph (Fin n) (Fin m)) (U : Finset (Fin n))
    (w : Fin k ≃ U) (p : Fin m → ℚ) (hp : ∀ e, 0 ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1)
    (hU : G.Feedback U {e | 0<(p e : ℝ)}) (r d : ℕ) (hr : 0<r) :
    let Z := eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (Digraph.retained ω))
    let N := countBits n m k r d
    (∑ tape : Fin N → Bool, (1/(2 : ℝ)^N)*
      (if (1/(r : ℝ))*Z < |(count G U w p r d tape : ℝ)-Z| then 1 else 0)) ≤
      (1/2 : ℝ)^d := by exact G.executableFPRAS_correct U (Equiv.refl _) (Equiv.refl _) w p hp hU r d hr

/-- If the true probability is zero, every tape returns exactly zero. -/
theorem count_zero {n m k : ℕ} (G : Digraph (Fin n) (Fin m)) (U : Finset (Fin n))
    (w : Fin k ≃ U) (p : Fin m → ℚ) (hp : ∀ e, 0 ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1)
    (r d : ℕ)
    (hz : eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (Digraph.retained ω)) = 0)
    (tape : Fin (countBits n m k r d) → Bool) : count G U w p r d tape = 0 := by
  unfold count
  rw [G.executableFPRAS_zero U (Equiv.refl _) (Equiv.refl _) w p hp r d hz]
  rfl

/-- Conditional sampling within total variation `2⁻ᵈ`, expressed by all tests
with values in `[0,1]`, on the finite space of retained edge configurations. -/
theorem sample_correct {n m k : ℕ} (G : Digraph (Fin n) (Fin m)) (U : Finset (Fin n))
    (w : Fin k ≃ U) (hk : 0<k) (p : Fin m → ℚ)
    (hp : ∀ e, 0 ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1)
    (hU : G.Feedback U {e | 0<(p e : ℝ)})
    (hZ : 0<eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (Digraph.retained ω)))
    (d : ℕ) (f : (Fin m → Bool) → ℝ) (hf0 : ∀ x, 0≤f x) (hf1 : ∀ x, f x≤1) :
    let N := sampleBits n m k d
    |(∑ tape : Fin N → Bool, (1/(2 : ℝ)^N)*f (sample G U w hk p d tape))-
      (∑ ω, if G.Cyclic (Digraph.retained ω) then edgeWeight (fun e => (p e : ℝ)) ω*f ω else 0)/
        eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (Digraph.retained ω))| ≤
      (1/2 : ℝ)^d := by
  exact G.executableConditionalSampler_correct U (Equiv.refl _) (Equiv.refl _)
    w hk p hp hU hZ d f hf0 hf1

/-- The exact independent-set reduction: acyclicity probability in the gate
construction equals the independent-set count divided by `2^|V|`. The complexity
theoretic hardness of counting independent sets is an external result. -/
theorem acyclicity_probability {V : Type} [Fintype V] (H : V → V → Prop)
    (hsym : ∀ ⦃u v⦄, H u v → H v u) :
    eventMass (AcyclicityReduction.retention H)
      (fun ω => ¬ (AcyclicityReduction.graph H).Cyclic (Digraph.retained ω)) =
    (Fintype.card {selected : V → Bool // AcyclicityReduction.Independent H selected} : ℝ)/
      (2 : ℝ)^Fintype.card V := by exact AcyclicityReduction.edge_retention_probability H hsym

end Publication
end DirectedCycleFPRAS
