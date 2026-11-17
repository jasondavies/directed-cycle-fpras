module

public import Mathlib

@[expose] public section

/-!
# Directed-cycle counting and conditional sampling

This is the independent statement surface for Palomar. Graphs allow loops and
parallel arcs. Edge retention is independent with rational probabilities.
The compared algorithms return a relative estimate and a sample conditioned
on cyclicity, using the explicit finite fair-bit budgets below. A supplied
valid feedback vertex set controls overlap; validity is a theorem precondition,
not checked by these frontends. All vertices always give a valid set.
The vertex-splitting identity and the independent-set/acyclicity reduction
are also compared.

Only `count` and `sample` are definition holes: the Solution supplies the
executable algorithms and proves their stated laws. All graph notions,
probabilities, and bit budgets have explicit definitions here. The statement
uses numbered finite vertices and edges; arbitrary finite graphs can be
numbered, and the library theorems accept arbitrary finite types and orders.

Polynomial machine runtime is justified in the paper, not asserted by this
interface. Probability and tape-length bounds alone do not exclude exponential
computation. Comparator checks the supplied executable definitions and their
laws, but does not certify an FPRAS runtime bound. The Algorithm S accuracy
proof is a dependency of the counting and sampling proofs.
Independent-set inapproximability is cited, not assumed as an
axiom or proved here. See formalization.yaml and validation/FORMALIZATION.md.
-/

open scoped BigOperators
open Classical

namespace DirectedCycleFPRAS

/-- A directed multigraph: edge identities are separate from endpoints. -/
structure Digraph (V E : Type*) where
  source : E → V
  target : E → V

namespace Digraph
/-- Adjacency using only edges in `S`. -/
def Adj {V E : Type*} (G : Digraph V E) (S : Set E) (u v : V) : Prop :=
  ∃ e ∈ S, G.source e = u ∧ G.target e = v

/-- A nonempty closed directed walk, equivalently a directed cycle. -/
def Cyclic {V E : Type*} (G : Digraph V E) (S : Set E) : Prop :=
  ∃ v, Relation.TransGen (G.Adj S) v v

/-- Edge configurations are Boolean functions; `true` means retained. -/
def retained {E : Type} (ω : E → Bool) : Set E := {e | ω e = true}

/-- Deleting the supplied vertices leaves no cycle in the support `S`. -/
def Feedback {V E : Type} (G : Digraph V E)
    (U : Finset V) (S : Set E) : Prop :=
  ¬ G.Cyclic {e | e ∈ S ∧ G.source e ∉ U ∧ G.target e ∉ U}

/-- Split `v` into outgoing `some v` and incoming `none`, preserving edge identities. -/
def splitVertex {V E : Type} [DecidableEq V] (G : Digraph V E) (v : V) :
    Digraph (Option V) E where
  source e := some (G.source e)
  target e := if G.target e = v then none else some (G.target e)
end Digraph

/-- Independent retention weight of one configuration. -/
noncomputable def edgeWeight {E : Type} [Fintype E]
    (q : E → ℝ) (ω : E → Bool) : ℝ := ∏ e, if ω e then q e else 1 - q e

/-- Probability of an event under independent edge retention. -/
noncomputable def eventMass {E : Type} [Fintype E] [DecidableEq E]
    (q : E → ℝ) (B : (E → Bool) → Prop) : ℝ :=
  ∑ ω, if B ω then edgeWeight q ω else 0

namespace AcyclicityReduction
/-- One random gate per vertex and one deterministic connector per ordered adjacency. -/
abbrev Edge {V : Type} (H : V → V → Prop) := Sum V {uv : V × V // H uv.1 uv.2}

/-- Split vertices into in/out ports; gates go in-to-out and connectors out-to-in. -/
def graph {V : Type} (H : V → V → Prop) : Digraph (V × Bool) (Edge H) where
  source e := match e with
    | .inl v => (v, false)
    | .inr uv => (uv.val.1, true)
  target e := match e with
    | .inl v => (v, true)
    | .inr uv => (uv.val.2, false)

/-- The selected vertices contain no adjacent pair. -/
def Independent {V : Type} (H : V → V → Prop) (selected : V → Bool) : Prop :=
  ∀ u v, H u v → ¬ (selected u = true ∧ selected v = true)

/-- Gates have probability one half; connectors are deterministic. -/
noncomputable def retention {V : Type} (H : V → V → Prop) : Edge H → ℝ
  | .inl _ => 1/2
  | .inr _ => 1
end AcyclicityReduction

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
noncomputable def count {n m k : ℕ} (G : Digraph (Fin n) (Fin m)) (U : Finset (Fin n))
    (w : Fin k ≃ U) (p : Fin m → ℚ) (r d : ℕ)
    (tape : Fin (countBits n m k r d) → Bool) : ℚ := by sorry

/-- The checked sampler on a finite tape. `none` reports zero cyclicity
probability; positive inputs return a retained configuration. The Solution
supplies the algorithm, and the theorems below constrain both cases. -/
noncomputable def sample {n m k : ℕ} (G : Digraph (Fin n) (Fin m)) (U : Finset (Fin n))
    (w : Fin k ≃ U) (p : Fin m → ℚ) (d : ℕ)
    (tape : Fin (sampleBits n m k d) → Bool) : Option (Fin m → Bool) := by sorry

/-- Cycle membership of a vertex is a two-terminal reliability event on the
split graph, without duplicating any random edge variable. -/
theorem vertex_reliability {V E : Type} [DecidableEq V] (G : Digraph V E)
    (v : V) (S : Set E) :
    Relation.TransGen (G.Adj S) v v ↔
      Relation.ReflTransGen ((G.splitVertex v).Adj S) (some v) none := by sorry

/-- Every cycle in the support meets a vertex of the supplied feedback set. -/
theorem feedback_cover {V E : Type} [DecidableEq V] (G : Digraph V E)
    (U : Finset V) (S : Set E) (hU : G.Feedback U S) :
    G.Cyclic S ↔ ∃ v ∈ U, Relation.TransGen (G.Adj S) v v := by sorry

/-- Relative counting accuracy on a uniformly random finite fair-bit tape.
All reliability calls are implemented by Algorithm S; there is no oracle premise. -/
theorem count_correct {n m k : ℕ} (G : Digraph (Fin n) (Fin m)) (U : Finset (Fin n))
    (w : Fin k ≃ U) (p : Fin m → ℚ) (hp : ∀ e, 0 ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1)
    (hU : G.Feedback U {e | 0<(p e : ℝ)}) (r d : ℕ) (hr : 0<r) :
    let Z := eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (Digraph.retained ω))
    let N := countBits n m k r d
    (∑ tape : Fin N → Bool, (1/(2 : ℝ)^N)*
      (if (1/(r : ℝ))*Z < |(count G U w p r d tape : ℝ)-Z| then 1 else 0)) ≤
      (1/2 : ℝ)^d := by sorry

/-- If the true probability is zero, every tape returns exactly zero. -/
theorem count_zero {n m k : ℕ} (G : Digraph (Fin n) (Fin m)) (U : Finset (Fin n))
    (w : Fin k ≃ U) (p : Fin m → ℚ) (hp : ∀ e, 0 ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1)
    (r d : ℕ)
    (hz : eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (Digraph.retained ω)) = 0)
    (tape : Fin (countBits n m k r d) → Bool) : count G U w p r d tape = 0 := by sorry

/-- Conditional sampling within total variation `2⁻ᵈ`, expressed by all tests
with values in `[0,1]`, on the finite space of retained edge configurations. -/
theorem sample_correct {n m k : ℕ} (G : Digraph (Fin n) (Fin m)) (U : Finset (Fin n))
    (w : Fin k ≃ U) (p : Fin m → ℚ)
    (hp : ∀ e, 0 ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1)
    (hU : G.Feedback U {e | 0<(p e : ℝ)})
    (hZ : 0<eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (Digraph.retained ω)))
    (d : ℕ) (f : (Fin m → Bool) → ℝ) (hf0 : ∀ x, 0≤f x) (hf1 : ∀ x, f x≤1) :
    let N := sampleBits n m k d
    |(∑ tape : Fin N → Bool, (1/(2 : ℝ)^N)*(sample G U w p d tape).elim 0 f)-
      (∑ ω, if G.Cyclic (Digraph.retained ω) then edgeWeight (fun e => (p e : ℝ)) ω*f ω else 0)/
        eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (Digraph.retained ω))| ≤
      (1/2 : ℝ)^d := by sorry

/-- The checked sampler reports an undefined conditional law exactly when
cyclicity has zero probability, for every finite tape. -/
theorem sample_none_iff {n m k : ℕ} (G : Digraph (Fin n) (Fin m)) (U : Finset (Fin n))
    (w : Fin k ≃ U) (p : Fin m → ℚ) (hp : ∀ e, 0 ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1)
    (hU : G.Feedback U {e | 0<(p e : ℝ)}) (d : ℕ)
    (tape : Fin (sampleBits n m k d) → Bool) :
    sample G U w p d tape = none ↔
      eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (Digraph.retained ω)) = 0 := by sorry

/-- The exact independent-set reduction: acyclicity probability in the gate
construction equals the independent-set count divided by `2^|V|`. The complexity
theoretic hardness of counting independent sets is an external result. -/
theorem acyclicity_probability {V : Type} [Fintype V] (H : V → V → Prop)
    (hsym : ∀ ⦃u v⦄, H u v → H v u) :
    eventMass (AcyclicityReduction.retention H)
      (fun ω => ¬ (AcyclicityReduction.graph H).Cyclic (Digraph.retained ω)) =
    (Fintype.card {selected : V → Bool // AcyclicityReduction.Independent H selected} : ℝ)/
      (2 : ℝ)^Fintype.card V := by sorry

end Publication
end DirectedCycleFPRAS
