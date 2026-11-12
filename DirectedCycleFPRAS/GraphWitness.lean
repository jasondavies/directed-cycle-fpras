module

public import Mathlib.Logic.Relation
public import Mathlib.Data.Finset.Basic

@[expose] public section

/-!
# Directed edge witnesses

Edges have identities separate from their endpoints, allowing loops and parallel
arcs. `Cyclic` means a nonempty closed directed walk; equivalently the graph has
an ordinary directed cycle. No finite-instance enumeration is used in the proof.
-/

namespace DirectedCycleFPRAS

structure Digraph (V E : Type*) where
  source : E → V
  target : E → V

namespace Digraph

variable {V E : Type*} (G : Digraph V E)

/-- Adjacency in the retained-edge set. -/
def Adj (S : Set E) (u v : V) : Prop :=
  ∃ e ∈ S, G.source e = u ∧ G.target e = v

/-- A nonempty closed directed walk. -/
def Cyclic (S : Set E) : Prop := ∃ v, Relation.TransGen (G.Adj S) v v

/-- Edge e is present, and its target can return to its source without e. -/
def Witness (S : Set E) (e : E) : Prop :=
  e ∈ S ∧ Relation.ReflTransGen (G.Adj (S \ {e})) (G.target e) (G.source e)

/-- A walk ending at the source of e can stop on its first visit there,
so it never needs to traverse e. -/
theorem reach_source_without_edge {S : Set E} {e : E} {v : V}
    (h : Relation.ReflTransGen (G.Adj S) v (G.source e)) :
    Relation.ReflTransGen (G.Adj (S \ {e})) v (G.source e) := by
  classical
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a c hac _ ih =>
    by_cases ha : a = G.source e
    · subst a
      exact .refl
    · obtain ⟨f, hf, hfa, hfc⟩ := hac
      have hne : f ≠ e := by
        intro he
        subst f
        exact ha hfa.symm
      exact ih.head ⟨f, ⟨hf, hne⟩, hfa, hfc⟩

/-- Exact witness-union reduction, valid also for loops and parallel arcs. -/
theorem cyclic_iff_exists_witness (S : Set E) :
    G.Cyclic S ↔ ∃ e, G.Witness S e := by
  constructor
  · rintro ⟨v, h⟩
    obtain ⟨u, ⟨e, he, hsrc, hdst⟩, hreturn⟩ := Relation.TransGen.head'_iff.mp h
    refine ⟨e, he, G.reach_source_without_edge ?_⟩
    simpa [hsrc, hdst] using hreturn
  · rintro ⟨e, he, hreturn⟩
    have hret : Relation.ReflTransGen (G.Adj S) (G.target e) (G.source e) := by
      exact Relation.ReflTransGen.mono
        (fun _ _ ⟨f, hf, hs, ht⟩ => ⟨f, hf.1, hs, ht⟩) _ _ hreturn
    exact ⟨G.source e, Relation.TransGen.head' ⟨e, he, rfl, rfl⟩ hret⟩

/-- A retained self-loop is a witness, using the empty return walk. -/
theorem loop_witness {S : Set E} {e : E} (he : e ∈ S)
    (hloop : G.target e = G.source e) : G.Witness S e := by
  refine ⟨he, ?_⟩
  rw [hloop]

end Digraph
end DirectedCycleFPRAS
