module

public import DirectedCycleFPRAS.AlgorithmSTerminal

@[expose] public section

/-! The adaptive Algorithm S round process, with supported pool invariants
built into its state type. Stopping states are absorbing. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Prog
variable {Q S : Type}
theorem steps_fixed (K : S → Prog Q S) (a : S) (ha : K a = .ret a) (n : ℕ) :
    steps K n a = .ret a := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [steps,ha,bind] using ih
end Prog

namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

structure RoundData (V : Type) where
  resolved : Finset V
  estimates : V → ℝ
  pools : V → List (Finset V)

def RoundData.Valid (s : V) (M : ℕ) (a : RoundData V) : Prop :=
  PoolInvariant a.resolved a.estimates a.pools M ∧
    ∀ u∈a.resolved, 0<G.reliability p s u

abbrev RoundState (s : V) (M : ℕ) := {a : RoundData V // a.Valid G p s M}

def RoundData.update (a : RoundData V) (v : V) (M : ℕ) (r : ℕ × List (Finset V)) : RoundData V :=
  ⟨insert v a.resolved,
    Function.update a.estimates v (G.phiS p a.resolved a.estimates*r.1/M),
    Function.update a.pools v r.2⟩

def liftRound {s : V} {M : ℕ} (fallback : G.RoundState p s M) (a : RoundData V) : G.RoundState p s M :=
  if h : a.Valid G p s M then ⟨a,h⟩ else fallback

def advanceRound {s : V} {M : ℕ} (a : G.RoundState p s M) (v : V) : Prog Empty (G.RoundState p s M) :=
  (G.sGenerate p a.val.resolved a.val.estimates a.val.pools M v M).bind
    (fun r => .ret (G.liftRound p a (a.val.update G p v M r)))

def roundStep {s : V} {M : ℕ} (t : V) (a : G.RoundState p s M) : Prog Empty (G.RoundState p s M) :=
  if t∈a.val.resolved then .ret a else
    (G.bestArc p a.val.resolved a.val.estimates).elim (.ret a) fun e =>
      if a.val.estimates (G.source e)*p e≤0 then .ret a else G.advanceRound p a (G.target e)

def roundPrediction {s : V} {M : ℕ} (w : V) (a : G.RoundState p s M) : ℝ :=
  G.prediction p a.val.resolved a.val.estimates a.val.pools w

def roundTotal {s : V} {M : ℕ} (a : G.RoundState p s M) : ℝ :=
  G.totalPrediction p s a.val.resolved a.val.estimates a.val.pools

theorem advanceRound_exp {s : V} {M : ℕ} (hM : 0<M) (a : G.RoundState p s M) (v : V)
    (hv : 0<G.reliability p s v) (hΦ : 0<G.phiS p a.val.resolved a.val.estimates)
    (f : RoundData V → ℝ) :
    (G.advanceRound p a v).exp noOracle (fun b => f b.val) =
      (G.sGenerate p a.val.resolved a.val.estimates a.val.pools M v M).exp noOracle
        (fun r => f (a.val.update G p v M r)) := by
  rw [advanceRound,Prog.exp_bind]
  apply (G.sGenerate_records p a.val.resolved a.val.estimates a.val.pools M a.property.1 v M).exp_congr
  intro r hr
  have hvalid : (a.val.update G p v M r).Valid G p s M := by
    refine ⟨a.property.1.update hM v _ hΦ r.1 r.2 hr.1 hr.2.1 hr.2.2, ?_⟩
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hv
    · exact a.property.2 u hu
  simp only [Prog.exp,liftRound,dite_eq_left hvalid]

theorem selected_positive (hp : Prob01 p) {s : V} {M : ℕ} (a : G.RoundState p s M)
    (e : E) (he : G.bestArc p a.val.resolved a.val.estimates=some e)
    (hscore : 0<a.val.estimates (G.source e)*p e) :
    0<G.reliability p s (G.target e) ∧ 0<G.phiS p a.val.resolved a.val.estimates := by
  have hcut := G.bestArc_mem p _ _ he
  have hu := a.property.2 _ hcut.1
  have hp' : 0<p e := (mul_pos_iff.mp hscore).resolve_right
    (fun h => (not_lt_of_ge (hp e).1) h.2) |>.2
  refine ⟨(mul_pos hu hp').trans_le (G.reliability_arc p hp s e), ?_⟩
  exact G.phiS_pos p (fun e => (hp e).1) (fun e => (hp e).2)
    _ _ a.property.1.nonneg e hcut hscore

/-- Local martingale identities of the complete transition, including all
absorbing branches. -/
theorem roundStep_mean (hp : Prob01 p) {s : V} {M : ℕ} (hM : 0<M) (t w : V)
    (a : G.RoundState p s M) :
    (G.roundStep p t a).exp noOracle (G.roundPrediction p w) = G.roundPrediction p w a ∧
    (G.roundStep p t a).exp noOracle (G.roundTotal p) = G.roundTotal p a := by
  unfold roundStep
  split_ifs with ht
  · exact ⟨rfl,rfl⟩
  · cases he : G.bestArc p a.val.resolved a.val.estimates with
    | none => exact ⟨rfl,rfl⟩
    | some e =>
      simp only [Option.elim_some]
      split_ifs with hscore
      · exact ⟨rfl,rfl⟩
      · have hpos := G.selected_positive p hp a e he (lt_of_not_ge hscore)
        have hcut := G.bestArc_mem p _ _ he
        constructor
        · change (G.advanceRound p a (G.target e)).exp noOracle (fun b =>
            G.prediction p b.val.resolved b.val.estimates b.val.pools w) = _
          rw [G.advanceRound_exp p hM a (G.target e) hpos.1 hpos.2
            (fun b => G.prediction p b.resolved b.estimates b.pools w)]
          exact G.prediction_generate_unbiased p hp _ _ _ _ w hcut.2 hM a.property.1
        · change (G.advanceRound p a (G.target e)).exp noOracle (fun b =>
            G.totalPrediction p s b.val.resolved b.val.estimates b.val.pools) = _
          rw [G.advanceRound_exp p hM a (G.target e) hpos.1 hpos.2
            (fun b => G.totalPrediction p s b.resolved b.estimates b.pools)]
          exact G.totalPrediction_generate_mean p hp s _ _ _ _ hcut.2 hM a.property.1

theorem roundStep_variance (hp : Prob01 p) {s : V} {M : ℕ} (hM : 0<M) (t : V)
    (ht : 0<G.reliability p s t) (a : G.RoundState p s M) :
    (G.roundStep p t a).exp noOracle (fun b => (G.roundPrediction p t b-G.roundPrediction p t a)^2) ≤
      (Fintype.card E/M)*(G.reliability p s t)^2*(G.roundTotal p a)^2 ∧
    (G.roundStep p t a).exp noOracle (fun b => (G.roundTotal p b-G.roundTotal p a)^2) ≤
      (Fintype.card V*Fintype.card E/M)*(G.roundTotal p a)^2 := by
  unfold roundStep
  split_ifs with htR
  · simp only [Prog.exp,sub_self,zero_pow (by decide : 2≠0)]
    constructor <;> positivity
  · cases he : G.bestArc p a.val.resolved a.val.estimates with
    | none =>
      simp only [Option.elim_none,Prog.exp,sub_self,zero_pow (by decide : 2≠0)]
      constructor <;> positivity
    | some e =>
      simp only [Option.elim_some]
      split_ifs with hscore
      · simp only [Prog.exp,sub_self,zero_pow (by decide : 2≠0)]
        constructor <;> positivity
      · have hpos := G.selected_positive p hp a e he (lt_of_not_ge hscore)
        have hcut := G.bestArc_mem p _ _ he
        change (G.advanceRound p a (G.target e)).exp noOracle (fun b =>
          (G.prediction p b.val.resolved b.val.estimates b.val.pools t-G.roundPrediction p t a)^2) ≤ _ ∧
          (G.advanceRound p a (G.target e)).exp noOracle (fun b =>
          (G.totalPrediction p s b.val.resolved b.val.estimates b.val.pools-G.roundTotal p a)^2) ≤ _
        rw [G.advanceRound_exp p hM a (G.target e) hpos.1 hpos.2
            (fun b => (G.prediction p b.resolved b.estimates b.pools t-G.roundPrediction p t a)^2),
          G.advanceRound_exp p hM a (G.target e) hpos.1 hpos.2
            (fun b => (G.totalPrediction p s b.resolved b.estimates b.pools-G.roundTotal p a)^2)]
        exact G.prediction_generate_variance_bounds p hp s _ _ _ hM a.property.1 e hcut
          (G.bestArc_max p _ _ he) (a.property.2 _ hcut.1) hpos.1 t ht

theorem roundUpdate_valid {s : V} {M : ℕ} (hM : 0<M) (a : G.RoundState p s M) (v : V)
    (hv : 0<G.reliability p s v) (hΦ : 0<G.phiS p a.val.resolved a.val.estimates)
    (r : ℕ × List (Finset V)) (hr : r.1=r.2.length ∧ r.1≤M ∧ ∀ D∈r.2, v∈D) :
    (a.val.update G p v M r).Valid G p s M := by
  refine ⟨a.property.1.update hM v _ hΦ r.1 r.2 hr.1 hr.2.1 hr.2.2, ?_⟩
  intro u hu
  rcases Finset.mem_insert.mp hu with rfl | hu
  · exact hv
  · exact a.property.2 u hu

/-- The full output law of Algorithm S is the final target prediction of the
absorbing round process. The invariant controls every supported pool update. -/
theorem sRounds_steps_law (hp : Prob01 p) {s : V} {M : ℕ} (hM : 0<M) (t : V)
    (fuel : ℕ) (a : G.RoundState p s M)
    (hf : Fintype.card V-a.val.resolved.card < fuel) (f : ℝ → ℝ) :
    (G.sRounds (Q := Empty) p t M fuel a.val.resolved a.val.estimates a.val.pools).exp noOracle f =
      (Prog.steps (G.roundStep p t) fuel a).exp noOracle (fun b => f (G.roundPrediction p t b)) := by
  induction fuel generalizing a with
  | zero => omega
  | succ fuel ih =>
    by_cases htR : t∈a.val.resolved
    · have hfix : G.roundStep p t a = .ret a := by simp [roundStep,htR]
      rw [Prog.steps_fixed _ a hfix]
      simp only [sRounds,htR,ite_true,Prog.exp,roundPrediction]
      rw [G.prediction_resolved p _ _ _ M a.property.1 t htR]
    · have hleft : (G.sRounds (Q := Empty) p t M (fuel+1) a.val.resolved a.val.estimates a.val.pools).exp noOracle f =
          ((G.bestArc p a.val.resolved a.val.estimates).elim (.ret 0) fun e =>
            if a.val.estimates (G.source e)*p e≤0 then .ret 0 else
              (G.sGenerate p a.val.resolved a.val.estimates a.val.pools M (G.target e) M).bind fun r =>
                G.sRounds p t M fuel (insert (G.target e) a.val.resolved)
                  (Function.update a.val.estimates (G.target e) (G.phiS p a.val.resolved a.val.estimates*r.1/M))
                  (Function.update a.val.pools (G.target e) r.2)).exp noOracle f := by
        simp only [sRounds,htR,ite_false,bestArc]
      rw [hleft]
      cases he : G.bestArc p a.val.resolved a.val.estimates with
      | none =>
        have hfix : G.roundStep p t a = .ret a := by simp [roundStep,htR,he]
        rw [Prog.steps_fixed _ a hfix]
        have hzero := G.prediction_zero_of_outflow_zero p hp _ _ _ M a.property.1 t htR
          (G.phiS_zero_of_no_arc p hp _ _ a.property.1.nonneg he)
        simp only [Option.elim_none,Prog.exp,roundPrediction,hzero]
      | some e =>
        simp only [Option.elim_some]
        by_cases hz : a.val.estimates (G.source e)*p e≤0
        · rw [ite_eq_left hz]
          have hfix : G.roundStep p t a = .ret a := by simp [roundStep,htR,he,hz]
          rw [Prog.steps_fixed _ a hfix]
          have hzero := G.prediction_zero_of_outflow_zero p hp _ _ _ M a.property.1 t htR
            (G.phiS_zero_of_nonpositive_best p hp _ _ a.property.1.nonneg e he hz)
          simp only [Prog.exp,roundPrediction,hzero]
        · rw [ite_eq_right hz]
          have hpos := G.selected_positive p hp a e he (lt_of_not_ge hz)
          have hcut := G.bestArc_mem p _ _ he
          have hstep : G.roundStep p t a = G.advanceRound p a (G.target e) := by simp [roundStep,htR,he,hz]
          rw [Prog.steps,hstep]
          simp only [Prog.exp_bind,advanceRound,Prog.exp]
          apply (G.sGenerate_records p _ _ _ M a.property.1 (G.target e) M).exp_congr
          intro r hr
          have hvalid := G.roundUpdate_valid p hM a (G.target e) hpos.1 hpos.2 r hr
          let b := G.liftRound p a (a.val.update G p (G.target e) M r)
          have hb : b.val = a.val.update G p (G.target e) M r := by
            simp only [b,liftRound,dite_eq_left hvalid]
          have hfb : Fintype.card V-b.val.resolved.card < fuel := by
            rw [hb]
            change Fintype.card V-(insert (G.target e) a.val.resolved).card < fuel
            rw [Finset.card_insert_of_notMem hcut.2]
            have hc := Finset.card_le_univ (insert (G.target e) a.val.resolved)
            rw [Finset.card_insert_of_notMem hcut.2] at hc
            omega
          have hh := ih b hfb
          rw [hb] at hh
          exact hh

theorem reliability_self (s : V) : G.reliability p s s=1 := by
  simp [reliability,eventMass,edgeWeight_sum,Relation.ReflTransGen.refl]

def initialRound (s : V) {M : ℕ} (hM : 0<M) : G.RoundState p s M :=
  ⟨⟨{s},(fun u => if u=s then 1 else 0),(fun u => if u=s then [{s}] else [])⟩,
    initial_poolInvariant s hM, by
      intro u hu
      have h : u=s := by simpa using hu
      subst u
      rw [G.reliability_self]
      norm_num⟩

theorem algS_steps_law (hp : Prob01 p) (s t : V) {M : ℕ} (hM : 0<M) (f : ℝ → ℝ) :
    (G.algS (Q := Empty) p s t M).exp noOracle f =
      (Prog.steps (G.roundStep p t) (Fintype.card V) (G.initialRound p s hM)).exp noOracle
        (fun a => f (G.roundPrediction p t a)) := by
  apply G.sRounds_steps_law p hp hM t (Fintype.card V) (G.initialRound p s hM) _ f
  have hn : 0<Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  simp only [initialRound,Finset.card_singleton]
  omega

end Digraph

end
end DirectedCycleFPRAS
