module

public import SphericalAging.FiniteIndependentRestrictionLaw
public import SphericalAging.RegularTreeHighEnergyPruning
public import SphericalAging.IndependentBranchingSuccess
public import SphericalAging.ActualAlgorithmTree

public section

/-! Static injective pruning of the actual Gaussian noise tree preserves
its literal product law. The spatial tree may depend on every unused noise;
no law of an adaptively selected noise is assumed. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianTreeStaticPruneLaw
open MeasureTheory ProbabilityTheory IndependentBranchingSuccess RegularTreeHighEnergyPruning
open RegularTreeEnergyTelescoping ActualAlgorithmTree
variable {S G : Type} [MeasurableSpace S] [MeasurableSpace G] {K k : ℕ}

@[expose] def pruneSample : (d : ℕ)→Selection K k d→TreeSample G K d→TreeSample G k d
  | 0,_,z => z
  | d+1,σ,z => fun i => ((z (σ.1 i)).1,pruneSample d (σ.2 i) (z (σ.1 i)).2)

theorem pruneSample_measurePreserving (ν : Measure G) [IsProbabilityMeasure ν]
    (d : ℕ) (σ : Selection K k d) :
    MeasurePreserving (pruneSample (G:=G) d σ) (treeLaw ν K d) (treeLaw ν k d) := by
  induction d with
  | zero => exact MeasurePreserving.id _
  | succ d ih =>
    have hr := FiniteIndependentRestrictionLaw.restriction_measurePreserving
      (ν.prod (treeLaw ν K d)) σ.1
    have hc (i : Fin k) : MeasurePreserving (Prod.map id (pruneSample (G:=G) d (σ.2 i)))
        (ν.prod (treeLaw ν K d)) (ν.prod (treeLaw ν k d)) :=
      (MeasurePreserving.id ν).prod (ih (σ.2 i))
    have hp := measurePreserving_pi (fun _ : Fin k => ν.prod (treeLaw ν K d))
      (fun _ : Fin k => ν.prod (treeLaw ν k d)) hc
    have hf : pruneSample (G:=G) (d+1) σ=
        (fun z : Fin k→G×TreeSample G K d => fun i => Prod.map id (pruneSample d (σ.2 i)) (z i)) ∘
          (fun z : Fin K→G×TreeSample G K d => fun i => z (σ.1 i)) := by
      funext z i
      rfl
    rw [hf]
    exact hp.comp hr

@[expose] def samplePrune (d : ℕ) (σ : Selection K k d) (z : S×TreeSample G K d) : S×TreeSample G k d :=
  (z.1,pruneSample d σ z.2)

theorem samplePrune_measurePreserving (μ : Measure S) [SFinite μ] (ν : Measure G)
    [IsProbabilityMeasure ν] (d : ℕ) (σ : Selection K k d) :
    MeasurePreserving (samplePrune (S:=S) (G:=G) d σ)
      (μ.prod (treeLaw ν K d)) (μ.prod (treeLaw ν k d)) :=
  (MeasurePreserving.id μ).prod (pruneSample_measurePreserving ν d σ)

theorem prune_outputTree {N : ℕ} (A : G→FiniteModel.Vector N) (u : ℕ→G→G→G)
    (d : ℕ) (σ : Selection K k d) (s : G) (z : TreeSample G K d) :
    prune d σ (outputTree A u d s z)=outputTree A u d s (pruneSample d σ z) := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih =>
    dsimp only [prune,outputTree,pruneSample]
    exact congrArg (fun f => (A s,f)) (funext (fun i => ih (σ.2 i) _ _))

end SphericalAging.GaussianTreeStaticPruneLaw
