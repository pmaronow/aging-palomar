module

public import SphericalAging.GaussianTreeBranchNoiseLaw
public import SphericalAging.GaussianScaledCommonPairLaw
public import SphericalAging.IndependentTreeChildPairLaw

public section

/-! Literal terminal pair law when the two sampled paths diverge at
their first child. Shared Gaussian ancestry is retained exactly. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianTreeFirstForkPairLaw
open MeasureTheory ProbabilityTheory IndependentBranchingSuccess GaussianTreePathState
open GaussianTreeBranchNoiseLaw GaussianScaledCommonPairLaw GaussianCommonFuturePairLaw
open IndependentTreeChildPairLaw GaussianBranchingSuccess
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {K : ℕ}

theorem firstFork_pair_measurePreserving (α β : ℕ→ℝ)
    (hunit : ∀d,(α d)^2+(β d)^2=1) (d : ℕ) (a b : Fin (d+1)→Fin K)
    (hab : a 0≠b 0) :
    MeasurePreserving (fun z : E×TreeSample E K (d+1) =>
      (terminalState (update α β) (d+1) a z,terminalState (update α β) (d+1) b z))
      ((stdGaussian E).prod (treeLaw (stdGaussian E) K (d+1)))
      (((stdGaussian E).prod (stdGaussian E)).map (correlatedPair (rootCoefficient α (d+1)))) := by
  let fa := branchResidual (E:=E) α β d (fun i => a i.succ)
  let fb := branchResidual (E:=E) α β d (fun i => b i.succ)
  let pairChild := fun z : TreeSample E K (d+1) => (z (a 0),z (b 0))
  have hchild := childPair_measurePreserving (stdGaussian E) d (a 0) (b 0) hab
  have hnoise := ((branchResidual_measurePreserving (E:=E) α β d (fun i => a i.succ)).prod
    (branchResidual_measurePreserving (E:=E) α β d (fun i => b i.succ))).comp hchild
  have hinputs := (MeasurePreserving.id (stdGaussian E)).prod hnoise
  have hend := endpointPair_measurePreserving (E:=E) (rootCoefficient α (d+1))
    (Real.sqrt (noiseVariance α β (d+1)))
    (by rw [Real.sq_sqrt (noiseVariance_nonneg α β (d+1))];exact totalVariance_one α β hunit (d+1))
  have hf : (fun z : E×TreeSample E K (d+1) =>
      (terminalState (update α β) (d+1) a z,terminalState (update α β) (d+1) b z))=
      endpointPair (rootCoefficient α (d+1)) ∘ Prod.map id (Prod.map fa fb ∘ pairChild) := by
    funext z
    simp only [Function.comp_def,Prod.map,id_eq,endpointPair,pairChild]
    rw [terminalState_affine,terminalState_affine,residualState_succ,residualState_succ]
    rfl
  rw [hf]
  exact hend.comp hinputs

end SphericalAging.GaussianTreeFirstForkPairLaw
