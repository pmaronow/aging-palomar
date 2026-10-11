module

public import SphericalAging.GaussianTreePathNoiseLaw

public section

/-! Exact Gaussian noise law for one whole branch below the first fork. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianTreeBranchNoiseLaw
open MeasureTheory ProbabilityTheory IndependentBranchingSuccess GaussianTreePathState
open GaussianLinearMixtureLaw GaussianTreePathNoiseLaw
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {K : ℕ}

@[expose] def branchResidual (α β : ℕ→ℝ) (d : ℕ) (a : Fin d→Fin K) (z : E×TreeSample E K d) : E :=
  (rootCoefficient α d*β d)•z.1+residualState α β d a z.2

theorem branchResidual_measurable (α β : ℕ→ℝ) (d : ℕ) (a : Fin d→Fin K) :
    Measurable (branchResidual (E:=E) α β d a) :=
  (measurable_fst.const_smul _).add ((residualState_measurable α β d a).comp measurable_snd)

theorem branchResidual_measurePreserving (α β : ℕ→ℝ) (d : ℕ) (a : Fin d→Fin K) :
    MeasurePreserving (branchResidual (E:=E) α β d a)
      ((stdGaussian E).prod (treeLaw (stdGaussian E) K d))
      ((stdGaussian E).map (scale (Real.sqrt (noiseVariance α β (d+1))))) := by
  let c := rootCoefficient α d*β d
  let v := Real.sqrt (noiseVariance α β d)
  have hp := (MeasurePreserving.id (stdGaussian E)).prod (residualState_measurePreserving (E:=E) α β d a)
  have hm : MeasurePreserving (mixture (E:=E) c 1)
      ((stdGaussian E).prod ((stdGaussian E).map (scale v)))
      ((stdGaussian E).map (scale (Real.sqrt (noiseVariance α β (d+1))))) := by
    refine ⟨(mixture (E:=E) c 1).measurable,?_⟩
    have ht := Measure.map_prod_map (stdGaussian E) (stdGaussian E) measurable_id (scale (E:=E) v).measurable
    simp only [Measure.map_id] at ht
    rw [ht,Measure.map_map (mixture (E:=E) c 1).measurable
      (measurable_id.prodMap (scale (E:=E) v).measurable)]
    have hf : (mixture (E:=E) c 1) ∘ Prod.map id (scale v)=mixture c v := by
      funext z
      simp [Prod.map,mixture_apply,scale_apply]
    rw [hf]
    apply mixture_map_eq_scaled
    dsimp [c,v]
    rw [Real.sq_sqrt (noiseVariance_nonneg α β d),
      Real.sq_sqrt (noiseVariance_nonneg α β (d+1)),noiseVariance]
  have hf : branchResidual (E:=E) α β d a=
      (mixture (E:=E) c 1) ∘ Prod.map id (residualState α β d a) := by
    funext z
    simp [branchResidual,Prod.map,mixture_apply,Function.comp_def,c]
  rw [hf]
  exact hm.comp hp

end SphericalAging.GaussianTreeBranchNoiseLaw
