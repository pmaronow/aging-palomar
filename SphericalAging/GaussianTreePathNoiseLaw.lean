module

public import SphericalAging.GaussianTreePathState

public section

/-! The residual on a literal sampled path has the exact Gaussian law
with its computed variance, including variance zero. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianTreePathNoiseLaw
open MeasureTheory ProbabilityTheory IndependentBranchingSuccess GaussianTreePathState
open GaussianLinearMixtureLaw PartialVarianceBranchingCoefficients
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {K : ℕ}

theorem residualState_measurePreserving (α β : ℕ→ℝ) (d : ℕ) (a : Fin d→Fin K) :
    MeasurePreserving (residualState (E:=E) α β d a) (treeLaw (stdGaussian E) K d)
      ((stdGaussian E).map (scale (Real.sqrt (noiseVariance α β d)))) := by
  induction d with
  | zero =>
    refine ⟨residualState_measurable α β 0 a,?_⟩
    simp [residualState,terminalState,noiseVariance,treeLaw,scale]
    change Measure.dirac (0:E)=(stdGaussian E).map (fun _ : E => 0)
    rw [Measure.map_const,measure_univ,one_smul]
  | succ d ih =>
    let c := rootCoefficient α d*β d
    let v := Real.sqrt (noiseVariance α β d)
    have he : MeasurePreserving (Function.eval (a 0)) (treeLaw (stdGaussian E) K (d+1))
        ((stdGaussian E).prod (treeLaw (stdGaussian E) K d)) :=
      measurePreserving_eval (fun _ : Fin K => (stdGaussian E).prod (treeLaw (stdGaussian E) K d)) (a 0)
    have hp := ((MeasurePreserving.id (stdGaussian E)).prod (ih (fun i => a i.succ))).comp he
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
        simp [Function.comp_def,Prod.map,mixture_apply,scale_apply]
      rw [hf]
      apply mixture_map_eq_scaled
      dsimp [c,v]
      rw [Real.sq_sqrt (noiseVariance_nonneg α β d),
        Real.sq_sqrt (noiseVariance_nonneg α β (d+1)),noiseVariance]
    have hf : residualState (E:=E) α β (d+1) a=
        (mixture (E:=E) c 1) ∘ (Prod.map id (residualState α β d (fun i => a i.succ))) ∘
          Function.eval (a 0) := by
      funext z
      simpa only [Function.comp_def,Prod.map,mixture_apply,one_smul,id_eq,c] using
        residualState_succ α β d a z
    rw [hf]
    exact hm.comp hp

theorem rootCoefficient_partialVariance (V : ℕ→ℝ) (hV : ∀d,0≤V d)
    (hmono : ∀d,V (d+1)≤V d) (hV0 : V 0=1) (d : ℕ) :
    rootCoefficient (parentCoefficient V) d=Real.sqrt (V d) := by
  induction d with
  | zero => simp [rootCoefficient,hV0]
  | succ d ih =>
    rw [rootCoefficient,ih]
    exact scaled_parentRatio (V (d+1)) (V d) (hV _) (hmono _)

theorem noiseVariance_partialVariance (V : ℕ→ℝ) (hV : ∀d,0≤V d)
    (hmono : ∀d,V (d+1)≤V d) (hV0 : V 0=1) (d : ℕ) :
    noiseVariance (parentCoefficient V) (freshCoefficient V) d=1-V d := by
  have ht := totalVariance_one (parentCoefficient V) (freshCoefficient V)
    (coefficients_unit V hV hmono) d
  rw [rootCoefficient_partialVariance V hV hmono hV0 d,Real.sq_sqrt (hV d)] at ht
  linarith

end SphericalAging.GaussianTreePathNoiseLaw
