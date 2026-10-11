module

public import SphericalAging.ScalarFamilyLift
public import SphericalAging.HardSphereStochastic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Actual bounded adapted continuous processes define continuous curves
of random L² classes. Common path bounds supply the genuine dominated
convergence argument, including at time zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.BoundedProcessL2Continuity
open HardSphereDynamics
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 1400000

lemma slice_memLp (f : ℝ≥0 → Ω → E) (hf : StronglyAdapted F f) (M : ℝ)
    (hbound : ∀ᵐ omega ∂P,∀ t,‖f t omega‖ ≤ M) (t : ℝ≥0) : MemLp (f t) 2 P :=
  MemLp.of_bound ((hf t).mono (F.le t)).aestronglyMeasurable M (hbound.mono (fun _ h => h t))

@[expose] def sliceClass (f : ℝ≥0 → Ω → E) (hf : StronglyAdapted F f) (M : ℝ)
    (hbound : ∀ᵐ omega ∂P,∀ t,‖f t omega‖ ≤ M) (t : ℝ≥0) : Lp E 2 P :=
  (slice_memLp f hf M hbound t).toLp (f t)

lemma norm_sq_sliceClass_sub (f : ℝ≥0 → Ω → E) (hf : StronglyAdapted F f) (M : ℝ)
    (hbound : ∀ᵐ omega ∂P,∀ t,‖f t omega‖ ≤ M) (t s : ℝ≥0) :
    ‖sliceClass f hf M hbound t-sliceClass f hf M hbound s‖^2=
      ∫ omega,‖f t omega-f s omega‖^2 ∂P := by
  rw [← ScalarFamilyLift.integral_norm_sq_Lp]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (sliceClass f hf M hbound t) (sliceClass f hf M hbound s),
    (slice_memLp f hf M hbound t).coeFn_toLp,(slice_memLp f hf M hbound s).coeFn_toLp]
      with omega hsub ht hs
  rw [hsub,Pi.sub_apply]
  simp only [sliceClass]
  rw [ht,hs]

/-- Genuine L² continuity from bounded sample-path continuity. -/
theorem sliceClass_continuous (f : ℝ≥0 → Ω → E) (hf : StronglyAdapted F f) (M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ᵐ omega ∂P,∀ t,‖f t omega‖ ≤ M)
    (hcontinuous : ∀ᵐ omega ∂P,Continuous (fun t => f t omega)) :
    Continuous (sliceClass f hf M hbound) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have hlimit : Tendsto (fun t : ℝ≥0 => ∫ omega,‖f t omega-f s omega‖^2 ∂P) (𝓝 s) (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝 s) (F := fun t : ℝ≥0 => fun omega : Ω => ‖f t omega-f s omega‖^2) (f := fun _omega : Ω => (0 : ℝ))
      (fun _omega : Ω => (2*M)^2)
      (.of_forall (fun t => ((slice_memLp f hf M hbound t).aestronglyMeasurable.sub
        (slice_memLp f hf M hbound s).aestronglyMeasurable).norm.pow 2))
      (.of_forall (fun t => hbound.mono (fun omega h => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith [h t,h s])) 2)))
      (integrable_const _) (hcontinuous.mono (fun omega h => by
        simpa only [sub_self,norm_zero,zero_pow (by norm_num : 2 ≠ 0)] using
          (((h.continuousAt (x := s)).tendsto.sub
            (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => f s omega) (𝓝 s) (𝓝 (f s omega)))).norm.pow 2)))
    simpa using hh
  rw [ContinuousAt,tendsto_iff_dist_tendsto_zero]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hlimit
  simp only [Function.comp_def,Real.sqrt_zero] at hsqrt
  convert hsqrt using 1
  funext t
  rw [dist_eq_norm,← norm_sq_sliceClass_sub f hf M hbound t s,Real.sqrt_sq (norm_nonneg _)]

end SphericalAging.BoundedProcessL2Continuity
