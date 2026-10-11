module

public import SphericalAging.LogBetaPowerDecay

public section

/-! Genuine measurability and local integrability for the smoothed renewal
series, and the finite initial-density part. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.LogBetaRenewalSeries
noncomputable section
open LogBetaRenewal LogBetaMoments LogBetaConvolutionPowers LogBetaSmoothedRenewal
  LogBetaPowerDecay AbsorptionCutoff.Renewal

@[expose] def renewalDensity (ρ a : ℝ) (y : ℝ) := ∑' n : ℕ,powerDensity ρ a n y

@[expose] def initialDensitySum (ρ a : ℝ) (j : ℕ) (y : ℝ) :=
  ∑ n∈Finset.range j,powerDensity ρ a n y

theorem renewalDensity_measurable {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1) :
    Measurable (renewalDensity ρ a) :=
  Measurable.tsum (fun n => (powerDensity_properties hρ ha ha1 n).1.measurable)

theorem smoothedRenewal_measurable {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1) (j : ℕ) :
    Measurable (smoothedRenewal ρ a j) := by
  letI := law_probability hρ ha
  apply Measurable.tsum
  intro n
  have hJoint : Measurable (fun z : ℝ×ℝ => powerDensity ρ a j (z.1-z.2)) := by
    exact (powerDensity_properties hρ ha ha1 j).1.measurable.comp (measurable_fst.sub measurable_snd)
  exact hJoint.stronglyMeasurable.integral_prod_right'.measurable

theorem smoothedRenewal_local_integrable {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1)
    (j : ℕ) (hj : 1<((j:ℝ)+1)*a) (T : ℝ) :
    IntegrableOn (smoothedRenewal ρ a j) (Icc 0 T) := by
  obtain ⟨_,C,hC,hb⟩ := smoothed_renewal_uniform_bound hρ ha ha1 j hj
  refine ⟨(smoothedRenewal_measurable hρ ha ha1 j).aestronglyMeasurable,HasFiniteIntegral.of_bounded (C:=C) ?_⟩
  exact Eventually.of_forall (fun y => by
    change ‖smoothedRenewal ρ a j y‖≤C
    rw [Real.norm_eq_abs,abs_of_nonneg (hb y).1]
    exact (hb y).2)

theorem initialDensitySum_integrable {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1) (j : ℕ) :
    Integrable (initialDensitySum ρ a j) := by
  exact integrable_finsetSum (Finset.range j) (fun n _ => (powerDensity_properties hρ ha ha1 n).2.2.1)

theorem initialDensitySum_limit_zero {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1) (j : ℕ) :
    Tendsto (initialDensitySum ρ a j) atTop (𝓝 0) := by
  convert tendsto_finsetSum (Finset.range j) (fun n _ => powerDensity_limit_zero hρ ha ha1 n) using 1
  · funext y
    simp only [initialDensitySum,Finset.sum_apply]
  · simp only [Finset.sum_const_zero]

theorem initialDensitySum_tail_bound {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1) (j : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀y≥1,0≤ initialDensitySum ρ a j y ∧ initialDensitySum ρ a j y≤C := by
  choose C hC hB using fun n : ℕ => powerDensity_tail_bound hρ ha ha1 n
  refine ⟨∑n∈Finset.range j,C n,Finset.sum_nonneg (fun n _ => hC n),?_⟩
  intro y hy
  constructor
  · exact Finset.sum_nonneg (fun n _ => (powerDensity_properties hρ ha ha1 n).1.nonnegative y)
  · exact Finset.sum_le_sum (fun n _ => hB n y hy)

end
end SphericalAging.LogBetaRenewalSeries
