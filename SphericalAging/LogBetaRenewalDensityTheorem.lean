module

public import SphericalAging.LogBetaConvolutionShift

public section

/-! Complete source Lemma log-beta-renewal-density (manuscript 16.12):
the actual renewal density is locally integrable, tail bounded, and has the
reciprocal-mean limit. All smoothing/key-renewal inputs are proved. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.LogBetaRenewalDensityTheorem
noncomputable section
open LogBetaRenewal LogBetaMoments LogBetaMean LogBetaConvolutionPowers
  LogBetaSmoothedRenewal LogBetaRenewalSeries LogBetaConvolutionShift

/-- All analytic conclusions for the genuine log-beta renewal density.
The proof smooths by a finite actual convolution, applies the proved key
renewal theorem with its hypotheses discharged, and adds the finite initial
power sum. No target renewal limit or target density estimate is a premise. -/
theorem log_beta_renewal_density {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1) :
    (∀ y>0,density ρ a y=Real.exp (-ρ*y)*(1-Real.exp (-y))^(a-1)/beta ρ a) ∧
    ((∫ y : ℝ,y ∂law ρ a)=
      (Complex.digamma ((ρ+a:ℝ):ℂ)).re-(Complex.digamma (ρ:ℂ)).re) ∧
    0<(∫ y : ℝ,y ∂law ρ a) ∧
    (∀ y : ℝ,Summable (fun n : ℕ => powerDensity ρ a n y)) ∧
    (∀ T : ℝ,IntegrableOn (renewalDensity ρ a) (Icc 0 T)) ∧
    (∃ C : ℝ,0≤C ∧ ∀ y≥1,0≤renewalDensity ρ a y ∧ renewalDensity ρ a y≤C) ∧
    Tendsto (renewalDensity ρ a) atTop (𝓝 (1/(∫ y : ℝ,y ∂law ρ a))) := by
  obtain ⟨j,hj⟩ := exists_smoothing_index a ha
  obtain ⟨hSum,hSplit⟩ := renewalDensity_decomposition hρ ha ha1 j hj
  obtain ⟨C1,hC1,hB1⟩ := initialDensitySum_tail_bound hρ ha ha1 j
  obtain ⟨_,C2,hC2,hB2⟩ := smoothed_renewal_uniform_bound hρ ha ha1 j hj
  have hLocal (T : ℝ) : IntegrableOn (renewalDensity ρ a) (Icc 0 T) := by
    apply ((initialDensitySum_integrable hρ ha ha1 j).integrableOn.add
      (smoothedRenewal_local_integrable hρ ha ha1 j hj T)).congr
    exact Eventually.of_forall (fun y => (hSplit y).symm)
  have hBound : ∀y≥1,0≤renewalDensity ρ a y ∧ renewalDensity ρ a y≤C1+C2 := by
    intro y hy
    rw [hSplit y]
    exact ⟨add_nonneg (hB1 y hy).1 (hB2 y).1,add_le_add (hB1 y hy).2 (hB2 y).2⟩
  have hLimit : Tendsto (renewalDensity ρ a) atTop (𝓝 (1/(∫ y : ℝ,y ∂law ρ a))) := by
    have h := (initialDensitySum_limit_zero hρ ha ha1 j).add (smoothed_renewal_limit hρ ha ha1 j hj)
    simp only [zero_add] at h
    exact h.congr (fun y => (hSplit y).symm)
  exact ⟨fun y hy => density_formula hy,mean_digamma_formula hρ ha,mean_positive hρ ha,hSum,hLocal,
    ⟨C1+C2,add_nonneg hC1 hC2,hBound⟩,hLimit⟩

end
end SphericalAging.LogBetaRenewalDensityTheorem
