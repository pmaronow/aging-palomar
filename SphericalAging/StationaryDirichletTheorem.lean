module

public import SphericalAging.StationaryDirichletEnergy

public section

/-! Complete manuscript Lemma 16.9: the logarithmic Dirichlet bound,
including boundedness, a positive lower bound and compact-uniform increments. -/
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.StationaryDirichletTheorem
noncomputable section
open StationaryNormalization StationaryLogProfile StationaryDirichletEnergy
  DirichletLogChange DirichletIncrement

/-- Exact complete logarithmic Dirichlet conclusion for the actual
normalized stationary profile. Every energy input is derived from the
stationary equation rather than assumed. -/
theorem stationary_critical_dirichlet (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ A d : ℝ,∃ L : ℝ≥0,0<A ∧ 0<d ∧
      (∀ x : ℝ,0<logProfile a (normalizedProfile q c) x ∧ logProfile a (normalizedProfile q c) x≤A) ∧
      (∀ x≥0,d≤logProfile a (normalizedProfile q c) x) ∧
      LipschitzWith L (logProfile a (normalizedProfile q c)) ∧
      Tendsto (logProfile a (normalizedProfile q c)) atBot (𝓝 0) ∧
      (∫⁻ z : ℝ×ℝ,ENNReal.ofReal
        ((logProfile a (normalizedProfile q c) z.1-logProfile a (normalizedProfile q c) z.2)^2/
          (2*Real.cosh ((z.1-z.2)/2))^(2-2*a)) ∂(volume.prod volume))<∞ ∧
      (∀ b : ℝ,Tendsto (fun x : ℝ => logProfile a (normalizedProfile q c) (x+b)-
        logProfile a (normalizedProfile q c) x) atTop (𝓝 0)) ∧
      (∀ R : ℝ,0≤R → ∀ ε : ℝ,0<ε → ∃ T : ℝ,∀ x≥T,∀ b : ℝ,
        |b|≤R → |logProfile a (normalizedProfile q c) (x+b)-
          logProfile a (normalizedProfile q c) x|<ε) := by
  obtain ⟨A,d,L,hA,hd,hb,hl,hLip,hBot⟩ :=
    normalized_logProfile_properties p β γ q a c r hp h ha0 ha1 hbalance
  have hFinite : (∫⁻ z : ℝ×ℝ,ENNReal.ofReal
      (energyDensity a (logProfile a (normalizedProfile q c)) z) ∂(volume.prod volume))<∞ := by
    rw [logarithmic_energy_eq_schur hLip.continuous.measurable]
    exact normalized_schur_energy_finite p β γ q a c r hp h ha0 ha1 hbalance
  refine ⟨A,d,L,hA,hd,hb,hl,hLip,hBot,hFinite,?_,?_⟩
  · exact fun b => fixed_increment_tendsto_zero (by linarith : a<1) hLip hFinite b
  · exact compact_increment_decay (by linarith : a<1) hLip hFinite

end
end SphericalAging.StationaryDirichletTheorem
