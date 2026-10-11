module

public import SphericalAging.ExternalFieldSeededCost

public section

/-! Actual seeded ball-algorithm energy integrability and dimension-uniform
expectation bounds from genuine Gaussian landscape moments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SphericalAging.SeedAlgorithmEnergyBounds
open Set MeasureTheory FiniteModel GaussianLandscape GaussianLandscapeMoments
  HamiltonianBallBounds SphereGibbsEntropy
variable {Ξ : Type*} [MeasurableSpace Ξ]

@[expose] def energy {N p : ℕ} (A : Ξ×Disorder N p→Vector N) (z : Ξ×Disorder N p) : ℝ :=
  Hamiltonian N p z.2 (A z)/(N:ℝ)

theorem energy_integrable_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    (σ : Measure Ξ) [IsProbabilityMeasure σ] {A : Ξ×Disorder N p→Vector N}
    (hA : Measurable A) (hball : ∀ᵐξ ∂σ,∀J,‖A (ξ,J)‖≤Real.sqrt N) :
    Integrable (energy A) (σ.prod (disorderLaw N p)) ∧
      |∫z,energy A z ∂σ.prod (disorderLaw N p)|≤momentCeiling p 1 := by
  have hQ := landscapeNorm_integrable hN hp
  have hQprod := hQ.comp_snd σ
  have hmeas : Measurable (energy A) :=
    ((Hamiltonian_joint_continuous N p).measurable.comp (measurable_snd.prodMk hA)).div_const _
  have hbound : ∀ᵐz ∂σ.prod (disorderLaw N p),‖energy A z‖≤landscapeNorm N p z.2 := by
    filter_upwards [(measurePreserving_fst (μ := σ) (ν := disorderLaw N p)).quasiMeasurePreserving.ae hball]
      with z hz
    have hh := Hamiltonian_ball_bound hN hp z.2 (hz z.2)
    change |Hamiltonian N p z.2 (A z)/(N:ℝ)|≤landscapeNorm N p z.2
    rw [abs_div,abs_of_pos (show 0<(N:ℝ) from Nat.cast_pos.mpr hN)]
    simpa only [Prod.mk.eta] using hh
  have hi : Integrable (energy A) (σ.prod (disorderLaw N p)) := hQprod.mono' hmeas.aestronglyMeasurable hbound
  refine ⟨hi,?_⟩
  have hh := (norm_integral_le_integral_norm (energy A)).trans (integral_mono_ae hi.norm hQprod hbound)
  have he : (∫z : Ξ×Disorder N p,landscapeNorm N p z.2 ∂σ.prod (disorderLaw N p))=
      ∫J : Disorder N p,landscapeNorm N p J ∂disorderLaw N p := by
    rw [integral_prod _ hQprod]
    simp only [integral_const,probReal_univ,one_smul]
  rw [he] at hh
  have hm := (uniform_real_power_moment (by omega : 1≤N) (by omega : 0<p)
    (k := 1) (by norm_num)).2
  simp only [Real.rpow_one] at hm
  exact hh.trans hm

end SphericalAging.SeedAlgorithmEnergyBounds
