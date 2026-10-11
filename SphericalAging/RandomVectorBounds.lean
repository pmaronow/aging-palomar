module

public import SphericalAging.ForkNormalizedEnergy

public section

/-! Actual probability-space L², energy, and Gaussian-overlap bounds.
These bounds establish the boundedness required for real limsup/liminf. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal InnerProductSpace
namespace SphericalAging.RandomVectorBounds
open FiniteModel ForkEnergyComparison RandomGaussianPairing ForkNormalizedEnergy
open GaussianLandscape GaussianLandscapeMoments SphereInitialLaw
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem lpNorm_le_bound {E : Type*} [NormedAddCommGroup E] {X : Ω→E}
    (hX : MemLp X 2 μ) {C : ℝ} (hC : 0≤C) (hB : ∀ᵐω ∂μ,‖X ω‖≤C) :
    lpNorm X 2 μ≤C := by
  have hb : ∀ᵐω ∂μ,‖hX.toLp X ω‖≤C := by
    filter_upwards [hX.coeFn_toLp,hB] with ω h1 h2
    simpa only [h1] using h2
  have hh := Lp.norm_le_of_ae_bound hC hb
  simpa [Lp.norm_toLp,lpNorm,measureUnivNNReal] using hh

theorem distanceRoot_le {N : ℕ} (hN : 0<N) {X Y : Ω→Vector N}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) {C D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (hXB : ∀ᵐω ∂μ,‖X ω‖≤C*Real.sqrt N)
    (hYB : ∀ᵐω ∂μ,‖Y ω‖≤D*Real.sqrt N) :
    distanceRoot μ N X Y≤C+D := by
  have hr : 0<Real.sqrt N := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hb : ∀ᵐω ∂μ,‖‖X ω-Y ω‖‖≤(C+D)*Real.sqrt N := by
    filter_upwards [hXB,hYB] with ω h1 h2
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (by linarith)
  exact (div_le_iff₀ hr).mpr
    (lpNorm_le_bound (hX.sub hY).norm (by positivity) hb)

theorem energy_abs_le {N p : ℕ} (hN : 0<N) (hp : 0<p)
    {J : Ω→Disorder N p} (hJ : HasLaw J (disorderLaw N p) μ)
    {X : Ω→Vector N} (hX : AEStronglyMeasurable X μ)
    (hXB : ∀ᵐω ∂μ,‖X ω‖≤Real.sqrt N) :
    |expectedEnergy (μ:=μ) J X|≤momentCeiling p 1 := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hQ := hJ.memLp_comp (landscape_memLp_two hN hp)
  have hQi := hQ.integrable (by norm_num : (1:ENNReal)≤2)
  have hHi := random_Hamiltonian_integrable hN hp (C:=1) (by norm_num) hJ hX
    (by simpa only [one_mul] using hXB)
  have hb : ∀ᵐω ∂μ,|Hamiltonian N p (J ω) (X ω)|≤(N:ℝ)*landscapeNorm N p (J ω) := by
    filter_upwards [hXB] with ω hω
    simpa only [one_pow,one_mul,mul_comm] using Hamiltonian_scaled_ball_bound hN hp
      (C:=1) (by norm_num) (J ω) (by simpa only [one_mul] using hω)
  have hh := (norm_integral_le_integral_norm (fun ω => Hamiltonian N p (J ω) (X ω))).trans
    (integral_mono_ae hHi.norm (hQi.const_mul (N:ℝ)) (by
      filter_upwards [hb] with ω hω
      simpa only [Real.norm_eq_abs,Function.comp_apply] using hω))
  rw [integral_const_mul] at hh
  dsimp only [Function.comp_apply] at hh
  have hi := hJ.integral_comp (landscapeNorm_continuous N p).aestronglyMeasurable
  dsimp only [Function.comp_apply] at hi
  rw [hi] at hh
  have hm := (uniform_real_power_moment (show 1≤N by omega) hp (k:=1) (by norm_num)).2
  simp only [Real.rpow_one] at hm
  unfold expectedEnergy
  rw [abs_div,abs_of_pos hNr]
  exact (div_le_iff₀ hNr).mpr (by
    have hmul := mul_le_mul_of_nonneg_left hm hNr.le
    simpa only [Real.norm_eq_abs,mul_comm] using hh.trans hmul)

theorem absolute_pairing_le_one {N : ℕ} (hN : 0<N) {X G : Ω→Vector N}
    (hX : MemLp X 2 μ) (hG : HasLaw G (gaussianLaw N) μ)
    (hXB : ∀ᵐω ∂μ,‖X ω‖≤Real.sqrt N) :
    (∫ω,|⟪X ω,G ω⟫_ℝ/(N:ℝ)| ∂μ)≤1 := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hg := gaussian_memLp hG
  have hi := inner_integrable hX hg
  have hprod := hX.norm.integrable_mul hg.norm
  have h1 : (∫ω,|⟪X ω,G ω⟫_ℝ| ∂μ)≤∫ω,‖X ω‖*‖G ω‖ ∂μ :=
    integral_mono hi.abs hprod (fun ω => abs_real_inner_le_norm _ _)
  have h2 := scalar_product_L2_bound hX.norm hg.norm
  rw [abs_of_nonneg (integral_nonneg fun ω => mul_nonneg (norm_nonneg _) (norm_nonneg _))] at h2
  have heX : ‖hX.norm.toLp (fun ω => ‖X ω‖)‖=lpNorm X 2 μ := by
    rw [Lp.norm_toLp,lpNorm,eLpNorm_norm _ hX.aestronglyMeasurable]
  have heG : ‖hg.norm.toLp (fun ω => ‖G ω‖)‖=Real.sqrt N := by
    rw [Lp.norm_toLp,eLpNorm_norm _ hg.aestronglyMeasurable,←Lp.norm_toLp _ hg]
    exact gaussian_L2_norm hG
  rw [heX,heG] at h2
  have h3 := mul_le_mul_of_nonneg_right
    (lpNorm_le_bound hX (Real.sqrt_nonneg _) hXB) (Real.sqrt_nonneg (N:ℝ))
  rw [Real.mul_self_sqrt hNr.le] at h3
  simp only [abs_div,abs_of_pos hNr,integral_div]
  exact (div_le_one hNr).mpr (h1.trans (h2.trans h3))

end SphericalAging.RandomVectorBounds
