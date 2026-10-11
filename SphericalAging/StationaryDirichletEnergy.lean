module

public import SphericalAging.StationaryTriangleIntegral
public import SphericalAging.StationaryLogProfile
public import SphericalAging.DirichletLogChange
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

public section

/-! The actual critical cutoff square estimate and its Fatou limit. -/
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.StationaryDirichletEnergy
noncomputable section
open StationaryNormalization StationaryCutoffBalance StationarySchurCutoff
  StationaryTriangleIntegral DirichletKernel StationaryLogProfile DirichletLogChange

@[expose] def cutoffEnergy (a : ℝ) (u : ℝ → ℝ) (T : ℝ) (z : ℝ×ℝ) :=
  Xi a z.1 z.2*(amplitudeCutoff a u T z.1-amplitudeCutoff a u T z.2)^2

theorem normalized_weighted_profile_square_integrable (p : ℕ) (β γ q a : ℝ)
    (c r : ℝ → ℝ) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha : 0<a) (T : ℝ) (hT : 0<T) :
    IntegrableOn (fun t => (normalizedProfile q c t)^2*t^(-criticalRho a)) (Ioc 0 T) := by
  obtain ⟨hu,_⟩ := StationaryComparison.normalized_profile_admissible p β γ q c r h
  have hUmeas : AEStronglyMeasurable (fun t => (normalizedProfile q c t)^2) (volume.restrict (Ioi 0)) :=
    ((h.profile_C1.continuousOn.mono Ioi_subset_Ici_self).aestronglyMeasurable (μ:=volume) measurableSet_Ioi).pow 2
  have hi := bounded_weighted_interval_integrable (fun t => (normalizedProfile q c t)^2)
    (criticalRho a) T 1 (by dsimp [criticalRho];linarith) hT hUmeas (by norm_num) (fun t ht => ?_)
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp hi
  · rw [abs_of_nonneg (sq_nonneg _)]
    obtain ⟨hl,hr⟩ := hu.values t ht.le
    nlinarith only [hl,hr]

theorem normalized_cutoff_energy_bound (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (ha : 0<a) (ha1 : a<1)
    (T : ℝ) (hT : 0<T) :
    Integrable (cutoffEnergy a (normalizedProfile q c) T)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) ∧
    (∫ z : ℝ×ℝ,cutoffEnergy a (normalizedProfile q c) T z
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))≤
      2*cutoffJ a (normalizedProfile q c) T := by
  have hu := h.profile_C1.continuousOn
  have humeas := (hu.mono Ioi_subset_Ici_self).aestronglyMeasurable (μ:=volume) measurableSet_Ioi
  have hi := normalized_weighted_profile_square_integrable p β γ q a c r h ha T hT
  obtain ⟨_,he,hid⟩ := cutoff_square_identity a T (normalizedProfile q c) ha1 hT humeas hi
  obtain ⟨_,hle⟩ := weighted_convolution_triangle_le a T (normalizedProfile q c) ha1 hT hu
    (fun t ht => (h.profile_positive t ht).le) hi
  refine ⟨he,?_⟩
  change (∫ z : ℝ×ℝ,cutoffEnergy a (normalizedProfile q c) T z
    ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))/2=_ at hid
  dsimp only [cutoffJ]
  linarith only [hid,hle]

/-- The actual raw-time Schur energy is finite. All cutoff estimates come
from the actual profile equation, and Fatou takes the real cutoff limit. -/
theorem normalized_schur_energy_finite (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    (∫⁻ z in Ioi (0:ℝ)×ˢIoi (0:ℝ),ENNReal.ofReal
      (schurDensity a (logProfile a (normalizedProfile q c)) z) ∂(volume.prod volume))<∞ := by
  let u := normalizedProfile q c
  let μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))
  let E := fun n : ℕ => cutoffEnergy a u (n+1)
  let F := fun n : ℕ => fun z : ℝ×ℝ => ENNReal.ofReal (E n z)
  obtain ⟨M,hM,hJM⟩ := normalized_cutoff_deficit_uniform_bound p β γ q a c r hp h ha0 ha1 hbalance
  have hCut (n : ℕ) : Integrable (E n) μ ∧ (∫ z,E n z ∂μ)≤2*M := by
    obtain ⟨hi,hb⟩ := normalized_cutoff_energy_bound p β γ q a c r h ha0 (by linarith) (n+1) (by positivity)
    refine ⟨hi,hb.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (hJM (n+1) (by positivity)) (by norm_num)
  have hNonneg (n : ℕ) : 0≤ᵐ[μ] E n := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with z hz
    exact mul_nonneg (Xi_nonnegative a z.1 z.2 hz.1.le hz.2.le) (sq_nonneg _)
  have hFb (n : ℕ) : (∫⁻ z,F n z ∂μ)≤ENNReal.ofReal (2*M) := by
    rw [←ofReal_integral_eq_lintegral_ofReal (hCut n).1 (hNonneg n)]
    exact ENNReal.ofReal_le_ofReal (hCut n).2
  have hLim (z : ℝ×ℝ) : Tendsto (fun n => F n z) atTop
      (𝓝 (ENNReal.ofReal (Xi a z.1 z.2*(z.1^a*u z.1-z.2^a*u z.2)^2))) := by
    have hbound : ∀ᶠ n : ℕ in atTop,z.1≤(n:ℝ)+1 ∧ z.2≤(n:ℝ)+1 := by
      have h1 := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
        (eventually_ge_atTop (max z.1 z.2))
      filter_upwards [h1] with n hn
      constructor <;> linarith [le_max_left z.1 z.2,le_max_right z.1 z.2]
    apply tendsto_const_nhds.congr'
    filter_upwards [hbound] with n hn
    simp only [F,E,cutoffEnergy,amplitudeCutoff,indicator_of_mem (show z.1∈Iic ((n:ℝ)+1) from hn.1),
      indicator_of_mem (show z.2∈Iic ((n:ℝ)+1) from hn.2)]
  have hFatou := lintegral_liminf_le' (μ:=μ) (u:=atTop) (f:=F) (fun n => ((hCut n).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal))
  have hEnergy : (∫⁻ z,ENNReal.ofReal (Xi a z.1 z.2*(z.1^a*u z.1-z.2^a*u z.2)^2) ∂μ)≤
      ENNReal.ofReal (2*M) := by
    calc
      _ = ∫⁻ z,liminf (fun n => F n z) atTop ∂μ := by
        apply lintegral_congr
        intro z
        exact (hLim z).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ z,F n z ∂μ) atTop := hFatou
      _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall hFb).frequently
  have hlog (s : ℝ) (hs : 0<s) : logProfile a u (Real.log s)=s^a*u s := by
    rw [logProfile,Real.exp_log hs,mul_comm a (Real.log s),←Real.rpow_def_of_pos hs]
  have hEq : (∫⁻ z in Ioi (0:ℝ)×ˢIoi (0:ℝ),ENNReal.ofReal (schurDensity a (logProfile a u) z) ∂(volume.prod volume))=
      ∫⁻ z,ENNReal.ofReal (Xi a z.1 z.2*(z.1^a*u z.1-z.2^a*u z.2)^2) ∂μ := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with z hz
    simp only [schurDensity,hlog z.1 hz.1,hlog z.2 hz.2]
  rw [hEq]
  exact hEnergy.trans_lt ENNReal.ofReal_lt_top

end
end SphericalAging.StationaryDirichletEnergy
