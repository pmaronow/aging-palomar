module

public import SphericalAging.BrownianFutureConditionalIntegral

public section

/-! Genuine weighted future moments. A past-measurable nonnegative weight
may be correlated with the waiting state; only the constructed future path
is integrated independently. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace SphericalAging.BrownianFutureWeightedMoment
open VectorBrownian BrownianFuturePath BrownianFutureFiltered
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {A : Type*} [MeasurableSpace A]

theorem weighted_future_moment (s : ℝ≥0) (Z : Space N→A)
    (hZ : Measurable[NullAugmentation.augment (filtration N) (law N) s] Z)
    (W : A→ℝ) (hW : StronglyMeasurable W) (hWi : Integrable (fun ω => W (Z ω)) (law N))
    (hWn : ∀ᵐ z ∂(law N).map Z,0≤W z)
    (G : A×Space N→ℝ) (hG : StronglyMeasurable G) (hGn : ∀ z η,0≤G (z,η))
    (hGi : ∀ᵐ z ∂(law N).map Z,Integrable (fun η => G (z,η)) (law N))
    (C : ℝ) (hC : 0≤C)
    (hGb : ∀ᵐ z ∂(law N).map Z,(∫ η,G (z,η) ∂law N)≤C) :
    Integrable (fun ω => W (Z ω)*G (Z ω,future s ω)) (law N) ∧
      (∫ ω,W (Z ω)*G (Z ω,future s ω) ∂law N)≤C*(∫ ω,W (Z ω) ∂law N) := by
  let P := law N
  let μ := P.map Z
  have hmZ : Measurable Z := hZ.mono ((NullAugmentation.augment (filtration N) P).le s) le_rfl
  letI : IsProbabilityMeasure μ := (hasLaw_map hmZ.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hmapZ : MeasurePreserving Z P μ := ⟨hmZ,rfl⟩
  have hWμ : Integrable W μ := (hmapZ.integrable_comp hW.aestronglyMeasurable).mp hWi
  let H : A×Space N→ℝ := fun q => W q.1*G q
  have hH : StronglyMeasurable H := (hW.comp_measurable measurable_fst).mul hG
  have hslice : ∀ᵐ z ∂μ,Integrable (fun η => H (z,η)) P := by
    filter_upwards [hGi] with z hz
    exact hz.const_mul (W z)
  have houter : Integrable (fun z => ∫ η,‖H (z,η)‖ ∂P) μ := by
    apply (hWμ.const_mul C).mono' hH.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hWn,hGb] with z hzn hzb
    rw [Real.norm_of_nonneg (integral_nonneg (fun η => norm_nonneg _))]
    have he : (fun η => ‖H (z,η)‖)=fun η => W z*G (z,η) := by
      funext η
      exact Real.norm_of_nonneg (mul_nonneg hzn (hGn z η))
    rw [he,integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hzb hzn).trans_eq (mul_comm _ _)
  have hHi : Integrable H (μ.prod P) := (integrable_prod_iff hH.aestronglyMeasurable).mpr ⟨hslice,houter⟩
  have hMP := waiting_future_measurePreserving s Z hZ
  refine ⟨hMP.integrable_comp_of_integrable hHi,?_⟩
  have he : (∫ ω,H (Z ω,future s ω) ∂P)=∫ q,H q ∂μ.prod P := by
    rw [←hMP.map_eq]
    exact (integral_map hMP.measurable.aemeasurable hH.aestronglyMeasurable).symm
  change (∫ ω,H (Z ω,future s ω) ∂P)≤C*(∫ ω,W (Z ω) ∂P)
  rw [he,integral_prod _ hHi]
  have hineq : (∫ z,∫ η,H (z,η) ∂P ∂μ)≤∫ z,C*W z ∂μ := by
    apply integral_mono_ae hHi.integral_prod_left (hWμ.const_mul C)
    filter_upwards [hWn,hGb] with z hzn hzb
    change (∫ η,W z*G (z,η) ∂P)≤C*W z
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hzb hzn).trans_eq (mul_comm _ _)
  rw [integral_const_mul] at hineq
  have heW : (∫ ω,W (Z ω) ∂P)=∫ z,W z ∂μ := by
    rw [←hmapZ.map_eq]
    exact (integral_map hmZ.aemeasurable hW.aestronglyMeasurable).symm
  rw [heW]
  exact hineq

end SphericalAging.BrownianFutureWeightedMoment
