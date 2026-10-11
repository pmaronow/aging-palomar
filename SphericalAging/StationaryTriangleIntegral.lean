module

public import SphericalAging.StationarySchurCutoff
public import Mathlib.MeasureTheory.Group.Prod

public section

/-! The actual weighted causal-convolution triangle is bounded by the
actual Schur square cross integral, via the genuine additive shear map. -/
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SphericalAging.StationaryTriangleIntegral
noncomputable section
open StationarySchurCutoff StationaryCutoffBalance StationaryNormalization DirichletKernel

@[expose] def subtractShear : ℝ×ℝ ≃ᵐ ℝ×ℝ :=
  (((MeasurableEquiv.prodComm : ℝ×ℝ ≃ᵐ ℝ×ℝ)).trans (MeasurableEquiv.shearSubRight ℝ)).trans
    ((MeasurableEquiv.prodComm : ℝ×ℝ ≃ᵐ ℝ×ℝ))

theorem subtractShear_apply (z : ℝ×ℝ) : subtractShear z=(z.1-z.2,z.2) := rfl

theorem kernel_amplitude_product (a : ℝ) (u : ℝ → ℝ) (T s t : ℝ)
    (hs : 0<s) (ht : 0<t) (hsT : s≤T) (htT : t≤T) :
    Xi a s t*amplitudeCutoff a u T s*amplitudeCutoff a u T t=
      u s*u t*(s+t)^(-1-criticalRho a) := by
  have hp : 0<s+t := add_pos hs ht
  rw [amplitudeCutoff,amplitudeCutoff,indicator_of_mem (show s∈Iic T from hsT),
    indicator_of_mem (show t∈Iic T from htT)]
  unfold Xi
  rw [Real.mul_rpow hs.le ht.le]
  have hsC : s^(-a)*s^a=1 := by rw [←Real.rpow_add hs];simp
  have htC : t^(-a)*t^a=1 := by rw [←Real.rpow_add ht];simp
  have he : -1-criticalRho a=-(2-2*a) := by dsimp [criticalRho];ring
  rw [he,Real.rpow_neg hp.le]
  calc
    _ = (s^(-a)*s^a)*(t^(-a)*t^a)*(u s*u t)*((s+t)^(2-2*a))⁻¹ := by ring
    _ = _ := by rw [hsC,htC];ring

/-- All triangular-cutoff integrability and the source square bound are
proved from the actual beta-row marginal, then additive-shear Fubini. -/
theorem weighted_convolution_triangle_le (a T : ℝ) (u : ℝ → ℝ) (ha : a<1) (hT : 0<T)
    (hu : ContinuousOn u (Ici 0)) (hun : ∀t≥0,0≤u t)
    (hi : IntegrableOn (fun t => u t^2*t^(-criticalRho a)) (Ioc 0 T)) :
    IntervalIntegrable (fun t => causalConvolution u u t*t^(-1-criticalRho a)) volume 0 T ∧
    cutoffI a u T≤
      (∫ z : ℝ×ℝ,Xi a z.1 z.2*amplitudeCutoff a u T z.1*amplitudeCutoff a u T z.2
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) := by
  let μ := volume.restrict (Ioi (0:ℝ))
  let P : Set (ℝ×ℝ) := Ioi 0×ˢIoi 0
  let F := fun z : ℝ×ℝ => Xi a z.1 z.2*amplitudeCutoff a u T z.1*amplitudeCutoff a u T z.2
  let G := P.indicator F
  let H := fun z : ℝ×ℝ => G (subtractShear z)
  have humeas : AEStronglyMeasurable u μ :=
    (hu.mono Ioi_subset_Ici_self).aestronglyMeasurable (μ:=volume) measurableSet_Ioi
  obtain ⟨hc,_,_⟩ := cutoff_square_identity a T u ha hT humeas hi
  have hG : Integrable G (volume.prod volume) := by
    apply (integrable_indicator_iff (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
    change Integrable F ((volume.prod volume).restrict P)
    simpa only [μ,P,Measure.prod_restrict] using hc
  have hShear : MeasurePreserving subtractShear (volume.prod volume) (volume.prod volume) := by
    convert measurePreserving_sub_prod (volume : Measure ℝ) volume using 1
    funext z
    exact subtractShear_apply z
  have hH : Integrable H (volume.prod volume) := hShear.integrable_comp_of_integrable hG
  have hGnonneg (z : ℝ×ℝ) : 0≤G z := by
    by_cases hz : z∈P
    · have hFnonneg : 0≤F z := by
        have hcut (s : ℝ) (hs : 0<s) : 0≤amplitudeCutoff a u T s := by
          by_cases hsT : s≤T
          · simp only [amplitudeCutoff,indicator_of_mem (show s∈Iic T from hsT)]
            exact mul_nonneg (Real.rpow_pos_of_pos hs _).le (hun s hs.le)
          · simp [amplitudeCutoff,hsT]
        exact mul_nonneg (mul_nonneg (Xi_nonnegative a z.1 z.2 hz.1.le hz.2.le) (hcut _ hz.1)) (hcut _ hz.2)
      simpa only [G,indicator_of_mem hz] using hFnonneg
    · simp [G,hz]
  have hHnonneg (z : ℝ×ℝ) : 0≤H z := hGnonneg (subtractShear z)
  have hInner (t : ℝ) (ht : t∈Ioc 0 T) :
      (∫ s,H (t,s))=causalConvolution u u t*t^(-1-criticalRho a) := by
    have heq : (fun s => H (t,s))=(Ioo 0 t).indicator (fun s => u (t-s)*u s*t^(-1-criticalRho a)) := by
      funext s
      by_cases hs : s∈Ioo 0 t
      · have hr : 0<t-s := sub_pos.mpr hs.2
        have hz : subtractShear (t,s)∈P := ⟨hr,hs.1⟩
        dsimp only [H,G]
        rw [indicator_of_mem hz,indicator_of_mem hs]
        change Xi a (t-s) s*amplitudeCutoff a u T (t-s)*amplitudeCutoff a u T s=_
        rw [kernel_amplitude_product a u T (t-s) s hr hs.1 (by linarith [ht.2,hs.1]) (hs.2.le.trans ht.2)]
        congr 1
        ring_nf
      · have hz : subtractShear (t,s)∉P := by
          change ¬(0<t-s ∧ 0<s)
          intro hz
          exact hs ⟨hz.2,by linarith [hz.1]⟩
        simp [H,G,hz,hs]
    rw [heq,integral_indicator measurableSet_Ioo,←integral_Ioc_eq_integral_Ioo,
      ←intervalIntegral.integral_of_le ht.1.le,intervalIntegral.integral_mul_const]
    rfl
  have hI : IntervalIntegrable (fun t => causalConvolution u u t*t^(-1-criticalRho a)) volume 0 T := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
    apply hH.integral_prod_left.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hInner t ht
  refine ⟨hI,?_⟩
  have hle : (∫ t in Ioc 0 T,∫ s,H (t,s))≤∫ t,∫ s,H (t,s) := by
    apply setIntegral_le_integral hH.integral_prod_left
    exact Eventually.of_forall (fun t => integral_nonneg (fun s => hHnonneg (t,s)))
  have hLeft : (∫ t in Ioc 0 T,∫ s,H (t,s))=cutoffI a u T := by
    rw [cutoffI,intervalIntegral.integral_of_le hT.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact hInner t ht
  rw [hLeft,←integral_prod _ hH] at hle
  have hfull : (∫ z : ℝ×ℝ,H z ∂volume.prod volume)=∫ z : ℝ×ℝ,G z ∂volume.prod volume :=
    hShear.integral_comp subtractShear.measurableEmbedding G
  rw [hfull,integral_indicator (measurableSet_Ioi.prod measurableSet_Ioi),←Measure.prod_restrict] at hle
  exact hle

end
end SphericalAging.StationaryTriangleIntegral
