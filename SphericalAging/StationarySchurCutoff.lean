module

public import SphericalAging.StationarySchurAlgebra

public section

/-! Actual finite-cutoff Schur marginal, diagonal and square identities. -/
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SphericalAging.StationarySchurCutoff
noncomputable section
open DirichletKernel StationaryCutoffBalance StationarySchurAlgebra

@[expose] def amplitudeCutoff (a : ℝ) (u : ℝ → ℝ) (T t : ℝ) :=
  (Iic T).indicator (fun s => s^a*u s) t

theorem amplitudeCutoff_measurable (a T : ℝ) (u : ℝ → ℝ)
    (hu : AEStronglyMeasurable u (volume.restrict (Ioi 0))) :
    AEStronglyMeasurable (amplitudeCutoff a u T) (volume.restrict (Ioi 0)) := by
  exact (((by fun_prop : Measurable (fun s : ℝ => s^a)).aestronglyMeasurable.mul hu).indicator measurableSet_Iic)

theorem cutoff_amplitude_square_weight (a : ℝ) (u : ℝ → ℝ) (T s : ℝ) (hs : 0<s) :
    amplitudeCutoff a u T s^2/s=
      (Ioc 0 T).indicator (fun s => u s^2*s^(-criticalRho a)) s := by
  by_cases hT : s≤T
  · rw [amplitudeCutoff,indicator_of_mem (show s∈Iic T from hT),indicator_of_mem (show s∈Ioc 0 T from ⟨hs,hT⟩)]
    rw [mul_pow,←Real.rpow_natCast (s^a) 2,←Real.rpow_mul hs.le]
    rw [div_eq_mul_inv,←Real.rpow_neg_one]
    have he : 2*a+(-1) = -criticalRho a := by dsimp [criticalRho];ring
    norm_num only [Nat.cast_ofNat]
    rw [show a*(2:ℝ)=2*a by ring]
    calc
      s^(2*a)*u s^2*s^(-1:ℝ)=u s^2*(s^(2*a)*s^(-1:ℝ)) := by ring
      _ = _ := by rw [←Real.rpow_add hs,he]
  · simp [amplitudeCutoff,hT,show s∉Ioc 0 T from fun h => hT h.2]

/-- Genuine product-integral diagonal. The beta row identity proves all
marginal integrability; the square identity is then an ordinary integral
identity, with no assumed Schur theorem. -/
theorem cutoff_diagonal_identity (a T : ℝ) (u : ℝ → ℝ) (ha : a<1) (hT : 0<T)
    (hu : AEStronglyMeasurable u (volume.restrict (Ioi 0)))
    (hi : IntegrableOn (fun t => u t^2*t^(-criticalRho a)) (Ioc 0 T)) :
    Integrable (fun z : ℝ×ℝ => Xi a z.1 z.2*amplitudeCutoff a u T z.1^2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) ∧
    (∫ z : ℝ×ℝ,Xi a z.1 z.2*amplitudeCutoff a u T z.1^2
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))=
      schurBeta a*(∫ t in 0..T,u t^2*t^(-criticalRho a)) := by
  let μ := volume.restrict (Ioi (0:ℝ))
  let f := amplitudeCutoff a u T
  let C := schurBeta a
  have hf : AEStronglyMeasurable f μ := amplitudeCutoff_measurable a T u hu
  have hAE : AEStronglyMeasurable (fun z : ℝ×ℝ => Xi a z.1 z.2*f z.1^2) (μ.prod μ) :=
    (Xi_measurable a).aestronglyMeasurable.mul (hf.comp_fst.pow 2)
  have hRow (s : ℝ) (hs : 0<s) : Integrable (fun t => Xi a s t*f s^2) μ :=
    (Xi_row_integrable ha hs).mul_const (f s^2)
  have hMarg (s : ℝ) (hs : 0<s) :
      (∫ t,‖Xi a s t*f s^2‖ ∂μ)=C*((Ioc 0 T).indicator (fun s => u s^2*s^(-criticalRho a))) s := by
    have he : (∫ t,‖Xi a s t*f s^2‖ ∂μ)=(∫ t,Xi a s t*f s^2 ∂μ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change ‖Xi a s t*f s^2‖=Xi a s t*f s^2
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Xi_nonnegative a s t hs.le ht.le) (sq_nonneg _))]
    rw [he,integral_mul_const,integral_Xi_row ha hs]
    change C/s*f s^2=C*((Ioc 0 T).indicator (fun s => u s^2*s^(-criticalRho a))) s
    rw [show C/s*f s^2=C*(f s^2/s) by ring,cutoff_amplitude_square_weight a u T s hs]
  have hGlobal : Integrable ((Ioc 0 T).indicator (fun s => u s^2*s^(-criticalRho a))) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr hi
  have hOuter : Integrable (fun s => ∫ t,‖Xi a s t*f s^2‖ ∂μ) μ := by
    apply (hGlobal.integrableOn.const_mul C).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hMarg s hs).symm
  have hDiag : Integrable (fun z : ℝ×ℝ => Xi a z.1 z.2*f z.1^2) (μ.prod μ) := by
    apply (integrable_prod_iff hAE).mpr
    refine ⟨?_,hOuter⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hRow s hs
  refine ⟨hDiag,?_⟩
  rw [integral_prod _ hDiag]
  have hInner : (∫ s,∫ t,Xi a s t*f s^2 ∂μ ∂μ)=
      C*(∫ s,((Ioc 0 T).indicator (fun s => u s^2*s^(-criticalRho a))) s ∂μ) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [integral_mul_const,integral_Xi_row ha hs]
    change C/s*f s^2=C*((Ioc 0 T).indicator (fun s => u s^2*s^(-criticalRho a))) s
    rw [show C/s*f s^2=C*(f s^2/s) by ring,cutoff_amplitude_square_weight a u T s hs]
  rw [hInner]
  congr 1
  change (∫ s in Ioi 0,((Ioc 0 T).indicator (fun s => u s^2*s^(-criticalRho a))) s)=_
  rw [setIntegral_indicator measurableSet_Ioc]
  have hset : Ioi (0:ℝ)∩Ioc 0 T=Ioc 0 T := inter_eq_right.mpr Ioc_subset_Ioi_self
  rw [hset,intervalIntegral.integral_of_le hT.le]

/-- Actual cutoffs satisfy the symmetric square identity, including cross
and energy integrability. -/
theorem cutoff_square_identity (a T : ℝ) (u : ℝ → ℝ) (ha : a<1) (hT : 0<T)
    (hu : AEStronglyMeasurable u (volume.restrict (Ioi 0)))
    (hi : IntegrableOn (fun t => u t^2*t^(-criticalRho a)) (Ioc 0 T)) :
    Integrable (fun z : ℝ×ℝ => Xi a z.1 z.2*amplitudeCutoff a u T z.1*amplitudeCutoff a u T z.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) ∧
    Integrable (fun z : ℝ×ℝ => Xi a z.1 z.2*(amplitudeCutoff a u T z.1-amplitudeCutoff a u T z.2)^2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) ∧
    (∫ z : ℝ×ℝ,Xi a z.1 z.2*(amplitudeCutoff a u T z.1-amplitudeCutoff a u T z.2)^2
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))/2=
      schurBeta a*(∫ t in 0..T,u t^2*t^(-criticalRho a))-
      (∫ z : ℝ×ℝ,Xi a z.1 z.2*amplitudeCutoff a u T z.1*amplitudeCutoff a u T z.2
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) := by
  let μ := volume.restrict (Ioi (0:ℝ))
  obtain ⟨hd,hdiag⟩ := cutoff_diagonal_identity a T u ha hT hu hi
  have hn : ∀ᵐ z : ℝ×ℝ ∂μ.prod μ,0≤Xi a z.1 z.2 := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with z hz
    exact Xi_nonnegative a z.1 z.2 hz.1.le hz.2.le
  obtain ⟨hc,he,hid⟩ := symmetric_kernel_square_identity μ (fun z => Xi a z.1 z.2)
    (amplitudeCutoff a u T) (Xi_measurable a).aestronglyMeasurable
    (amplitudeCutoff_measurable a T u hu) hn (Xi_symmetric a) hd
  rw [hdiag] at hid
  exact ⟨hc,he,hid⟩

end
end SphericalAging.StationarySchurCutoff
