module

public import SphericalAging.ScalarHilbertKernel

public section

/-! The genuine complex Moore space of a real positive kernel. This supplies
the complex Hilbert operator algebra required by Mathlib's functional calculus. -/
noncomputable section
open scoped InnerProductSpace ComplexConjugate NNReal
open Set
namespace SphericalAging.ComplexHilbertKernel
open ScalarHilbertKernel

@[expose] def operatorKernel {X : Type} (K : PositiveKernel X) : Matrix X X (ℂ →L[ℂ] ℂ) :=
  fun x y => (K.value x y : ℂ) • ContinuousLinearMap.id ℂ ℂ

theorem operatorKernel_posSemidef {X : Type} (K : PositiveKernel X) :
    (operatorKernel K).PosSemidef := by
  classical
  apply RKHS.posSemidef_iff_re_sum_kernel'.mpr
  refine ⟨?_,?_⟩
  · ext x y
    simp [Matrix.conjTranspose_apply,operatorKernel,star_smul,K.symmetric,
      ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_id]
  · intro a
    have hr := finite_positive_finset K a.support (fun x => (a x).re)
    have hi := finite_positive_finset K a.support (fun x => (a x).im)
    have he :
        (a.sum fun x w => a.sum fun y z =>
          inner ℂ (operatorKernel K y x w) z).re=
        (∑ x ∈ a.support,∑ y ∈ a.support,(a x).re*(a y).re*K.value x y)+
        (∑ x ∈ a.support,∑ y ∈ a.support,(a x).im*(a y).im*K.value x y) := by
      simp only [Finsupp.sum,operatorKernel,smul_apply,
        ContinuousLinearMap.id_apply,smul_eq_mul,RCLike.inner_apply,
        Complex.re_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [K.symmetric y x]
      simp only [map_mul,Complex.conj_re,Complex.conj_im,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
      ring
    change 0≤(a.sum fun x w => a.sum fun y z => inner ℂ (operatorKernel K y x w) z).re
    rw [he]
    exact add_nonneg hr hi

instance {X : Type} (K : PositiveKernel X) : Fact (operatorKernel K).PosSemidef :=
  ⟨operatorKernel_posSemidef K⟩

@[expose] abbrev Space {X : Type} (K : PositiveKernel X) := RKHS.OfKernel (operatorKernel K)

@[expose] def feature {X : Type} (K : PositiveKernel X) (x : X) : Space K :=
  RKHS.kerFun (Space K) x 1

@[simp] theorem feature_inner {X : Type} (K : PositiveKernel X) (x y : X) :
    inner ℂ (feature K x) (feature K y)=(K.value x y : ℂ) := by
  have hh := RKHS.kernel_inner (Space K) y x (1:ℂ) (1:ℂ)
  rw [RKHS.OfKernel.kernel_ofKernel] at hh
  simpa [feature,operatorKernel,K.symmetric] using hh.symm

@[simp] theorem feature_norm_sq {X : Type} (K : PositiveKernel X) (x : X) :
    ‖feature K x‖^2=K.value x x := by
  rw [norm_sq_eq_re_inner (𝕜:=ℂ),feature_inner]
  rfl

theorem feature_norm_sub_sq {X : Type} (K : PositiveKernel X) (x y : X) :
    ‖feature K x-feature K y‖^2=K.value x x-2*K.value x y+K.value y y := by
  rw [norm_sub_sq (𝕜:=ℂ),feature_norm_sq,feature_norm_sq,feature_inner]
  rfl

theorem feature_continuous {X : Type} [TopologicalSpace X] (K : PositiveKernel X)
    (hK : Continuous (Function.uncurry K.value)) : Continuous (feature K) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have hnorm (y : X) : ‖feature K y-feature K x‖=
      Real.sqrt (K.value y y-2*K.value y x+K.value x x) := by
    rw [←feature_norm_sub_sq,Real.sqrt_sq (norm_nonneg _)]
  simp_rw [hnorm]
  have hdiag : Continuous (fun y : X => K.value y y) :=
    hK.comp (continuous_id.prodMk continuous_id)
  have hcol : Continuous (fun y : X => K.value y x) :=
    hK.comp (continuous_id.prodMk continuous_const)
  have hpoly : ContinuousAt (fun y : X => K.value y y-2*K.value y x+K.value x x) x :=
    (hdiag.continuousAt.sub (hcol.continuousAt.const_mul 2)).add continuousAt_const
  have hp := hpoly.sqrt
  change Filter.Tendsto (fun y : X => Real.sqrt (K.value y y-2*K.value y x+K.value x x))
    (nhds x) (nhds (Real.sqrt (K.value x x-2*K.value x x+K.value x x))) at hp
  have hz : K.value x x-2*K.value x x+K.value x x=0 := by ring
  simpa only [hz,Real.sqrt_zero] using hp

end SphericalAging.ComplexHilbertKernel
