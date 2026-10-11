module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

public section

/-! Constructed scalar spectral measures of actual bounded selfadjoint
operators on complex Hilbert space, using proved functional calculus and RMK. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped InnerProductSpace CompactlySupported
namespace SphericalAging.PositiveOperatorSpectralLaw

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[expose] def functional (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (v : H) :
    C_c(spectrum ℝ T,ℝ) →ₚ[ℝ] ℝ where
  toFun f := (inner ℂ ((cfcHom hT f.toContinuousMap) v) v).re
  map_add' f g := by
    change (inner ℂ ((cfcHom hT (f.toContinuousMap+g.toContinuousMap)) v) v).re=
      (inner ℂ ((cfcHom hT f.toContinuousMap) v) v).re+
      (inner ℂ ((cfcHom hT g.toContinuousMap) v) v).re
    rw [map_add,add_apply,inner_add_left,Complex.add_re]
  map_smul' a f := by
    change (inner ℂ ((cfcHom hT (a • f.toContinuousMap)) v) v).re=
      a*(inner ℂ ((cfcHom hT f.toContinuousMap) v) v).re
    simp [map_smul,smul_apply,inner_smul_left_eq_smul]
  monotone' := by
    intro f g hfg
    have hp : 0≤cfcHom hT (g.toContinuousMap-f.toContinuousMap) :=
      (cfcHom_nonneg_iff hT).mpr (fun x => sub_nonneg.mpr (hfg x))
    have hn := (ContinuousLinearMap.nonneg_iff_isPositive.mp hp).re_inner_nonneg_left v
    rw [map_sub,sub_apply,inner_sub_left] at hn
    change 0≤(inner ℂ ((cfcHom hT g.toContinuousMap) v) v).re-
      (inner ℂ ((cfcHom hT f.toContinuousMap) v) v).re at hn
    exact sub_nonneg.mp hn

@[expose] def spectralLaw (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (v : H) :
    Measure (spectrum ℝ T) := RealRMK.rieszMeasure (functional T hT v)

theorem integral_spectralLaw (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (v : H)
    (f : C_c(spectrum ℝ T,ℝ)) :
    (∫ x,f x ∂spectralLaw T hT v)=
      (inner ℂ ((cfcHom hT f.toContinuousMap) v) v).re :=
  RealRMK.integral_rieszMeasure (functional T hT v) f

theorem integral_continuous_spectralLaw (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (v : H)
    (f : C(spectrum ℝ T,ℝ)) :
    (∫ x,f x ∂spectralLaw T hT v)=
      (inner ℂ ((cfcHom hT f) v) v).re :=
  integral_spectralLaw T hT v ⟨f,HasCompactSupport.of_compactSpace f⟩

instance (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (v : H) :
    IsFiniteMeasure (spectralLaw T hT v) :=
  inferInstanceAs (IsFiniteMeasure (RealRMK.rieszMeasure (functional T hT v)))

theorem spectralLaw_probability (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (v : H) (hv : ‖v‖^2=1) : IsProbabilityMeasure (spectralLaw T hT v) := by
  let onecc : C_c(spectrum ℝ T,ℝ) :=
    CompactlySupportedContinuousMap.continuousMapEquiv (1 : C(spectrum ℝ T,ℝ))
  have h := integral_spectralLaw T hT v onecc
  have he : onecc.toContinuousMap=(1 : C(spectrum ℝ T,ℝ)) := rfl
  rw [he,map_one] at h
  change (∫ _ : spectrum ℝ T,(1:ℝ) ∂spectralLaw T hT v)=(inner ℂ v v).re at h
  rw [integral_const,smul_eq_mul,mul_one] at h
  have hi : (spectralLaw T hT v univ).toReal=1 := by
    calc
      _ = (inner ℂ v v).re := h
      _ = ‖v‖^2 := (norm_sq_eq_re_inner (𝕜:=ℂ) v).symm
      _ = 1 := hv
  constructor
  rw [←ENNReal.toReal_eq_one_iff]
  exact hi

end SphericalAging.PositiveOperatorSpectralLaw
