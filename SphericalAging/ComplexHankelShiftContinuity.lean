module

public import SphericalAging.ComplexHankelShift
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.InnerProductSpace.Adjoint

public section

/-! Strong continuity of the actually constructed Hankel shift semigroup. -/
noncomputable section
open Set Submodule
open scoped InnerProductSpace NNReal BoundedContinuousFunction
namespace SphericalAging.ComplexHankelShiftContinuity
open HankelReflection (HankelPositive)
open ComplexHankelShiftNorm ComplexHankelShift

theorem rawMap_time_continuous {c : ℝ → ℝ} (hc : HankelPositive c)
    (hcont : ContinuousOn c (Ici 0)) (f : ℝ≥0 →₀ ℂ) :
    Continuous (fun t : ℝ≥0 => rawMap c hc t f) := by
  classical
  simp only [rawMap,Finsupp.linearCombination_apply,Finsupp.sum]
  apply continuous_finsetSum
  intro a ha
  exact ((feature_continuous hc hcont).comp
    (continuous_const.add continuous_id)).const_smul (f a)

@[expose] def rawOrbit (c : ℝ → ℝ) (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (hcont : ContinuousOn c (Ici 0)) :
    (ℝ≥0 →₀ ℂ) →ₗ[ℂ] (ℝ≥0 →ᵇ Space c hc) where
  toFun f := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => rawMap c hc t f) (rawMap_time_continuous hc hcont f)
    ‖rawMap c hc 0 f‖ (fun t => rawMap_norm_contracts hc hb t f)
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro t
    exact (rawMap c hc t).map_add f g
  map_smul' a f := by
    apply BoundedContinuousFunction.ext
    intro t
    exact (rawMap c hc t).map_smul a f

@[simp] theorem rawOrbit_apply (c : ℝ → ℝ) (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (hcont : ContinuousOn c (Ici 0))
    (f : ℝ≥0 →₀ ℂ) (t : ℝ≥0) : rawOrbit c hc hb hcont f t=rawMap c hc t f := rfl

theorem rawOrbit_norm_le {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (hcont : ContinuousOn c (Ici 0)) (f : ℝ≥0 →₀ ℂ) :
    ‖rawOrbit c hc hb hcont f‖≤‖rawMap c hc 0 f‖ := by
  exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    (fun t => rawMap_norm_contracts hc hb t f)

@[expose] def orbit (c : ℝ → ℝ) (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (hcont : ContinuousOn c (Ici 0)) :
    Space c hc →L[ℂ] (ℝ≥0 →ᵇ Space c hc) :=
  (rawOrbit c hc hb hcont).extendOfNorm (rawMap c hc 0)

theorem orbit_rawMap {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (hcont : ContinuousOn c (Ici 0)) (f : ℝ≥0 →₀ ℂ) :
    orbit c hc hb hcont (rawMap c hc 0 f)=rawOrbit c hc hb hcont f := by
  apply LinearMap.extendOfNorm_eq (rawMap_dense c hc)
  exact ⟨1,fun f => by simpa only [one_mul] using rawOrbit_norm_le hc hb hcont f⟩

theorem orbit_apply {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (hcont : ContinuousOn c (Ici 0))
    (v : Space c hc) (t : ℝ≥0) : orbit c hc hb hcont v t=shift c hc t v := by
  have he : (BoundedContinuousFunction.evalCLM ℂ t).comp (orbit c hc hb hcont)=shift c hc t := by
    apply ext_features hc
    intro a
    have h := orbit_rawMap hc hb hcont (Finsupp.single a 1)
    have hval := congrArg (fun f : ℝ≥0 →ᵇ Space c hc => f t) h
    simpa only [rawMap_single,add_zero,one_smul,rawOrbit_apply,
      ContinuousLinearMap.comp_apply,BoundedContinuousFunction.evalCLM_apply,
      shift_feature hc hb] using hval
  exact congrArg (fun A : Space c hc →L[ℂ] Space c hc => A v) he

theorem shift_strongly_continuous {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (hcont : ContinuousOn c (Ici 0)) (v : Space c hc) :
    Continuous (fun t : ℝ≥0 => shift c hc t v) := by
  have he : (fun t => orbit c hc hb hcont v t)=(fun t => shift c hc t v) :=
    funext (fun t => orbit_apply hc hb hcont v t)
  rw [←he]
  exact (orbit c hc hb hcont v).continuous

theorem shift_selfAdjoint {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (t : ℝ≥0) : IsSelfAdjoint (shift c hc t) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro v w
  exact shift_inner_symmetric hc hb t v w


theorem shift_positive {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (t : ℝ≥0) :
    0≤shift c hc t := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  refine ⟨?_,?_⟩
  · intro v w
    exact shift_inner_symmetric hc hb t v w
  · intro v
    change 0≤(inner ℂ (shift c hc t v) v).re
    have ht : t/2+t/2=t := add_halves t
    rw [←ht,shift_add hc hb,ContinuousLinearMap.comp_apply,shift_inner_symmetric hc hb]
    exact inner_self_nonneg (𝕜:=ℂ)

theorem shift_opNorm_le {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (t : ℝ≥0) : ‖shift c hc t‖≤1 := by
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun v => by simpa only [one_mul] using shift_norm_le hc hb t v)

end SphericalAging.ComplexHankelShiftContinuity
