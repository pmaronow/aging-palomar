module

public import SphericalAging.AdaptiveGaussianRotation

public section

/-! Genuine orthogonal Gaussian regeneration on arbitrary finite Hilbert
spaces, for reuse inside a finite adaptive disclosure induction. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianSubspaceRegeneration
open Set MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

 theorem projection_law (K : Submodule ℝ E) :
    (stdGaussian E).map K.orthogonalProjectionOnto=stdGaussian K := by
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_stdGaussian,charFun_apply,integral_map (by fun_prop) (by fun_prop)]
  have hi z : ⟪K.orthogonalProjectionOnto z,x⟫_ℝ=⟪z,(x : E)⟫_ℝ := by
    simpa only [Submodule.adjoint_orthogonalProjectionOnto,Submodule.subtypeL_apply] using
      ((K.orthogonalProjectionOnto).adjoint_inner_right z x).symm
  simp_rw [hi]
  rw [←charFun_apply,charFun_stdGaussian]
  rfl

 theorem projections_independent (K : Submodule ℝ E) :
    IndepFun K.orthogonalProjectionOnto Kᗮ.orthogonalProjectionOnto (stdGaussian E) := by
  have hG := (IsGaussian.hasGaussianLaw_id (μ:=stdGaussian E)).map_fun
    (K.orthogonalProjectionOnto.prod Kᗮ.orthogonalProjectionOnto)
  apply hG.indepFun_of_covariance_inner
  intro a b
  change cov[fun x : E => ⟪a,K.orthogonalProjectionOnto x⟫_ℝ,
    fun x : E => ⟪b,Kᗮ.orthogonalProjectionOnto x⟫_ℝ;stdGaussian E]=0
  have h₁ : (fun x : E => ⟪a,K.orthogonalProjectionOnto x⟫_ℝ)=fun x => ⟪(a : E),x⟫_ℝ := by
    funext x
    simpa only [Submodule.adjoint_orthogonalProjectionOnto,Submodule.subtypeL_apply] using
      ((K.orthogonalProjectionOnto).adjoint_inner_left x a).symm
  have h₂ : (fun x : E => ⟪b,Kᗮ.orthogonalProjectionOnto x⟫_ℝ)=fun x => ⟪(b : E),x⟫_ℝ := by
    funext x
    simpa only [Submodule.adjoint_orthogonalProjectionOnto,Submodule.subtypeL_apply] using
      ((Kᗮ.orthogonalProjectionOnto).adjoint_inner_left x b).symm
  rw [h₁,h₂,←covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,covarianceBilin_stdGaussian,
    innerSL_apply_apply]
  exact Submodule.inner_right_of_mem_orthogonal a.property b.property

 theorem projection_pair_law (K : Submodule ℝ E) :
    (stdGaussian E).map (fun x => (K.orthogonalProjectionOnto x,Kᗮ.orthogonalProjectionOnto x))=
      (stdGaussian K).prod (stdGaussian Kᗮ) := by
  rw [(projections_independent K).map_prod_eq_prod_map_map (by fun_prop) (by fun_prop),
    projection_law,projection_law]

end SphericalAging.GaussianSubspaceRegeneration
