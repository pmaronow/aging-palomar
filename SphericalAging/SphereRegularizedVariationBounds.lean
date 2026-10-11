module

public import SphericalAging.SphereRegularizedNormBounds
public import SphericalAging.SphereGenerator

public section

/-! Integrable physical generator bounds and coordinate contractions for
the actual smooth tangent norm observable. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereRegularizedVariationBounds
open FiniteModel HardSphereDynamics LocalSDE SphereRegularizedNorm SphereRegularizedNormBounds
open LandscapeDerivatives SphereCurvatureHessianBound GaussianLandscape
open scoped InnerProductSpace BigOperators

theorem variationGenerator_tangent_norm_le {N p : ℕ} (hN : 2≤N) (hp : 2≤p)
    {ε β : ℝ} (hε : 0<ε) (hβ : 0≤β) (J : Disorder N p) (x v : Vector N)
    (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0) :
    ‖variationGenerator ε β J x v‖≤
      (β*(p:ℝ)^2*landscapeNorm N p J+((N:ℝ)-2)/(N:ℝ))*regularizedNorm ε v+
        Real.sqrt ε/(N:ℝ) := by
  have hn : 0<N := by omega
  have hr := regularizedNorm_pos hε v
  have hq : ‖v‖^2/regularizedNorm ε v≤regularizedNorm ε v := by
    apply (div_le_iff₀ hr).mpr
    nlinarith only [regularizedNorm_sq hε v,hε]
  have hcast : (2:ℝ)≤N := by exact_mod_cast hN
  have hgeom : 0≤((N:ℝ)-2)/(N:ℝ) := div_nonneg (sub_nonneg.mpr hcast) (Nat.cast_nonneg N)
  have hK : 0≤β*(p:ℝ)^2*landscapeNorm N p J :=
    mul_nonneg (mul_nonneg hβ (sq_nonneg _)) (landscapeNorm_nonnegative N p J)
  have hh : ‖β*⟪v,sphericalHessian J x v⟫_ℝ/regularizedNorm ε v‖≤
      (β*(p:ℝ)^2*landscapeNorm N p J)*regularizedNorm ε v := by
    rw [norm_div,norm_mul,Real.norm_of_nonneg hβ,Real.norm_of_nonneg hr.le]
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (sphericalHessian_quadratic_abs_bound hn hp J x v hx) hβ) hr.le
    have h' := mul_le_mul_of_nonneg_left hq hK
    rw [Real.norm_eq_abs]
    calc
      _ ≤ (β*(p:ℝ)^2*landscapeNorm N p J)*(‖v‖^2/regularizedNorm ε v) := by convert h using 1 <;> ring
      _ ≤ _ := h'
  have hg : ‖((N:ℝ)-2)/(N:ℝ)*‖v‖^2/regularizedNorm ε v‖≤
      ((N:ℝ)-2)/(N:ℝ)*regularizedNorm ε v := by
    rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg hgeom (sq_nonneg _)) hr.le)]
    convert mul_le_mul_of_nonneg_left hq hgeom using 1 <;> ring
  have he : ‖ε*‖v‖^2/((N:ℝ)*(regularizedNorm ε v)^3)‖≤Real.sqrt ε/(N:ℝ) := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact regularization_error_le hn hε v
  rw [variationGenerator_tangent hn hε β J x v hx hv]
  calc
    _ ≤ ‖β*⟪v,sphericalHessian J x v⟫_ℝ/regularizedNorm ε v-
        ((N:ℝ)-2)/(N:ℝ)*‖v‖^2/regularizedNorm ε v‖+
        ‖ε*‖v‖^2/((N:ℝ)*(regularizedNorm ε v)^3)‖ := norm_add_le _ _
    _ ≤ ‖β*⟪v,sphericalHessian J x v⟫_ℝ/regularizedNorm ε v‖+
        ‖((N:ℝ)-2)/(N:ℝ)*‖v‖^2/regularizedNorm ε v‖+
        ‖ε*‖v‖^2/((N:ℝ)*(regularizedNorm ε v)^3)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ _ := by nlinarith only [hh,hg,he]

theorem derivative_coordinates {N : ℕ} (D : Vector N →L[ℝ] ℝ) (b : Vector N) :
    (∑ i : Fin N,D (basisVector i)*b i)=D b := by
  conv_rhs => rw [← state_sum_basis b]
  simp only [map_sum,map_smul,smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem hessian_coordinates {N : ℕ} (H : Vector N →L[ℝ] Vector N →L[ℝ] ℝ)
    (σ : Fin N → Vector N) :
    (∑ i : Fin N,∑ k : Fin N,H (basisVector i) (basisVector k)*(∑ j : Fin N,σ j i*σ j k))=
      ∑ j : Fin N,H (σ j) (σ j) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm,SphereGenerator.bilinear_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

end SphericalAging.SphereRegularizedVariationBounds
