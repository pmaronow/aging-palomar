module

public import SphericalAging.PhysicalC2Ito

public section

/-! Exact physical noise contraction and tangent gradient bounds for
arbitrary actual scalar test functions. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace SphericalAging.SphereNoiseGradient
open HardSphereDynamics LocalSDE
set_option maxHeartbeats 1200000
variable {N : ℕ}

/-- The physical sphere diffusion measures twice the squared tangent gradient. -/
theorem noise_gradient_square_sum (f : State N → ℝ) (x : State N) :
    (∑ j : Fin N,(fderiv ℝ f x (noiseColumn x j))^2)=
      2*‖projection x (gradient f x)‖^2 := by
  have ht (j : Fin N) : fderiv ℝ f x (noiseColumn x j)=
      Real.sqrt 2*(projection x (gradient f x)) j := by
    rw [← inner_gradient_left,noiseColumn,real_inner_smul_right,
      ← projection_self_adjoint,basis_inner]
  simp_rw [ht,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  rw [← Finset.mul_sum,coordinate_square_sum,real_inner_self_eq_norm_sq]

/-- A true tangent-direction derivative bound controls the full tangent
score with no factor equal to the ambient dimension. -/
theorem tangent_gradient_norm_le (hN : N≠0) (f : State N → ℝ)
    (x : State N) (hx : OnSphere x) (K : ℝ) (hK : 0≤K)
    (hb : ∀ v,‖fderiv ℝ f x (projection x v)‖≤K*‖v‖) :
    ‖projection x (gradient f x)‖≤K := by
  have hi : ⟪gradient f x,projection x (gradient f x)⟫_ℝ=
      ‖projection x (gradient f x)‖^2 := by
    calc
      _ = ⟪projection x (gradient f x),projection x (gradient f x)⟫_ℝ := by
        rw [projection_self_adjoint,projection_idempotent hN x _ hx]
      _ = _ := real_inner_self_eq_norm_sq _
  have hh := hb (projection x (gradient f x))
  rw [projection_idempotent hN x _ hx,← inner_gradient_left,hi,
    Real.norm_of_nonneg (sq_nonneg _)] at hh
  nlinarith [norm_nonneg (projection x (gradient f x))]

/-- Genuine dimension-free noise carré-du-champ bound from the actual
projected spatial derivative. -/
theorem noise_gradient_square_sum_le (hN : N≠0) (f : State N → ℝ)
    (x : State N) (hx : OnSphere x) (K : ℝ) (hK : 0≤K)
    (hb : ∀ v,‖fderiv ℝ f x (projection x v)‖≤K*‖v‖) :
    (∑ j : Fin N,(fderiv ℝ f x (noiseColumn x j))^2)≤2*K^2 := by
  rw [noise_gradient_square_sum]
  have hh := tangent_gradient_norm_le hN f x hx K hK hb
  gcongr

end SphericalAging.SphereNoiseGradient
