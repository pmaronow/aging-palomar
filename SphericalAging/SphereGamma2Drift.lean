module

public import SphericalAging.SphereCasimirGamma2
public import SphericalAging.SphereCanonicalGenerator
public import SphericalAging.SphereCurvatureHessianBound

public section

/-! The actual Hamiltonian contribution to canonical spherical Γ₂. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereGamma2Drift

open FiniteModel HardSphereDynamics SphericalIntegrationByParts SphereRotationGeometry
open SphereGeneratorIntegrationByParts SphereGeneratorAlgebra SphereGamma2Algebra SphereFisherDissipation
open SphereCasimir SphereCasimirGamma2 SphereCanonicalGenerator LandscapeDerivatives
open scoped BigOperators InnerProductSpace

theorem coordinate_commutator_score_sum_zero {N : ℕ} (k l : Fin N)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (x : Vector N) :
    (∑ i : Fin N, ∑ j : Fin N, lieDerivative (coordinateRotation i j) f x *
      (lieDerivative (coordinateRotation k l) (lieDerivative (coordinateRotation i j) f) x -
        lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation k l) f) x)) = 0 := by
  classical
  simp_rw [coordinate_lieDerivative_commutator _ _ _ _ hf x, mul_sub, mul_add]
  have ht (a b : Fin N) (c d : ℝ) : c*((if a=b then (1 : ℝ) else 0)*d) =
      (if a=b then c*d else 0) := by
    by_cases h : a=b <;> simp [h]
  simp_rw [ht, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const_zero]
  have he (i : Fin N) : lieDerivative (coordinateRotation i l) f x *
      lieDerivative (coordinateRotation k i) f x =
      lieDerivative (coordinateRotation i k) f x * lieDerivative (coordinateRotation l i) f x := by
    rw [coordinate_lieDerivative_swap l, coordinate_lieDerivative_swap k]
    ring
  simp_rw [he]
  have hc (j : Fin N) : lieDerivative (coordinateRotation k j) f x *
      lieDerivative (coordinateRotation l j) f x =
      lieDerivative (coordinateRotation l j) f x * lieDerivative (coordinateRotation k j) f x := by ring
  simp_rw [hc]
  ring

theorem coordinate_rotationGamma_invariant {N : ℕ} (κ : ℝ) (k l : Fin N)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (x : Vector N) :
    lieDerivative (coordinateRotation k l) (rotationGamma κ (rotations N) f f) x =
      2*rotationGamma κ (rotations N) f (lieDerivative (coordinateRotation k l) f) x := by
  classical
  have hD (i j : Fin N) : ContDiff ℝ 1 (lieDerivative (coordinateRotation i j) f) :=
    lieDerivative_contDiff_order _ hf
  have hSq (i j : Fin N) : ContDiff ℝ 1
      (fun y => (lieDerivative (coordinateRotation i j) f y)^2) := (hD i j).pow 2
  have hRow (i : Fin N) : ContDiff ℝ 1
      (fun y => ∑ j : Fin N, (lieDerivative (coordinateRotation i j) f y)^2) :=
    ContDiff.sum (s := Finset.univ) (fun j _ => hSq i j)
  have hS : ContDiff ℝ 1
      (fun y => ∑ i : Fin N, ∑ j : Fin N, (lieDerivative (coordinateRotation i j) f y)^2) :=
    ContDiff.sum (s := Finset.univ) (fun i _ => hRow i)
  rw [rotationGamma_self_eq_square_sum, lieDerivative_const_mul _ κ hS,
    lieDerivative_sum _ _ hRow]
  simp_rw [lieDerivative_sum _ _ (hSq _)]
  have hterm i j : lieDerivative (coordinateRotation k l)
      (fun y => (lieDerivative (coordinateRotation i j) f y)^2) x =
      2*(lieDerivative (coordinateRotation i j) f x *
        lieDerivative (coordinateRotation k l) (lieDerivative (coordinateRotation i j) f) x) := by
    have he : (fun y => (lieDerivative (coordinateRotation i j) f y)^2) =
        (fun y => lieDerivative (coordinateRotation i j) f y*lieDerivative (coordinateRotation i j) f y) := by
      funext y
      ring
    rw [he, lieDerivative_mul _ (hD i j) (hD i j)]
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  unfold rotationGamma
  simp only [rotations, Fintype.sum_prod_type]
  have hh := coordinate_commutator_score_sum_zero k l hf x
  simp only [mul_sub, Finset.sum_sub_distrib] at hh
  rw [sub_eq_zero.mp hh]
  ring

theorem lieDerivative_rotationGamma {N : ℕ} {ι : Type*} [Fintype ι]
    (κ : ℝ) (A : ι → Operator N) (B : Operator N) {f g : Vector N → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Vector N) :
    lieDerivative B (rotationGamma κ A f g) x =
      κ*(∑ a, (lieDerivative (A a) f x * lieDerivative B (lieDerivative (A a) g) x +
        lieDerivative (A a) g x * lieDerivative B (lieDerivative (A a) f) x)) := by
  classical
  have hterm a : ContDiff ℝ 1 (fun y => lieDerivative (A a) f y * lieDerivative (A a) g y) :=
    (lieDerivative_contDiff_order _ hf).mul (lieDerivative_contDiff_order _ hg)
  have hsum : ContDiff ℝ 1 (fun y => ∑ a, lieDerivative (A a) f y * lieDerivative (A a) g y) :=
    ContDiff.sum (s := Finset.univ) (fun a _ => hterm a)
  unfold rotationGamma
  rw [lieDerivative_const_mul _ κ hsum, lieDerivative_sum _ _ hterm]
  simp_rw [lieDerivative_mul _ (lieDerivative_contDiff_order _ hf)
    (lieDerivative_contDiff_order _ hg)]

theorem rotationGamma_drift_eq_second_rotation_sum {N : ℕ} (κ : ℝ)
    {H f : Vector N → ℝ} (hH : ContDiff ℝ 2 H) (hf : ContDiff ℝ 2 f) (x : Vector N) :
    (1/2)*rotationGamma κ (rotations N) H (rotationGamma κ (rotations N) f f) x -
      rotationGamma κ (rotations N) f (rotationGamma κ (rotations N) H f) x =
      -κ^2*(∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        lieDerivative (coordinateRotation i j) f x * lieDerivative (coordinateRotation k l) f x *
          lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation k l) H) x) := by
  classical
  have hfirst : (1/2)*rotationGamma κ (rotations N) H (rotationGamma κ (rotations N) f f) x =
      κ^2*(∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        lieDerivative (coordinateRotation k l) H x * lieDerivative (coordinateRotation i j) f x *
          lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation k l) f) x) := by
    change (1/2)*(κ*(∑ a : Fin N × Fin N, lieDerivative (rotations N a) H x *
      lieDerivative (rotations N a) (rotationGamma κ (rotations N) f f) x)) = _
    simp only [rotations, Fintype.sum_prod_type]
    simp_rw [coordinate_rotationGamma_invariant κ _ _ hf x]
    unfold rotationGamma
    simp only [rotations, Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum]
    have ht (k l i j : Fin N) : (1/2)*(κ*(lieDerivative (coordinateRotation k l) H x *
        (2*(κ*(lieDerivative (coordinateRotation i j) f x *
          lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation k l) f) x))))) =
        κ^2*(lieDerivative (coordinateRotation k l) H x * lieDerivative (coordinateRotation i j) f x *
          lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation k l) f) x) := by ring
    simp_rw [ht]
    simp_rw [← Finset.mul_sum]
    congr 1
    let T (k l i j : Fin N) := lieDerivative (coordinateRotation k l) H x *
      lieDerivative (coordinateRotation i j) f x *
      lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation k l) f) x
    change (∑ k : Fin N, ∑ l : Fin N, ∑ i : Fin N, ∑ j : Fin N, T k l i j) =
      (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, T k l i j)
    calc
      _ = ∑ k : Fin N, ∑ i : Fin N, ∑ l : Fin N, ∑ j : Fin N, T k l i j := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
      _ = ∑ i : Fin N, ∑ k : Fin N, ∑ l : Fin N, ∑ j : Fin N, T k l i j := by
        rw [Finset.sum_comm]
      _ = ∑ i : Fin N, ∑ k : Fin N, ∑ j : Fin N, ∑ l : Fin N, T k l i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
  have hsecond : rotationGamma κ (rotations N) f (rotationGamma κ (rotations N) H f) x =
      κ^2*(∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        (lieDerivative (coordinateRotation k l) H x * lieDerivative (coordinateRotation i j) f x *
          lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation k l) f) x +
        lieDerivative (coordinateRotation i j) f x * lieDerivative (coordinateRotation k l) f x *
          lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation k l) H) x)) := by
    unfold rotationGamma
    change κ*(∑ a : Fin N × Fin N, lieDerivative (rotations N a) f x *
      lieDerivative (rotations N a) (rotationGamma κ (rotations N) H f) x) = _
    simp_rw [lieDerivative_rotationGamma κ (rotations N) _ hH hf x]
    simp only [rotations, Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hfirst, hsecond]
  simp only [Finset.sum_add_distrib]
  ring

theorem coordinate_rotation_weighted_action {N : ℕ} (x z w : Vector N) :
    (∑ i : Fin N, ∑ j : Fin N, (x j*z i-x i*z j) • coordinateRotation i j w) =
      (2 : ℝ) • (⟪x,w⟫_ℝ • z - ⟪z,w⟫_ℝ • x) := by
  classical
  apply PiLp.ext
  intro a
  change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) a)
      (∑ i : Fin N, ∑ j : Fin N, (x j*z i-x i*z j) • coordinateRotation i j w) = _
  rw [map_sum]
  simp_rw [map_sum, map_smul]
  simp only [PiLp.proj_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  simp_rw [coordinateRotation_apply_coordinate]
  simp only [basisVector, PiLp.single_apply]
  have ht (i j : Fin N) : (x j*z i-x i*z j) *
      (w j*(if i=a then (1 : ℝ) else 0)-w i*(if j=a then (1 : ℝ) else 0)) =
      (if i=a then (x j*z i-x i*z j)*w j else 0) -
        (if j=a then (x j*z i-x i*z j)*w i else 0) := by
    by_cases hi : i=a <;> by_cases hj : j=a <;> simp [hi,hj]
  simp_rw [ht, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const_zero]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  have hp (b : Fin N) : x b*z a*w b = z a*(x b*w b) := by ring
  have hq (b : Fin N) : x a*z b*w b = x a*(z b*w b) := by ring
  simp_rw [hp, hq, ← Finset.mul_sum]
  rw [real_inner_coordinates x w, real_inner_coordinates z w]
  ring

theorem canonical_weighted_rotation_action {N : ℕ} (hN : 0<N)
    (f : Vector N → ℝ) (x w : Vector N) :
    (1/(2*(N : ℝ))) • (∑ i : Fin N, ∑ j : Fin N,
      lieDerivative (coordinateRotation i j) f x • coordinateRotation i j w) =
      (⟪x,w⟫_ℝ/(N : ℝ)) • gradient f x -
        (⟪gradient f x,w⟫_ℝ/(N : ℝ)) • x := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  simp_rw [lieDerivative_coordinate]
  rw [coordinate_rotation_weighted_action]
  simp only [smul_sub, smul_smul]
  congr 1 <;> congr 1 <;> field_simp

theorem canonical_rotation_score_sum {N : ℕ} (hN : 0<N)
    (f : Vector N → ℝ) (x : Vector N) (hx : OnSphere x) :
    (1/(2*(N : ℝ))) • (∑ i : Fin N, ∑ j : Fin N,
      lieDerivative (coordinateRotation i j) f x • coordinateRotation i j x) =
      projection x (gradient f x) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [canonical_weighted_rotation_action hN, hx, div_self hn, one_smul]
  simp only [projection, real_inner_comm]

theorem canonical_rotation_acceleration_sum {N : ℕ} (hN : 0<N)
    (f : Vector N → ℝ) (x : Vector N) (hx : OnSphere x) :
    (1/(2*(N : ℝ)))^2 • (∑ a : Fin N × Fin N, ∑ b : Fin N × Fin N,
      (lieDerivative (rotations N a) f x * lieDerivative (rotations N b) f x) •
        rotations N b (rotations N a x)) =
      -(‖projection x (gradient f x)‖^2/(N : ℝ)) • x := by
  classical
  let κ : ℝ := 1/(2*(N : ℝ))
  let c (a : Fin N × Fin N) := lieDerivative (rotations N a) f x
  have hS : κ • (∑ a : Fin N × Fin N, c a • rotations N a x) = projection x (gradient f x) := by
    simpa only [κ, c, rotations, Fintype.sum_prod_type] using canonical_rotation_score_sum hN f x hx
  have hT : κ^2 • (∑ a : Fin N × Fin N, ∑ b : Fin N × Fin N,
      (c a*c b) • rotations N b (rotations N a x)) =
      κ • (∑ b : Fin N × Fin N, c b • rotations N b
        (κ • (∑ a : Fin N × Fin N, c a • rotations N a x))) := by
    simp only [map_smul, map_sum, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ring
  change κ^2 • (∑ a : Fin N × Fin N, ∑ b : Fin N × Fin N,
    (c a*c b) • rotations N b (rotations N a x)) = _
  rw [hT, hS]
  have hA : κ • (∑ b : Fin N × Fin N, c b • rotations N b (projection x (gradient f x))) =
      (⟪x,projection x (gradient f x)⟫_ℝ/(N : ℝ)) • gradient f x -
        (⟪gradient f x,projection x (gradient f x)⟫_ℝ/(N : ℝ)) • x := by
    simpa only [κ, c, rotations, Fintype.sum_prod_type] using
      canonical_weighted_rotation_action hN f x (projection x (gradient f x))
  rw [hA, projection_tangent (Nat.ne_of_gt hN) x _ hx, zero_div, zero_smul, zero_sub]
  have hi : ⟪gradient f x, projection x (gradient f x)⟫_ℝ = ‖projection x (gradient f x)‖^2 := by
    calc
      _ = ⟪gradient f x, projection x (projection x (gradient f x))⟫_ℝ := by
        rw [projection_idempotent (Nat.ne_of_gt hN) x (gradient f x) hx]
      _ = ⟪projection x (gradient f x), projection x (gradient f x)⟫_ℝ :=
        (projection_self_adjoint x _ _).symm
      _ = _ := real_inner_self_eq_norm_sq _
  rw [hi, neg_smul]

theorem canonical_rotation_bilinear_score_sum {N : ℕ} (hN : 0<N)
    (f : Vector N → ℝ) (x : Vector N) (hx : OnSphere x)
    (B : Vector N →L[ℝ] Vector N →L[ℝ] ℝ) :
    (1/(2*(N : ℝ)))^2 * (∑ a : Fin N × Fin N, ∑ b : Fin N × Fin N,
      lieDerivative (rotations N a) f x * lieDerivative (rotations N b) f x *
        B (rotations N a x) (rotations N b x)) =
      B (projection x (gradient f x)) (projection x (gradient f x)) := by
  classical
  have hS : (1/(2*(N : ℝ))) • (∑ a : Fin N × Fin N,
      lieDerivative (rotations N a) f x • rotations N a x) = projection x (gradient f x) := by
    simpa only [rotations, Fintype.sum_prod_type] using canonical_rotation_score_sum hN f x hx
  rw [← hS]
  simp only [map_smul, map_sum, smul_apply, sum_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem canonical_rotation_second_sum_eq_extrinsic_hessian {N : ℕ} (hN : 0<N)
    {H f : Vector N → ℝ} (hH : ContDiff ℝ 2 H) (x : Vector N) (hx : OnSphere x) :
    (1/(2*(N : ℝ)))^2 * (∑ a : Fin N × Fin N, ∑ b : Fin N × Fin N,
      lieDerivative (rotations N a) f x * lieDerivative (rotations N b) f x *
        lieDerivative (rotations N a) (lieDerivative (rotations N b) H) x) =
      fderiv ℝ (fderiv ℝ H) x (projection x (gradient f x)) (projection x (gradient f x)) -
        (⟪x,gradient H x⟫_ℝ/(N : ℝ))*‖projection x (gradient f x)‖^2 := by
  classical
  have hA : (1/(2*(N : ℝ)))^2 * (∑ a : Fin N × Fin N, ∑ b : Fin N × Fin N,
      lieDerivative (rotations N a) f x * lieDerivative (rotations N b) f x *
        fderiv ℝ H x (rotations N b (rotations N a x))) =
      -(⟪x,gradient H x⟫_ℝ/(N : ℝ))*‖projection x (gradient f x)‖^2 := by
    have he := congrArg (fun v => fderiv ℝ H x v) (canonical_rotation_acceleration_sum hN f x hx)
    simp only [map_smul, map_sum, smul_eq_mul] at he
    rw [← inner_gradient_left] at he
    rw [real_inner_comm x (gradient H x)] at he
    convert he using 1
    ring
  simp_rw [lieDerivative_twice_fderiv _ _ hH, mul_add, Finset.sum_add_distrib]
  rw [mul_add, canonical_rotation_bilinear_score_sum hN f x hx, hA]
  ring

theorem fderiv_gradient_inner {N : ℕ} (H : Vector N → ℝ) (x v w : Vector N) :
    ⟪fderiv ℝ (gradient H) x v,w⟫_ℝ = fderiv ℝ (fderiv ℝ H) x v w := by
  change ⟪fderiv ℝ ((InnerProductSpace.toDual ℝ (Vector N)).symm ∘ fderiv ℝ H) x v,w⟫_ℝ = _
  rw [LinearIsometryEquiv.comp_fderiv]
  change ⟪(InnerProductSpace.toDual ℝ (Vector N)).symm (fderiv ℝ (fderiv ℝ H) x v),w⟫_ℝ = _
  rw [← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply]

theorem sphericalHessian_tangent_quadratic {N p : ℕ}
    (J : Disorder N p) (x v : Vector N) (hv : ⟪x,v⟫_ℝ=0) :
    ⟪v,sphericalHessian J x v⟫_ℝ = fderiv ℝ (fderiv ℝ (Hamiltonian N p J)) x v v -
      (⟪x,gradient (Hamiltonian N p J) x⟫_ℝ/(N : ℝ))*‖v‖^2 := by
  have hPv : tangentProjection x v = v := by
    rw [tangentProjection_apply]
    exact projection_tangent_fixed x v hv
  unfold sphericalHessian
  simp only [sub_apply, ContinuousLinearMap.comp_apply, smul_apply, hPv,
    inner_sub_right, real_inner_smul_right]
  rw [tangentProjection_apply, ← projection_self_adjoint, projection_tangent_fixed x v hv]
  have hc : ⟪v,fderiv ℝ (gradient (Hamiltonian N p J)) x v⟫_ℝ =
      ⟪fderiv ℝ (gradient (Hamiltonian N p J)) x v,v⟫_ℝ := real_inner_comm _ _
  rw [hc, fderiv_gradient_inner,
    real_inner_self_eq_norm_sq]

theorem canonical_rotation_second_sum_eq_sphericalHessian {N p : ℕ} (hN : 0<N)
    (J : Disorder N p) (f : Vector N → ℝ) (x : Vector N) (hx : OnSphere x) :
    (1/(2*(N : ℝ)))^2 * (∑ a : Fin N × Fin N, ∑ b : Fin N × Fin N,
      lieDerivative (rotations N a) f x * lieDerivative (rotations N b) f x *
        lieDerivative (rotations N a) (lieDerivative (rotations N b) (Hamiltonian N p J)) x) =
      ⟪projection x (gradient f x),sphericalHessian J x (projection x (gradient f x))⟫_ℝ := by
  rw [canonical_rotation_second_sum_eq_extrinsic_hessian hN
    ((Hamiltonian_contDiff J).of_le (by simp)) x hx,
    sphericalHessian_tangent_quadratic J x _
      (projection_tangent (Nat.ne_of_gt hN) x _ hx)]

theorem canonical_rotationGamma_drift_eq_sphericalHessian {N p : ℕ} (hN : 0<N)
    (J : Disorder N p) {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f)
    (x : Vector N) (hx : OnSphere x) :
    (1/2)*rotationGamma (1/(2*(N : ℝ))) (rotations N) (Hamiltonian N p J)
        (rotationGamma (1/(2*(N : ℝ))) (rotations N) f f) x -
      rotationGamma (1/(2*(N : ℝ))) (rotations N) f
        (rotationGamma (1/(2*(N : ℝ))) (rotations N) (Hamiltonian N p J) f) x =
      -⟪projection x (gradient f x),sphericalHessian J x (projection x (gradient f x))⟫_ℝ := by
  rw [rotationGamma_drift_eq_second_rotation_sum _ ((Hamiltonian_contDiff J).of_le (by simp)) hf]
  have hh := canonical_rotation_second_sum_eq_sphericalHessian hN J f x hx
  simp only [rotations, Fintype.sum_prod_type] at hh
  linarith only [hh]

/-- Actual canonical spherical Γ₂ decomposes into its proved nonnegative
rotation-diffusion part and the intrinsic Hamiltonian Hessian drift. -/
theorem canonical_rotationGamma2_eq_diffusion_sub_hessian {N p : ℕ} (hN : 0<N)
    (β : ℝ) (J : Disorder N p) {f : Vector N → ℝ} (hf : ContDiff ℝ 3 f)
    (x : Vector N) (hx : OnSphere x) :
    rotationGamma2 (1/(2*(N : ℝ))) β J (rotations N) f x =
      rotationGamma2 (1/(2*(N : ℝ))) 0 J (rotations N) f x -
        β*⟪projection x (gradient f x),sphericalHessian J x (projection x (gradient f x))⟫_ℝ := by
  rw [rotationGamma2_drift_split _ β J _ hf,
    canonical_rotationGamma_drift_eq_sphericalHessian hN J (hf.of_le (by norm_num)) x hx]
  ring

/-- The genuine canonical spherical Bakry–Émery lower bound. Its proof uses the
actual Casimir sum of squares and actual intrinsic Hamiltonian Hessian bound. -/
theorem canonical_rotationGamma2_curvature_lower_bound {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) {f : Vector N → ℝ} (hf : ContDiff ℝ 3 f)
    (x : Vector N) (hx : OnSphere x) :
    -β*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J *
        rotationGamma (1/(2*(N : ℝ))) (rotations N) f f x ≤
      rotationGamma2 (1/(2*(N : ℝ))) β J (rotations N) f x := by
  have hzero := rotationGamma2_zero_nonneg (1/(2*(N : ℝ))) J hf x
  have hH := SphereCurvatureHessianBound.sphericalHessian_drift_lower_bound hN hp hβ J x
    (projection x (gradient f x)) hx
  rw [canonical_rotationGamma2_eq_diffusion_sub_hessian hN β J hf x hx]
  change _*rotationGamma (1/(2*(N : ℝ)))
    (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2) f f x ≤ _
  rw [canonical_rotationGamma_eq_tangent_inner hN f f x hx, real_inner_self_eq_norm_sq]
  nlinarith only [hzero,hH]

end SphericalAging.SphereGamma2Drift
