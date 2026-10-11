module

public import SphericalAging.SphereGamma2Algebra

public section

/-! The actual complete coordinate-rotation Casimir commutes with each rotation.
The argument uses the proved linear vector field commutators and exact so(N)
structure constants. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereCasimir

open FiniteModel SphericalIntegrationByParts SphereFisherDissipation SphereGeneratorAlgebra
open SphereRotationGeometry SphereGamma2Algebra
open scoped BigOperators

@[expose] def rotationCasimir {N : ℕ} (f : Vector N → ℝ) (x : Vector N) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, lieDerivative (coordinateRotation i j)
    (lieDerivative (coordinateRotation i j) f) x

theorem lieDerivative_sum {N : ℕ} {ι : Type*} [Fintype ι] (A : Operator N)
    (f : ι → Vector N → ℝ) (hf : ∀ i, ContDiff ℝ 1 (f i)) (x : Vector N) :
    lieDerivative A (fun y => ∑ i, f i y) x = ∑ i, lieDerivative A (f i) x := by
  classical
  unfold lieDerivative
  rw [fderiv_fun_sum (fun i _ => (hf i).differentiable (by norm_num) x)]
  simp only [sum_apply]

theorem lieDerivative_sub {N : ℕ} (A : Operator N) {f g : Vector N → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : Vector N) :
    lieDerivative A (fun y => f y-g y) x = lieDerivative A f x-lieDerivative A g x := by
  unfold lieDerivative
  rw [fderiv_fun_sub (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x)]
  rfl

theorem lieDerivative_square_commutator {N : ℕ} (A B : Operator N)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 3 f) (x : Vector N) :
    lieDerivative A (lieDerivative A (lieDerivative B f)) x -
        lieDerivative B (lieDerivative A (lieDerivative A f)) x =
      lieDerivative A (lieDerivative (B.comp A-A.comp B) f) x +
        lieDerivative (B.comp A-A.comp B) (lieDerivative A f) x := by
  have hf₂ : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hAf : ContDiff ℝ 2 (lieDerivative A f) := lieDerivative_contDiff_order A hf
  have hBf : ContDiff ℝ 2 (lieDerivative B f) := lieDerivative_contDiff_order B hf
  have he : (fun y => lieDerivative A (lieDerivative B f) y -
      lieDerivative B (lieDerivative A f) y) = lieDerivative (B.comp A-A.comp B) f :=
    funext (lieDerivative_commutator A B hf₂)
  have hh := congrArg (fun g => lieDerivative A g x) he
  rw [lieDerivative_sub A (lieDerivative_contDiff_order A hBf)
    (lieDerivative_contDiff_order B hAf)] at hh
  have hh₂ := lieDerivative_commutator A B hAf x
  linarith

theorem coordinateRotation_swap {N : ℕ} (i j : Fin N) :
    coordinateRotation j i = -coordinateRotation i j := by
  simp [coordinateRotation, neg_sub]

theorem coordinate_lieDerivative_swap {N : ℕ} (i j : Fin N)
    (f : Vector N → ℝ) (x : Vector N) :
    lieDerivative (coordinateRotation j i) f x = -lieDerivative (coordinateRotation i j) f x := by
  rw [coordinateRotation_swap]
  simp [lieDerivative]

theorem coordinate_lieDerivative_square_commutator {N : ℕ} (i j k l : Fin N)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 3 f) (x : Vector N) :
    lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation i j)
        (lieDerivative (coordinateRotation k l) f)) x -
      lieDerivative (coordinateRotation k l) (lieDerivative (coordinateRotation i j)
        (lieDerivative (coordinateRotation i j) f)) x =
      (if i=k then (1 : ℝ) else 0) *
        (lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation j l) f) x +
          lieDerivative (coordinateRotation j l) (lieDerivative (coordinateRotation i j) f) x) +
      (if j=l then (1 : ℝ) else 0) *
        (lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation i k) f) x +
          lieDerivative (coordinateRotation i k) (lieDerivative (coordinateRotation i j) f) x) -
      (if j=k then (1 : ℝ) else 0) *
        (lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation i l) f) x +
          lieDerivative (coordinateRotation i l) (lieDerivative (coordinateRotation i j) f) x) -
      (if i=l then (1 : ℝ) else 0) *
        (lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation j k) f) x +
          lieDerivative (coordinateRotation j k) (lieDerivative (coordinateRotation i j) f) x) := by
  rw [lieDerivative_square_commutator _ _ hf, coordinateRotation_commutator]
  have hf₂ : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  simp only [lieDerivative_twice_fderiv _ _ hf₂, sub_apply, add_apply, smul_apply,
    map_sub, map_add, map_smul, smul_eq_mul]
  ring

theorem coordinate_square_commutator_sum_zero {N : ℕ} (k l : Fin N)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 3 f) (x : Vector N) :
    (∑ i : Fin N, ∑ j : Fin N,
      (lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation i j)
          (lieDerivative (coordinateRotation k l) f)) x -
        lieDerivative (coordinateRotation k l) (lieDerivative (coordinateRotation i j)
          (lieDerivative (coordinateRotation i j) f)) x)) = 0 := by
  classical
  simp_rw [coordinate_lieDerivative_square_commutator _ _ _ _ hf x]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero]
  have hn (i j a b : Fin N) :
      lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation b a) f) x =
        -lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation a b) f) x := by
    have he : lieDerivative (coordinateRotation b a) f =
        (fun y => -lieDerivative (coordinateRotation a b) f y) :=
      funext (coordinate_lieDerivative_swap a b f)
    rw [he]
    change (fderiv ℝ (fun y => -lieDerivative (coordinateRotation a b) f y) x)
      ((coordinateRotation i j) x) = _
    rw [fderiv_fun_neg]
    rfl
  simp_rw [coordinate_lieDerivative_swap l, hn _ _ k]
  simp only [neg_neg, Finset.sum_add_distrib]
  have he (j : Fin N) :
      lieDerivative (coordinateRotation j k) (lieDerivative (coordinateRotation l j) f) x =
        lieDerivative (coordinateRotation k j) (lieDerivative (coordinateRotation j l) f) x := by
    rw [coordinate_lieDerivative_swap k, hn k j j l, neg_neg]
  simp_rw [he]
  ring

theorem rotationCasimir_commutes {N : ℕ} (k l : Fin N)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 3 f) (x : Vector N) :
    rotationCasimir (lieDerivative (coordinateRotation k l) f) x =
      lieDerivative (coordinateRotation k l) (rotationCasimir f) x := by
  have hterm (i j : Fin N) : ContDiff ℝ 1
      (lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation i j) f)) :=
    lieDerivative_contDiff_order _ (lieDerivative_contDiff_order _ hf)
  have hsum (i : Fin N) : ContDiff ℝ 1 (fun y => ∑ j : Fin N,
      lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation i j) f) y) := by
    classical
    exact ContDiff.sum (s := Finset.univ) (fun j _ => hterm i j)
  have hh := coordinate_square_commutator_sum_zero k l hf x
  simp only [Finset.sum_sub_distrib] at hh
  unfold rotationCasimir
  rw [lieDerivative_sum _ _ hsum]
  simp_rw [lieDerivative_sum _ _ (hterm _)]
  linarith only [hh]

end SphericalAging.SphereCasimir
