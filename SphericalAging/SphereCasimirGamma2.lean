module

public import SphericalAging.SphereCasimir

public section

/-! The canonical diffusion-only iterated carré du champ is the sum of squares
of the genuine second rotation derivatives. Its nonnegativity is therefore
proved from the actual coordinate Casimir, without a Bochner premise. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereCasimirGamma2

open FiniteModel SphericalIntegrationByParts SphereGeneratorIntegrationByParts SphereGeneratorAlgebra
open SphereFisherDissipation SphereGamma2Algebra SphereRotationGeometry SphereCasimir
open scoped BigOperators

@[expose] abbrev rotations (N : ℕ) (ij : Fin N × Fin N) := coordinateRotation ij.1 ij.2

theorem rotationGenerator_zero_eq_casimir {N p : ℕ} (κ : ℝ) (J : Disorder N p)
    (f : Vector N → ℝ) :
    rotationGenerator κ 0 J (rotations N) f = (fun x => κ*rotationCasimir f x) := by
  funext x
  simp [rotationGenerator, rotationCasimir, rotations, Fintype.sum_prod_type]

theorem rotationGamma_self_eq_square_sum {N : ℕ} (κ : ℝ) (f : Vector N → ℝ) :
    rotationGamma κ (rotations N) f f =
      (fun x => κ*(∑ i : Fin N, ∑ j : Fin N, (lieDerivative (coordinateRotation i j) f x)^2)) := by
  funext x
  simp [rotationGamma, rotations, Fintype.sum_prod_type, pow_two]

theorem rotationCasimir_contDiff_one {N : ℕ} {f : Vector N → ℝ} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 1 (rotationCasimir f) := by
  classical
  unfold rotationCasimir
  exact ContDiff.sum (s := Finset.univ) (fun i _ =>
    ContDiff.sum (s := Finset.univ) (fun j _ =>
      lieDerivative_contDiff_order _ (lieDerivative_contDiff_order _ hf)))

theorem rotationCasimir_const_mul {N : ℕ} (c : ℝ) {f : Vector N → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Vector N) :
    rotationCasimir (fun y => c*f y) x = c*rotationCasimir f x := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have he i j : lieDerivative (coordinateRotation i j) (fun y => c*f y) =
      (fun y => c*lieDerivative (coordinateRotation i j) f y) :=
    funext (lieDerivative_const_mul _ c hf₁)
  unfold rotationCasimir
  simp_rw [he, lieDerivative_const_mul _ c (lieDerivative_contDiff_order _ hf)]
  simp only [Finset.mul_sum]

theorem rotationCasimir_sum {N : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Vector N → ℝ) (hf : ∀ a, ContDiff ℝ 2 (f a)) (x : Vector N) :
    rotationCasimir (fun y => ∑ a, f a y) x = ∑ a, rotationCasimir (f a) x := by
  classical
  have he i j : lieDerivative (coordinateRotation i j) (fun y => ∑ a, f a y) =
      (fun y => ∑ a, lieDerivative (coordinateRotation i j) (f a) y) :=
    funext (lieDerivative_sum _ f (fun a => (hf a).of_le (by norm_num)))
  unfold rotationCasimir
  simp_rw [he, lieDerivative_sum _ _ (fun a => lieDerivative_contDiff_order _ (hf a))]
  calc
    _ = ∑ i : Fin N, ∑ a : ι, ∑ j : Fin N,
        lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation i j) (f a)) x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem rotationCasimir_square {N : ℕ} {f : Vector N → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Vector N) :
    rotationCasimir (fun y => (f y)^2) x = 2*f x*rotationCasimir f x +
      2*(∑ i : Fin N, ∑ j : Fin N, (lieDerivative (coordinateRotation i j) f x)^2) := by
  have he : (fun y => (f y)^2) = (fun y => f y*f y) := by
    funext y
    ring
  rw [he]
  unfold rotationCasimir
  simp_rw [lieDerivative_twice_mul _ hf hf]
  have ht i j : f x*lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation i j) f) x +
      f x*lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation i j) f) x +
      2*(lieDerivative (coordinateRotation i j) f x*lieDerivative (coordinateRotation i j) f x) =
      (2*f x)*lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation i j) f) x +
      2*(lieDerivative (coordinateRotation i j) f x)^2 := by ring
  simp_rw [ht, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem rotationGamma2_zero_eq_sum_squares {N p : ℕ} (κ : ℝ) (J : Disorder N p)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 3 f) (x : Vector N) :
    rotationGamma2 κ 0 J (rotations N) f x =
      κ^2 * (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        (lieDerivative (coordinateRotation k l) (lieDerivative (coordinateRotation i j) f) x)^2) := by
  classical
  have hD (i j : Fin N) : ContDiff ℝ 2 (lieDerivative (coordinateRotation i j) f) :=
    lieDerivative_contDiff_order _ hf
  have hSq (i j : Fin N) : ContDiff ℝ 2
      (fun y => (lieDerivative (coordinateRotation i j) f y)^2) := (hD i j).pow 2
  have hRow (i : Fin N) : ContDiff ℝ 2
      (fun y => ∑ j : Fin N, (lieDerivative (coordinateRotation i j) f y)^2) :=
    ContDiff.sum (s := Finset.univ) (fun j _ => hSq i j)
  have hS : ContDiff ℝ 2
      (fun y => ∑ i : Fin N, ∑ j : Fin N, (lieDerivative (coordinateRotation i j) f y)^2) :=
    ContDiff.sum (s := Finset.univ) (fun i _ => hRow i)
  have hLG : rotationGenerator κ 0 J (rotations N) (rotationGamma κ (rotations N) f f) x =
      κ^2 * (∑ i : Fin N, ∑ j : Fin N,
        (2*lieDerivative (coordinateRotation i j) f x*
          rotationCasimir (lieDerivative (coordinateRotation i j) f) x +
          2*(∑ k : Fin N, ∑ l : Fin N,
            (lieDerivative (coordinateRotation k l) (lieDerivative (coordinateRotation i j) f) x)^2))) := by
    rw [rotationGamma_self_eq_square_sum, rotationGenerator_zero_eq_casimir]
    change κ*rotationCasimir (fun y => κ*(∑ i : Fin N, ∑ j : Fin N,
      (lieDerivative (coordinateRotation i j) f y)^2)) x = _
    rw [rotationCasimir_const_mul κ hS, rotationCasimir_sum _ hRow]
    simp_rw [rotationCasimir_sum _ (hSq _), rotationCasimir_square (hD _ _)]
    ring
  have hGL : rotationGamma κ (rotations N) f (rotationGenerator κ 0 J (rotations N) f) x =
      κ^2 * (∑ i : Fin N, ∑ j : Fin N, lieDerivative (coordinateRotation i j) f x *
        rotationCasimir (lieDerivative (coordinateRotation i j) f) x) := by
    rw [rotationGenerator_zero_eq_casimir]
    unfold rotationGamma
    simp only [rotations, Fintype.sum_prod_type]
    simp_rw [lieDerivative_const_mul _ κ (rotationCasimir_contDiff_one hf),
      ← rotationCasimir_commutes _ _ hf, mul_left_comm _ κ, ← Finset.mul_sum]
    ring
  unfold rotationGamma2
  rw [hLG, hGL]
  have ht (i j : Fin N) : 2*lieDerivative (coordinateRotation i j) f x *
      rotationCasimir (lieDerivative (coordinateRotation i j) f) x =
      2*(lieDerivative (coordinateRotation i j) f x *
        rotationCasimir (lieDerivative (coordinateRotation i j) f) x) := by ring
  simp_rw [ht, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem rotationGamma2_zero_nonneg {N p : ℕ} (κ : ℝ) (J : Disorder N p)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 3 f) (x : Vector N) :
    0 ≤ rotationGamma2 κ 0 J (rotations N) f x := by
  rw [rotationGamma2_zero_eq_sum_squares κ J hf x]
  exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun l _ => sq_nonneg _)

end SphericalAging.SphereCasimirGamma2
