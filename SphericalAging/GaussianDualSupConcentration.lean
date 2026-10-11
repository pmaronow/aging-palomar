module

public import SphericalAging.GaussianLipschitzConcentration

public section

/-! Concentration of the actual supremum of any bounded family of
Gaussian linear functionals. Its Lipschitz constant is proved from the
dual norms, including infinite nonempty index families. -/
noncomputable section
set_option maxHeartbeats 600000
namespace SphericalAging.GaussianDualSupConcentration
open Set MeasureTheory ProbabilityTheory GaussianSmoothConcentration
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {I : Type*} [Nonempty I]

@[expose] def supremum (A : I→(E→L[ℝ] ℝ)) (x : E) : ℝ := sSup (Set.range (fun i => A i x))

theorem range_bddAbove (A : I→(E→L[ℝ] ℝ)) {L : ℝ≥0}
    (hA : ∀i,‖A i‖≤L) (x : E) : BddAbove (Set.range (fun i => A i x)) := by
  refine ⟨(L:ℝ)*‖x‖,?_⟩
  rintro z ⟨i,rfl⟩
  exact (le_abs_self _).trans (by
    have hh := (A i).le_opNorm x
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _)))

theorem supremum_lipschitz (A : I→(E→L[ℝ] ℝ)) {L : ℝ≥0}
    (hA : ∀i,‖A i‖≤L) : LipschitzWith L (supremum A) := by
  have hdiff (x y : E) : supremum A x≤supremum A y+(L:ℝ)*dist x y := by
    apply csSup_le (Set.range_nonempty _)
    rintro z ⟨i,rfl⟩
    have hi : A i y≤supremum A y := le_csSup (range_bddAbove A hA y) (Set.mem_range_self i)
    have hb : A i x-A i y≤(L:ℝ)*dist x y := by
      rw [←map_sub]
      have hh := (A i).le_opNorm (x-y)
      rw [Real.norm_eq_abs] at hh
      rw [dist_eq_norm]
      exact (le_abs_self _).trans (hh.trans (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _)))
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor
  · have hh := hdiff y x
    rw [dist_comm] at hh
    linarith
  · linarith [hdiff x y]

theorem supremum_centered_hasSubgaussianMGF (A : I→(E→L[ℝ] ℝ)) {L : ℝ≥0}
    (hA : ∀i,‖A i‖≤L) :
    HasSubgaussianMGF (fun x => supremum A x-∫y,supremum A y ∂stdGaussian E)
      (rotationConstant L) (stdGaussian E) :=
  GaussianLipschitzConcentration.centered_hasSubgaussianMGF _ (supremum_lipschitz A hA)

theorem supremum_centered_absolute_tail (A : I→(E→L[ℝ] ℝ)) {L : ℝ≥0}
    (hA : ∀i,‖A i‖≤L) (ε : ℝ) (hε : 0≤ε) :
    (stdGaussian E).real {x | ε≤|supremum A x-∫y,supremum A y ∂stdGaussian E|}≤
      2*Real.exp (-ε^2/(2*(rotationConstant L:ℝ))) :=
  GaussianLipschitzConcentration.centered_absolute_tail _ (supremum_lipschitz A hA) ε hε

end SphericalAging.GaussianDualSupConcentration
