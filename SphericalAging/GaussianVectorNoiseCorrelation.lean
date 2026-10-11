module

public import SphericalAging.GaussianNoiseCorrelation
public import SphericalAging.FiniteModel

public section

/-! Positive and monotone Gaussian noise stability for actual Euclidean
vector-valued algorithms, obtained by finite coordinate decomposition. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianVectorNoiseCorrelation
open Set MeasureTheory ProbabilityTheory FiniteModel GaussianNoiseSymmetry GaussianNoiseOperator
  GaussianNoiseCorrelation GaussianLinearMixtureLaw
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N : ℕ}

@[expose] def coordinate (A : E→Vector N) (i : Fin N) (x : E) : ℝ := A x i
@[expose] def stability (ρ : ℝ) (A : E→Vector N) : ℝ :=
  ∫z : E×E,⟪A z.1,A (noise ρ z.1 z.2)⟫_ℝ ∂(stdGaussian E).prod (stdGaussian E)

theorem coordinate_measurable (A : E→Vector N) (hA : Measurable A) (i : Fin N) :
    Measurable (coordinate A i) :=
  (PiLp.proj 2 (fun _ : Fin N => ℝ) i : Vector N→L[ℝ]ℝ).measurable.comp hA

theorem coordinate_bound (A : E→Vector N) (B : ℝ) (hB : ∀x,‖A x‖≤B) (i : Fin N) (x : E) :
    |coordinate A i x|≤B := by
  have hh := PiLp.norm_apply_le (A x) i
  rw [Real.norm_eq_abs] at hh
  exact hh.trans (hB x)

theorem stability_eq_sum (ρ : ℝ) (A : E→Vector N) (hA : Measurable A)
    (B : ℝ) (hB : ∀x,‖A x‖≤B) :
    stability ρ A=∑i,GaussianNoiseCorrelation.stability ρ (coordinate A i) := by
  have hB0 : 0≤B := (norm_nonneg (A 0)).trans (hB 0)
  have hn : Measurable (fun z : E×E => noise ρ z.1 z.2) :=
    (mixture (E:=E) ρ (Real.sqrt (1-ρ^2))).measurable
  have hi (i : Fin N) : Integrable (fun z : E×E =>
      coordinate A i z.1*coordinate A i (noise ρ z.1 z.2))
        ((stdGaussian E).prod (stdGaussian E)) := by
    have hm : Measurable (fun z : E×E => coordinate A i z.1*coordinate A i (noise ρ z.1 z.2)) :=
      ((coordinate_measurable A hA i).comp measurable_fst).mul
      ((coordinate_measurable A hA i).comp hn)
    apply signed_bounded_integrable _ _ hm (B*B)
    intro z
    rw [abs_mul]
    exact mul_le_mul (coordinate_bound A B hB i _) (coordinate_bound A B hB i _)
      (abs_nonneg _) hB0
  unfold stability
  simp only [PiLp.inner_apply,Real.inner_apply]
  change (∫z : E×E,∑i,coordinate A i z.1*coordinate A i (noise ρ z.1 z.2)
    ∂(stdGaussian E).prod (stdGaussian E))=_
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  change (∫z : E×E,coordinate A i z.1*coordinate A i (noise ρ z.1 z.2)
    ∂(stdGaussian E).prod (stdGaussian E))=_
  rw [integral_prod _ (hi i)]
  simp_rw [integral_const_mul]
  rfl

theorem stability_nonneg (ρ : ℝ) (h0 : 0≤ρ) (h1 : ρ≤1)
    (A : E→Vector N) (hA : Measurable A) (B : ℝ) (hB : ∀x,‖A x‖≤B) :
    0≤stability ρ A := by
  rw [stability_eq_sum ρ A hA B hB]
  exact Finset.sum_nonneg (fun i _ => GaussianNoiseCorrelation.stability_nonneg ρ h0 h1
    (coordinate A i) (coordinate_measurable A hA i) B (coordinate_bound A B hB i))

theorem stability_monotone (A : E→Vector N) (hA : Measurable A)
    (B : ℝ) (hB : ∀x,‖A x‖≤B) : MonotoneOn (fun ρ => stability ρ A) (Set.Icc 0 1) := by
  intro ρ hρ σ hσ hρσ
  change stability ρ A≤stability σ A
  rw [stability_eq_sum ρ A hA B hB,stability_eq_sum σ A hA B hB]
  exact Finset.sum_le_sum (fun i _ => GaussianNoiseCorrelation.stability_monotone
    (coordinate A i) (coordinate_measurable A hA i) B (coordinate_bound A B hB i) hρ hσ hρσ)

end SphericalAging.GaussianVectorNoiseCorrelation
