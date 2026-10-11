module

public import SphericalAging.UniformApproximationOrthogonality
public import SphericalAging.FiniteStateOrthogonalityTheorem

public section

/-! The waiting-state proof allows the random seed space to vary with every outer parameter. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SphericalAging.VariableSeedOrthogonality
open MeasureTheory Filter Set FiniteModel FiniteStateOrthogonalityBounds
open scoped Topology InnerProductSpace NNReal
universe u v

theorem waiting_state_limit {Θ : Type v} {l : Filter Θ} (dim : ℕ→ℕ) (hDim : ∀n,0<dim n)
    {Ω : Θ→ℕ→Type u} [∀θ n,MeasurableSpace (Ω θ n)]
    (μ : ∀θ n,Measure (Ω θ n)) [∀θ n,IsProbabilityMeasure (μ θ n)]
    (A X : ∀θ n,Ω θ n→Vector (dim n))
    (Y : ℕ→∀θ n,Ω θ n→Vector (dim n))
    (hA : ∀θ n,AEStronglyMeasurable (A θ n) (μ θ n))
    (hX : ∀θ n,AEStronglyMeasurable (X θ n) (μ θ n))
    (hY : ∀M θ n,AEStronglyMeasurable (Y M θ n) (μ θ n))
    (hAb : ∀θ n,∀ᵐω ∂μ θ n,‖A θ n ω‖≤Real.sqrt (dim n))
    (hXb : ∀θ n,∀ᵐω ∂μ θ n,‖X θ n ω‖≤Real.sqrt (dim n))
    (hYb : ∀M θ n,∀ᵐω ∂μ θ n,‖Y M θ n ω‖≤Real.sqrt (dim n))
    (hspan : ∀M,0<M→Tendsto (fun θ => limsup
      (fun n => ∫ω,|inner ℝ (A θ n ω) (Y M θ n ω)/(dim n:ℝ)|^2 ∂μ θ n) atTop)
      l (𝓝 0))
    {C : ℝ} (hC : 0≤C)
    (hEuler : ∀M,0<M→∀θ,limsup
      (fun n => ∫ω,‖X θ n ω-Y M θ n ω‖^2/(dim n:ℝ) ∂μ θ n) atTop≤C/(M:ℝ)) :
    Tendsto (fun θ => limsup
      (fun n => ∫ω,|inner ℝ (A θ n ω) (X θ n ω)/(dim n:ℝ)|^2 ∂μ θ n) atTop)
      l (𝓝 0) := by
  apply UniformApproximationOrthogonality.ordered_uniform_approximation_limit
    (fun θ n => (overlap_square_integrable_bound (hDim n) (hA θ n) (hX θ n) (hAb θ n) (hXb θ n)).2)
    (fun M θ n => (overlap_square_integrable_bound (hDim n) (hA θ n) (hY M θ n) (hAb θ n) (hYb M θ n)).2)
    (fun M θ n => (distance_square_integrable_bound (hDim n) (hX θ n) (hY M θ n) (hXb θ n) (hYb M θ n)).2)
    (fun M θ n => overlap_mean_square_comparison (hDim n) (hA θ n) (hX θ n) (hY M θ n)
      (hAb θ n) (hXb θ n) (hYb M θ n)) hspan hC hEuler

end SphericalAging.VariableSeedOrthogonality
