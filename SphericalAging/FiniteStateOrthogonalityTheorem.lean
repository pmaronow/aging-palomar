module

public import SphericalAging.FiniteStateOrthogonalityLimit
public import SphericalAging.ActualWeightedWiener

public section

/-! Complete local waiting-state transfer, with the exact preceding
finite-span orthogonality and Euler mean-square approximation inputs.
It applies on arbitrary probability spaces and in particular to the
literal Gaussian/sphere/Brownian model. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SphericalAging.FiniteStateOrthogonalityTheorem
open MeasureTheory Filter Set FiniteModel FiniteStateOrthogonalityBounds
  FiniteStateOrthogonalityLimit
open scoped Topology InnerProductSpace NNReal
universe u v

theorem source10_9 {Θ : Type v} {l : Filter Θ} (dim : ℕ→ℕ) (hDim : ∀n,0<dim n)
    {Ω : ℕ→Type u} [∀n,MeasurableSpace (Ω n)]
    (μ : ∀n,Measure (Ω n)) [∀n,IsProbabilityMeasure (μ n)]
    (A : Θ→∀n : ℕ,Ω n→Vector (dim n)) (X : ∀n,Ω n→Vector (dim n))
    (Y : ∀M n : ℕ,Ω n→Vector (dim n))
    (hA : ∀θ n,AEStronglyMeasurable (A θ n) (μ n))
    (hX : ∀n,AEStronglyMeasurable (X n) (μ n))
    (hY : ∀M n,AEStronglyMeasurable (Y M n) (μ n))
    (hAb : ∀θ n,∀ᵐω ∂μ n,‖A θ n ω‖≤Real.sqrt (dim n))
    (hXb : ∀n,∀ᵐω ∂μ n,‖X n ω‖≤Real.sqrt (dim n))
    (hYb : ∀M n,∀ᵐω ∂μ n,‖Y M n ω‖≤Real.sqrt (dim n))
    (hspan : ∀M,0<M→Tendsto (fun θ => limsup
      (fun n => ∫ω,|inner ℝ (A θ n ω) (Y M n ω)/(dim n:ℝ)|^2 ∂μ n) atTop)
      l (𝓝 0))
    {C : ℝ} (hC : 0≤C)
    (hEuler : ∀M,0<M→limsup
      (fun n => ∫ω,‖X n ω-Y M n ω‖^2/(dim n:ℝ) ∂μ n) atTop≤C/(M:ℝ)) :
    Tendsto (fun θ => limsup
      (fun n => ∫ω,|inner ℝ (A θ n ω) (X n ω)/(dim n:ℝ)|^2 ∂μ n) atTop)
      l (𝓝 0) := by
  apply ordered_approximation_limit
    (fun θ n => (overlap_square_integrable_bound (hDim n) (hA θ n) (hX n) (hAb θ n) (hXb n)).2)
    (fun M θ n => (overlap_square_integrable_bound (hDim n) (hA θ n) (hY M n) (hAb θ n) (hYb M n)).2)
    (fun M n => (distance_square_integrable_bound (hDim n) (hX n) (hY M n) (hXb n) (hYb M n)).2)
    (fun M θ n => overlap_mean_square_comparison (hDim n) (hA θ n) (hX n) (hY M n)
      (hAb θ n) (hXb n) (hYb M n)) hspan hC hEuler

open AnnealedHamiltonianEnergyStein

theorem actual_model_waiting_state_ball {N p : ℕ} (hN : 0<N) (β : ℝ) (s : ℝ≥0) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,‖modelProcess N p β s ω‖≤Real.sqrt N := by
  filter_upwards [(ActualModelRestart.modelProcess_physical (p:=p) hN β).2] with ω hω
  have hn : 0≤(N:ℝ) := Nat.cast_nonneg N
  have hs : ‖modelProcess N p β s ω‖^2=(N:ℝ) := by
    rw [←real_inner_self_eq_norm_sq]
    exact hω s
  nlinarith [Real.sq_sqrt hn,Real.sqrt_nonneg (N:ℝ),norm_nonneg (modelProcess N p β s ω)]

end SphericalAging.FiniteStateOrthogonalityTheorem
