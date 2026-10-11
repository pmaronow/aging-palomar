module

public import SphericalAging.WaitingAlgorithmOrthogonality
public import SphericalAging.VariableSeedOrthogonality

public section

/-! The preceding finite query-span orthogonality of source10.7 and uniform
Euler error imply the admissible-algorithm waiting-state estimate used in
the finite-fork fixed-wait forgetting argument. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.WaitingOrthogonalityFromQueries
open MeasureTheory ProbabilityTheory Filter FiniteModel ForkSeedCoordinates
  FiniteForkMoments PhysicalForkWaitingTransfer ForkEnergyComparison ForkNormalizedEnergy
  ForkOrderedParameters AlgorithmEnergyDeficit ExternalFieldElementaryPenalty
  WaitingAlgorithmOrthogonality
open scoped NNReal Topology InnerProductSpace

theorem input_of_finite_queries_and_Euler {dim : ℕ→ℕ} {p : ℕ} {β : ℝ} {s : ℝ≥0}
    (hDim : ∀n,0<dim n)
    (Y : ℕ→∀θ n,Space dim p θ n→Vector (dim n))
    (hY : ∀m θ n,AEStronglyMeasurable (Y m θ n) (WaitingAlgorithmOrthogonality.measure dim p θ n))
    (hYb : ∀m θ n,∀ᵐω ∂WaitingAlgorithmOrthogonality.measure dim p θ n,
      ‖Y m θ n ω‖≤Real.sqrt (dim n))
    {C : ℝ} (hC : 0≤C)
    (hEuler : ∀m : ℕ,0<m→∀θ,limsup (fun n => ∫ω,
      ‖seededWaiting (K:=branches θ.1) β s ω-Y m θ n ω‖^2/(dim n:ℝ)
        ∂WaitingAlgorithmOrthogonality.measure dim p θ n) atTop≤C/(m:ℝ))
    (hSpan : ∀ (A : ∀θ n,Space dim p θ n→Vector (dim n)) (Lip : Index→ℝ≥0),
      (∀θ n,Measurable (A θ n))→
      (∀θ n,∀ᵐξ ∂ForkSeedCoordinates.law (dim n) (branches θ.1),
        LipschitzWith (Lip θ) (fun J : EuclideanSpace ℝ (TensorIndex (dim n) p) => A θ n (ξ,J.ofLp)) ∧
          ∀J,‖A θ n (ξ,J)‖≤Real.sqrt (dim n))→
      ∀m : ℕ,0<m→Tendsto (fun θ => deficit (thresholdEnergy p)
        (fun n => expectedEnergy (μ:=WaitingAlgorithmOrthogonality.measure dim p θ n) Prod.snd (A θ n)))
          (orderedFilter.curry atTop) (𝓝 0)→
      Tendsto (fun θ => limsup (fun n => ∫ω,
        |inner ℝ (A θ n ω) (Y m θ n ω)/(dim n:ℝ)|^2
          ∂WaitingAlgorithmOrthogonality.measure dim p θ n) atTop) (orderedFilter.curry atTop) (𝓝 0)) :
    Input dim p β s := by
  intro A Lip hA hgood hδ
  have hAb θ n : ∀ᵐω ∂WaitingAlgorithmOrthogonality.measure dim p θ n,
      ‖A θ n ω‖≤Real.sqrt (dim n) := by
    filter_upwards [(measurePreserving_fst (μ:=ForkSeedCoordinates.law (dim n) (branches θ.1))
      (ν:=disorderLaw (dim n) p)).quasiMeasurePreserving.ae (hgood θ n)] with z hz
    exact hz.2 z.2
  exact VariableSeedOrthogonality.waiting_state_limit dim hDim
    (WaitingAlgorithmOrthogonality.measure dim p) A
    (fun θ n => seededWaiting (K:=branches θ.1) β s) Y
    (fun θ n => (hA θ n).aestronglyMeasurable)
    (fun θ n => (seededWaiting_memLp (dim n) p (branches θ.1) β s).aestronglyMeasurable)
    hY hAb (fun θ n => seededWaiting_bound (hDim n) β s) hYb
    (fun m hm => hSpan A Lip hA hgood m hm hδ) hC hEuler

end SphericalAging.WaitingOrthogonalityFromQueries
