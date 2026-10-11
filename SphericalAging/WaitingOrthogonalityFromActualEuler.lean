module

public import SphericalAging.SphereEulerWaitingTransfer
public import SphericalAging.WaitingOrthogonalityFromQueries

public section

/-! Preceding finite-query algorithm orthogonality transfers to the actual
physical waiting state. Every Euler output and approximation error is
constructed here; only the separately proved finite-query conclusion is
an upstream input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology InnerProductSpace
namespace SphericalAging.WaitingOrthogonalityFromActualEuler
open FiniteModel ForkSeedCoordinates PhysicalForkWaitingTransfer ForkEnergyComparison ForkNormalizedEnergy
open ForkOrderedParameters AlgorithmEnergyDeficit ExternalFieldElementaryPenalty
open WaitingAlgorithmOrthogonality SphereEulerWaitingTransfer SphereEulerDimensionRate
open AdditiveSphereGaussianApproximation
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem input_of_actual_euler_queries {dim : ℕ→ℕ} (hDim : ∀n,0<dim n)
    (hDimTop : Tendsto dim atTop atTop) {p : ℕ} (hp : 2≤p) (β s : ℝ≥0)
    (hSpan : ∀ (A : ∀θ n,Space dim p θ n→Vector (dim n)) (Lip : Index→ℝ≥0),
      (∀θ n,Measurable (A θ n))→
      (∀θ n,∀ᵐξ ∂ForkSeedCoordinates.law (dim n) (branches θ.1),
        LipschitzWith (Lip θ) (fun J : EuclideanSpace ℝ (TensorIndex (dim n) p) => A θ n (ξ,J.ofLp)) ∧
          ∀J,‖A θ n (ξ,J)‖≤Real.sqrt (dim n))→
      ∀m : ℕ,0<m→Tendsto (fun θ => deficit (thresholdEnergy p)
        (fun n => expectedEnergy (μ:=WaitingAlgorithmOrthogonality.measure dim p θ n) Prod.snd (A θ n)))
          (orderedFilter.curry atTop) (𝓝 0)→
      Tendsto (fun θ => limsup (fun n => ∫z,
        |inner ℝ (A θ n z) (family dim p β s m θ n z)/(dim n:ℝ)|^2
          ∂WaitingAlgorithmOrthogonality.measure dim p θ n) atTop) (orderedFilter.curry atTop) (𝓝 0)) :
    Input dim p β s := by
  apply WaitingOrthogonalityFromQueries.input_of_finite_queries_and_Euler
    (dim:=dim) (p:=p) (β:=(β:ℝ)) (s:=s) hDim
    (fun m => family dim p β s m)
    (fun m θ n => (family_measurable dim p β s m θ n).aestronglyMeasurable)
    (fun m θ n => .of_forall (family_norm_le dim p β s m θ n))
    (C:=(globalRate p β (landscapeCutoff p) s:ℝ)*(s:ℝ)) (by positivity)
  · intro m hm θ
    exact family_dimension_limsup_le dim hDimTop p hp β s (Nat.ne_of_gt hm) θ
  · exact hSpan

end SphericalAging.WaitingOrthogonalityFromActualEuler
