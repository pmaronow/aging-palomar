module

public import SphericalAging.SphereEulerForkTensorHistory
public import SphericalAging.ForkAlgorithmDisclosureClipping
public import SphericalAging.WaitingOrthogonalityFromActualEuler

public section

/-! The Euler-history waiting-state specialization (retained internal identifier
`source10_9`) for the literal physical waiting process. The normalized
Euler directions are genuine predictable tensor disclosures, and the true
Euler error is sent to zero after source10.7. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereOnlyActualWaitingOrthogonality
open Set Filter MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open AdaptiveTensorDisclosureSource AdaptiveSourceProjectionMoments
open AdaptiveSourceProjectionRecursion ExternalFieldUniformCost
open ForkAlgorithmDisclosureClipping WaitingAlgorithmOrthogonality
open ForkOrderedParameters SphereEulerForkTensorHistory
open scoped NNReal Topology InnerProductSpace

theorem actual_source10_9 {dim : ℕ→ℕ} (hDim : ∀n,0<dim n)
    (hTop : Tendsto dim atTop atTop) {p : ℕ} (hp : 3≤p) (β s : ℝ≥0)
    (hPub : ∀Lip,PublishedFieldThreshold p Lip) : Input dim p β s := by
  apply WaitingOrthogonalityFromActualEuler.input_of_actual_euler_queries hDim hTop (by omega) β s
  intro A Lip hA hgood M hM hδ
  let Seeds (θ : Index) (n : ℕ) := ForkSeedCoordinates.Seed (dim n) (branches θ.1)
  let μ (θ : Index) (n : ℕ) : Measure (Seeds θ n) := ForkSeedCoordinates.law (dim n) (branches θ.1)
  let alg (θ : Index) (n : ℕ) := clippedTensorAlgorithm (A θ n)
  have hball θ n : ∀ᵐξ ∂μ θ n,∀J,‖A θ n (ξ,J)‖≤Real.sqrt (dim n) :=
    (hgood θ n).mono (fun _ h => h.2)
  have hδ' : Tendsto (fun θ => energyDeficit (μ θ) (alg θ))
      (orderedFilter.curry atTop) (𝓝 0) := by
    have he : (fun θ => energyDeficit (μ θ) (alg θ))=
        fun θ => AlgorithmEnergyDeficit.deficit (ExternalFieldElementaryPenalty.thresholdEnergy p)
          (fun n => ForkNormalizedEnergy.expectedEnergy
            (μ:=WaitingAlgorithmOrthogonality.measure dim p θ n) Prod.snd (A θ n)) := by
      funext θ
      exact energyDeficit_eq (μ θ) (A θ) (hball θ)
    rw [he]
    exact hδ
  have hlim := (AdaptiveTensorDisclosureWaitingPairing.actual_source_10_7_with_pairing hp Lip
    (fun θ => hPub (Lip θ)) hDim hTop μ
    (fun θ n => W0 (N:=dim n) (K:=branches θ.1) s M)
    (fun θ n => W0_projection_measurable s M)
    (fun θ n ξ => W0_finrank_le s M ξ)
    (fun θ n => u (N:=dim n) (p:=p) (K:=branches θ.1) β s M)
    (fun θ n j => u_history_measurable (by omega : 2≤p) β s M j)
    (fun θ n j z => u_orthogonal β s M j z)
    (fun θ n j z => u_zero_or_unit β s M j z)
    alg (fun θ n => measurable_uncurry (hA θ n))
    (fun θ n => lipschitz_seed ((hgood θ n).mono (fun _ h => h.1)))
    (fun θ n ξ J => global_ball (A θ n) ξ J) hδ' M
    (SphereEulerWaitingTransfer.family dim p β s M)
    (fun θ n => SphereEulerWaitingTransfer.family_measurable dim p β s M θ n)
    (fun θ n z => SphereEulerWaitingTransfer.family_norm_le dim p β s M θ n z)
    (fun θ n z => eulerWaiting_mem β s M z)).2
  apply hlim.congr
  intro θ
  congr 1
  funext n
  exact pairing_integral_eq (μ θ n) (hball θ n)
    (SphereEulerWaitingTransfer.family dim p β s M θ n)

end SphericalAging.SphereOnlyActualWaitingOrthogonality
