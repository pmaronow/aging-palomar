module

public import SphericalAging.AdaptiveTensorDisclosureWaitingPairing
public import SphericalAging.PurePActualPublishedFieldThreshold

public section

/-! Native whole source10.7, including its actual finite-span pairing
consequence. The preceding field theorem is now derived from the original
Gaussian model instead of supplied as a research assumption. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualAdaptiveTensorDisclosureWaitingPairing
open Set Filter MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open AdaptiveTensorDisclosureSource AdaptiveSourceProjectionMoments AdaptiveResidualEnergyLimit
open AdaptiveSourceProjectionRecursion AdaptiveTensorDisclosureWaitingOrthogonality
open ExternalFieldUniformCost ExternalFieldElementaryPenalty ExternalFieldSharpScalar
open scoped Topology InnerProductSpace NNReal

theorem actual_source_10_7_with_pairing {Θ : Type*} {l : Filter Θ} {p k0 : ℕ} (hp : 3≤p)
    (L : Θ→ℝ≥0)
    {dim : ℕ→ℕ} (hDim : ∀n,0<dim n) (hTop : Tendsto dim atTop atTop)
    {S : Θ→ℕ→Type} [∀θ n,MeasurableSpace (S θ n)]
    (μ : ∀θ n,Measure (S θ n)) [∀θ n,IsProbabilityMeasure (μ θ n)]
    (W0 : ∀θ n,S θ n→Submodule ℝ (Vector (dim n)))
    (hW0 : ∀θ n,Measurable (fun z : S θ n×Vector (dim n) => (W0 θ n z.1).starProjection z.2))
    (hRank0 : ∀θ n s,Module.finrank ℝ (W0 θ n s)≤k0)
    (u : ∀θ n,ℕ→S θ n×TensorSpace (dim n) p→Vector (dim n))
    (hu : ∀θ n j,Measurable[MeasurableSpace.comap (History (W0 θ n) (u θ n) j) inferInstance] (u θ n j))
    (horth : ∀θ n j z,u θ n j z∈(Space (W0 θ n) (u θ n) j z)ᗮ)
    (hun : ∀θ n j z,u θ n j z=0 ∨ ‖u θ n j z‖=1)
    (A : ∀θ n,S θ n→TensorSpace (dim n) p→Vector (dim n))
    (hA : ∀θ n,Measurable (Function.uncurry (A θ n)))
    (hLip : ∀θ n,∀ᵐs ∂μ θ n,LipschitzWith (L θ) (A θ n s))
    (hball : ∀θ n s J,‖A θ n s J‖≤Real.sqrt (dim n))
    (hδ : Tendsto (fun θ => energyDeficit (μ θ) (A θ)) l (𝓝 0)) (M : ℕ)
    (Y : ∀θ n,S θ n×Disorder (dim n) p→Vector (dim n))
    (hY : ∀θ n,Measurable (Y θ n))
    (hYball : ∀θ n z,‖Y θ n z‖≤Real.sqrt (dim n))
    (hYmem : ∀θ n z,Y θ n z∈Space (W0 θ n) (u θ n) M (sample z)) :
    Tendsto (fun θ => projectionLimit (μ θ) (W0 θ) (u θ) (A θ) M) l (𝓝 0) ∧
    Tendsto (fun θ => limsup (fun n => ∫z,
      |⟪algorithm (A θ n) z,Y θ n z⟫_ℝ/(dim n:ℝ)|^2
        ∂(μ θ n).prod (disorderLaw (dim n) p)) atTop) l (𝓝 0) := by
  exact AdaptiveTensorDisclosureWaitingPairing.actual_source_10_7_with_pairing hp L
    (fun θ => PurePActualPublishedFieldThreshold.actual_published_field_threshold hp (L θ))
    hDim hTop μ W0 hW0 hRank0 u hu horth hun A hA hLip hball hδ M Y hY hYball hYmem

end SphericalAging.ActualAdaptiveTensorDisclosureWaitingPairing
