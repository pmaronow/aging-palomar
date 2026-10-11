module

public import SphericalAging.AdaptiveSourceProjectionRecursion
public import SphericalAging.AdaptiveInitialSpanLimit

public section

/-! Complete source Proposition10.7: every fixed finite literal adaptive
query span is orthogonal in mean square to a threshold-saturating seeded
Lipschitz algorithm. The Lipschitz constant may vary in the outer limit. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AdaptiveTensorDisclosureWaitingOrthogonality
open Set Filter MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open AdaptiveTensorDisclosureSource AdaptiveSourceProjectionMoments AdaptiveResidualEnergyLimit
open AdaptiveSourceProjectionRecursion AlgorithmEnergyDeficit AdaptivePairingLimitTransfer
open ExternalFieldUniformCost ExternalFieldElementaryPenalty ExternalFieldSharpScalar
open scoped Topology InnerProductSpace NNReal

theorem actual_source_10_7 {Θ : Type*} {l : Filter Θ} {p k0 : ℕ} (hp : 3≤p)
    (L : Θ→ℝ≥0) (H : ∀θ,PublishedFieldThreshold p (L θ))
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
    (hδ : Tendsto (fun θ => energyDeficit (μ θ) (A θ)) l (𝓝 0)) (M : ℕ) :
    Tendsto (fun θ => projectionLimit (μ θ) (W0 θ) (u θ) (A θ) M) l (𝓝 0) := by
  let ψ j θ := projectionLimit (μ θ) (W0 θ) (u θ) (A θ) j
  let δ θ := energyDeficit (μ θ) (A θ)
  have hψ j θ : 0≤ψ j θ := by
    have hb n := projectionEnergy_bounds (hDim n) (μ θ n) (span (W0 θ n) (u θ n) j)
      (algorithm (A θ n))
      (AdaptiveSourceProjectionMoments.projection_measurable (S θ n) (W0 θ n) (hW0 θ n)
        (u θ n) (hu θ n) j (A θ n) (hA θ n)) (fun z => hball θ n z.1 _)
    exact le_limsup_of_frequently_le (Eventually.of_forall (fun n => (hb n).1)).frequently
      (isBoundedUnder_of_eventually_le (Eventually.of_forall (fun n => (hb n).2)))
  have hq : 0<2/(p:ℝ) := by positivity
  have hInitial θ : ψ 0 θ≤(k0:ℝ)*(δ θ/betaD p)^(2/(p:ℝ)) := by
    have hh := AdaptiveInitialSpanLimit.initial_span_limsup hp (H θ) dim hDim hTop (μ θ)
      (W0 θ) (hW0 θ) (hRank0 θ) (fun n => algorithm (A θ n))
      (fun n => algorithm_measurable (A θ n) (hA θ n))
      (fun n z => hball θ n z.1 _)
      (fun n => (hLip θ n).mono (fun s hs => by
        convert hs using 1
        funext J
        simp only [algorithm,WithLp.toLp_ofLp]))
    have hsp n : span (W0 θ n) (u θ n) 0=(fun z : S θ n×Disorder (dim n) p => W0 θ n z.1) := rfl
    simpa only [ψ,δ,projectionLimit,energyDeficit,hsp] using hh
  have hzero : Tendsto (ψ 0) l (𝓝 0) := by
    have hbase := hδ.div_const (betaD p)
    have hpow := (Real.continuous_rpow_const hq.le).continuousAt.tendsto.comp hbase
    have ht : Tendsto (fun θ => (k0:ℝ)*(δ θ/betaD p)^(2/(p:ℝ))) l (𝓝 0) := by
      simpa only [δ,Function.comp_def,zero_div,Real.zero_rpow hq.ne',mul_zero] using hpow.const_mul (k0:ℝ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (hψ 0) hInitial
  have hstep j θ : ψ (j+1) θ≤ψ j θ+
      ((δ θ+(p:ℝ)*Real.sqrt (GaussianLandscapeMoments.momentCeiling p 2)*Real.sqrt (ψ j θ))/betaD p)^(2/(p:ℝ)) :=
    (actual_projection_recursion hp (H θ) hDim hTop (μ θ) (W0 θ) (hW0 θ) (hRank0 θ)
      (u θ) (hu θ) (A θ) (hA θ) (hLip θ) (hball θ) j
      (fun n => horth θ n j) (fun n => hun θ n j)).2
  exact vanishing_projection_recursion (betaD_positive hp) hq hψ hδ hzero hstep M

end SphericalAging.AdaptiveTensorDisclosureWaitingOrthogonality
