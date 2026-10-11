module

public import SphericalAging.AdaptiveSourceProjectionMoments
public import SphericalAging.AdaptivePairingLimitTransfer

public section

/-! Source10.7 Steps2--4: the quantitative adaptive projection recursion
for literal histories, with all costs and moments derived from the
original Gaussian disorder and the published external-field theorem. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AdaptiveSourceProjectionRecursion
open Set Filter MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open AdaptiveTensorDisclosureSource AdaptiveSourceProjectionMoments AdaptiveResidualEnergyLimit
open AlgorithmEnergyDeficit AdaptivePairingLimitTransfer GaussianLandscapeMoments
open ExternalFieldUniformCost ExternalFieldElementaryPenalty ExternalFieldSharpScalar
open scoped Topology InnerProductSpace NNReal

@[expose] def projectionLimit {p : ℕ} {dim : ℕ→ℕ} {S : ℕ→Type}
    [∀n,MeasurableSpace (S n)] (μ : ∀n,Measure (S n))
    (W0 : ∀n,S n→Submodule ℝ (Vector (dim n)))
    (u : ∀n,ℕ→S n×TensorSpace (dim n) p→Vector (dim n))
    (A : ∀n,S n→TensorSpace (dim n) p→Vector (dim n)) (j : ℕ) : ℝ :=
  limsup (fun n => projectionEnergy (μ n) (span (W0 n) (u n) j) (algorithm (A n))) atTop

@[expose] def energyDeficit {p : ℕ} {dim : ℕ→ℕ} {S : ℕ→Type}
    [∀n,MeasurableSpace (S n)] (μ : ∀n,Measure (S n))
    (A : ∀n,S n→TensorSpace (dim n) p→Vector (dim n)) : ℝ :=
  deficit (thresholdEnergy p) (fun n => meanEnergy (μ n) (algorithm (A n)))

theorem actual_projection_recursion {p k0 : ℕ} (hp : 3≤p) {L : ℝ≥0}
    (H : PublishedFieldThreshold p L) {dim : ℕ→ℕ}
    (hDim : ∀n,0<dim n) (hTop : Tendsto dim atTop atTop)
    {S : ℕ→Type} [∀n,MeasurableSpace (S n)]
    (μ : ∀n,Measure (S n)) [∀n,IsProbabilityMeasure (μ n)]
    (W0 : ∀n,S n→Submodule ℝ (Vector (dim n)))
    (hW0 : ∀n,Measurable (fun z : S n×Vector (dim n) => (W0 n z.1).starProjection z.2))
    (hRank0 : ∀n s,Module.finrank ℝ (W0 n s)≤k0)
    (u : ∀n,ℕ→S n×TensorSpace (dim n) p→Vector (dim n))
    (hu : ∀n j,Measurable[MeasurableSpace.comap (History (W0 n) (u n) j) inferInstance] (u n j))
    (A : ∀n,S n→TensorSpace (dim n) p→Vector (dim n))
    (hA : ∀n,Measurable (Function.uncurry (A n)))
    (hLip : ∀n,∀ᵐs ∂μ n,LipschitzWith L (A n s))
    (hball : ∀n s J,‖A n s J‖≤Real.sqrt (dim n))
    (j : ℕ) (horth : ∀n z,u n j z∈(Space (W0 n) (u n) j z)ᗮ)
    (hun : ∀n z,u n j z=0 ∨ ‖u n j z‖=1) :
    (limsup (fun n => powerMoment (μ n) (u n j) (A n)) atTop≤
      (energyDeficit μ A+(p:ℝ)*Real.sqrt (momentCeiling p 2)*Real.sqrt (projectionLimit μ W0 u A j))/betaD p) ∧
    projectionLimit μ W0 u A (j+1)≤projectionLimit μ W0 u A j+
      ((energyDeficit μ A+(p:ℝ)*Real.sqrt (momentCeiling p 2)*Real.sqrt (projectionLimit μ W0 u A j))/betaD p)^(2/(p:ℝ)) := by
  let e n := meanEnergy (μ n) (residual (span (W0 n) (u n) j) (algorithm (A n)))
  let m n := powerMoment (μ n) (u n j) (A n)
  let a n := projectionEnergy (μ n) (span (W0 n) (u n) j) (algorithm (A n))
  let b n := projectionEnergy (μ n) (span (W0 n) (u n) (j+1)) (algorithm (A n))
  have hgood n : ∀ᵐs ∂μ n,LipschitzWith L (A n s) ∧ ∀J,‖A n s J‖≤Real.sqrt (dim n) :=
    (hLip n).mono (fun s hs => ⟨hs,hball n s⟩)
  have hCost := AdaptiveResidualSourceCost.actual_source_cost_eventually hp H dim hDim hTop μ W0 hW0
    hRank0 u hu A hA hgood j horth hun
  have hcost : ∀ε>0,∀ᶠn in atTop,e n+betaD p*m n≤thresholdEnergy p+ε := by
    intro ε hε
    filter_upwards [hCost ε hε] with n hn
    rw [source_cost_integral_eq (hDim n) hp (μ n) (W0 n) (hW0 n) (u n) (hu n)
      (A n) (hA n) (hball n) j (hun n)] at hn
    exact hn
  have hP n k := AdaptiveSourceProjectionMoments.projection_measurable (S n) (W0 n) (hW0 n)
    (u n) (hu n) k (A n) (hA n)
  have hAM n := algorithm_measurable (A n) (hA n)
  have hAb n z : ‖algorithm (A n) z‖≤Real.sqrt (dim n) := hball n z.1 _
  have heB n : |e n|≤momentCeiling p 1 := meanEnergy_abs_bound (hDim n) (by omega : 0<p) (μ n)
    (residual (span (W0 n) (u n) j) (algorithm (A n)))
    (residual_measurable _ _ (hAM n) (hP n j)) (residual_ball _ _ (hAb n))
  have heBelow : IsBoundedUnder (·≥·) atTop e :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n =>
      show -momentCeiling p 1≤e n from by linarith [heB n,neg_abs_le (e n)])
  have hM n : 0≤m n ∧ m n≤1 := powerMoment_bounds (hDim n) (μ n) (u n j)
    (AdaptiveResidualSourceCost.query_measurable (S n) (W0 n) (hW0 n) (u n) (hu n) j)
    (A n) (hA n) (hun n) (hball n)
  have hEnergy := actual_residual_energy_liminf (by omega : 0<p) hDim μ
    (fun n => span (W0 n) (u n) j) (fun n => algorithm (A n)) hAM
    (fun n => hP n j) hAb (thresholdEnergy p)
  have hMom := penalty_limsup_le (betaD_positive hp) heBelow (fun n => (hM n).1) hcost
    (show thresholdEnergy p-(energyDeficit μ A+(p:ℝ)*Real.sqrt (momentCeiling p 2)*
      Real.sqrt (projectionLimit μ W0 u A j))≤liminf e atTop from by
      change thresholdEnergy p-deficit (thresholdEnergy p) (fun n => meanEnergy (μ n) (algorithm (A n)))-
        (p:ℝ)*Real.sqrt (momentCeiling p 2)*Real.sqrt (limsup a atTop)≤liminf e atTop at hEnergy
      dsimp only [energyDeficit,projectionLimit]
      linarith)
  refine ⟨hMom,?_⟩
  exact projection_limsup_recursion (show 0≤2/(p:ℝ) by positivity)
    (fun n => projectionEnergy_bounds (hDim n) (μ n) _ _ (hP n j) (hAb n))
    (fun n => projectionEnergy_bounds (hDim n) (μ n) _ _ (hP n (j+1)) (hAb n))
    hM (fun n => projectionEnergy_succ (hDim n) (by omega : 2≤p) (μ n) (W0 n) (hW0 n)
      (u n) (hu n) (A n) (hA n) (hball n) j (horth n) (hun n)) hMom

end SphericalAging.AdaptiveSourceProjectionRecursion
