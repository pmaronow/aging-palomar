module

public import SphericalAging.FiniteDisclosureAmbientCost

public section

/-! The fixed finite-rank adaptive residual cost tends to the threshold
from above, uniformly over the genuinely constructed histories. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureCostLimit
open Set Filter MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosureAmbient FiniteDisclosureAmbientCost
open ExternalFieldUniformCost ExternalFieldElementaryPenalty ExternalFieldSharpScalar
open scoped Topology InnerProductSpace NNReal

 theorem actual_cost_eventually {p k : ℕ} (hp : 3≤p) {L : ℝ≥0} (H : PublishedFieldThreshold p L)
    (dim steps : ℕ→ℕ) (hDim : ∀n,0<dim n) (hTop : Tendsto dim atTop atTop)
    {S : ℕ→Type} [∀n,MeasurableSpace (S n)] (μ : ∀n,Measure (S n)) [∀n,IsProbabilityMeasure (μ n)]
    (P : ∀n,Plan (dim n) p (steps n) 0 (S n))
    (A : ∀n,S n→TensorSpace (dim n) p→Vector (dim n))
    (hA : ∀n,Measurable (Function.uncurry (A n)))
    (hgood : ∀n,∀ᵐs ∂μ n,LipschitzWith L (A n s) ∧ ∀J,‖A n s J‖≤Real.sqrt (dim n))
    (u : ∀n,Past (dim n) p (steps n) 0 (S n)→Vector (dim n)) (hu : ∀n,Measurable (u n))
    (hRank : ∀n z,Module.finrank ℝ (actualSpace (P n) z)≤k)
    (horth : ∀n z,u n (actualHistory (P n) z)∈(actualSpace (P n) z)ᗮ)
    (hun : ∀n z,u n (actualHistory (P n) z)=0 ∨ ‖u n (actualHistory (P n) z)‖=1) :
    ∀ε>0,∀ᶠn in atTop,
      (∫z,cost (P n) (A n) (u n) z ∂(μ n).prod (stdGaussian (TensorSpace (dim n) p)))≤thresholdEnergy p+ε := by
  intro ε hε
  obtain ⟨N0,hN0⟩ := (eventually_atTop.mp (uniform_meanCost_eventually hp H (show 0<ε/2 by linarith)))
  have hr : Tendsto (fun n => betaD p*(k:ℝ)/(dim n:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
        (tendsto_natCast_atTop_atTop.comp hTop)).const_mul (betaD p*(k:ℝ)))
  filter_upwards [hTop.eventually_ge_atTop (N0+k),hTop.eventually_gt_atTop k,
    hr.eventually (eventually_lt_nhds (show (0:ℝ)<ε/2 by linarith))] with n hn hnk hnr
  have hb : ∀m,dim n-k≤m→1≤m→∀B : BallFieldAlgorithm m p L,meanCost B≤thresholdEnergy p+ε/2 := by
    intro m hm _ B
    exact hN0 m (by omega) B
  have hh := actual_mean_bound (hDim n) hnk hp (show 0≤ε/2 by linarith) hb
    (P n) (μ n) (A n) (hA n) (hgood n) (u n) (hu n) (hRank n) (horth n) (hun n)
  linarith

end SphericalAging.FiniteDisclosureCostLimit
