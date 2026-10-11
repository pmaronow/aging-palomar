module

public import SphericalAging.ActualSphereOnlyForkMomentComparison
public import SphericalAging.ActualForkL2Estimate

public section

/-! Genuine L² fork transfer from actual k=1,2 product-current estimates
and the actual full annealed overlap variance. -/
noncomputable section
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereOnlyForkL2Estimate
open Set Filter MeasureTheory FiniteModel HardSphereDynamics
open ActualForkOverlapLaw ActualSphereOnlyForkMomentComparison ActualModelOverlapVariance
open ActualForkL2Estimate
open ActualOverlapConcentration ActualCompactJointOverlapVariance ActualOverlapVarianceLimit
open ActualSphereOnlyTensorUniformComparison ActualForkFisherWindowLimit ActualSphereRestrictedFisherBudget ActualSphereForkEndpoints
open TwoMomentL2Transfer
open scoped Topology NNReal ENNReal

theorem comparisonError_one_le_two {N p : ℕ} (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (T L : ℝ) :
    comparisonError (N:=N) (p:=p) (windowCoefficient p 1 β L) L β R hR T≤
      comparisonError (N:=N) (p:=p) (windowCoefficient p 2 β L) L β R hR T := by
  unfold comparisonError windowCoefficient
  simp only [Nat.cast_one,Nat.cast_ofNat]
  nlinarith [Real.exp_pos ((β:ℝ)*(p:ℝ)^2*SphereBadEventFisherMass.cutoff p*(2*L)),
    Real.sqrt_nonneg (L*(∫w in T..(T+L),full (N:=N) (p:=p) β R hR w))]

/-- Finite-N source fork L² ceiling. The CK mean bridge is deliberately
absent: the mean appearing here is the literal actual SDE overlap mean. -/
theorem actual_fork_centered_secondMoment_le {N p : ℕ} (hN : 3≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {T L a d c : ℝ} (hT : 0≤T) (ha : a∈Icc 0 L) (hd : d∈Icc 0 L) (hc : |c|≤1) :
    centeredError (N:=N) (p:=p) β R hR T a d c≤
      jointVarianceCeiling p β (T+3*L+1).toNNReal/(N:ℝ)+
      ((∫z,actualOverlap (p:=p) β R hR (T.toNNReal+a.toNNReal)
        ((T.toNNReal+a.toNNReal)+(a.toNNReal+d.toNNReal)) z ∂AnnealedModelLaw.law N p)-c)^2+
      3*comparisonError (N:=N) (p:=p) (windowCoefficient p 2 β L) L β R hR T := by
  have hn : 0<N := by omega
  have hL : 0≤L := ha.1.trans ha.2
  let s := T.toNNReal+a.toNNReal
  let t := s+(a.toNNReal+d.toNNReal)
  let H := (T+3*L+1).toNNReal
  have hs : s≤t := le_add_of_nonneg_right (by positivity)
  have ht : t≤H := by
    rw [←NNReal.coe_le_coe]
    dsimp only [t,s,H]
    simp only [NNReal.coe_add,Real.coe_toNNReal T hT,Real.coe_toNNReal a ha.1,
      Real.coe_toNNReal d hd.1,Real.coe_toNNReal _ (by positivity : 0≤T+3*L+1)]
    linarith [ha.2,hd.2]
  have hH : 0<H := by
    rw [←NNReal.coe_pos]
    dsimp only [H]
    rw [Real.coe_toNNReal _ (by positivity : 0≤T+3*L+1)]
    positivity
  have hQ := forkOverlap_memLp (p:=p) hn β R hR hNR T.toNNReal a.toNNReal d.toNNReal
  have hC := actualOverlap_memLp (p:=p) hN β R hR hNR s t
  have h1 := actual_fork_moment_uniform_bound (k:=1) (by omega : 2≤N) hp β R hR hNR hT ha hd (by norm_num : 1≤1)
  have h2 := actual_fork_moment_uniform_bound (k:=2) (by omega : 2≤N) hp β R hR hNR hT ha hd (by norm_num : 1≤2)
  simp only [pow_one] at h1
  have htransfer := centered_secondMoment_le_of_two_moments (forkLaw N p) (AnnealedModelLaw.law N p)
    (hQ.integrable (by norm_num : (1:ENNReal)≤2)) hQ.integrable_sq
    (hC.integrable (by norm_num : (1:ENNReal)≤2)) hC.integrable_sq hc h1 h2
  rw [centered_square_eq_mean_centered_add (AnnealedModelLaw.law N p)
    (hC.integrable (by norm_num : (1:ENNReal)≤2)) hC.integrable_sq c] at htransfer
  have hv := actual_overlap_centered_secondMoment_le hN hp β R hR hNR s t H hs ht hH
  have he := comparisonError_one_le_two (N:=N) (p:=p) β R hR T L
  exact htransfer.trans (by dsimp only [s,t,H] at hv ⊢;linarith)

end SphericalAging.ActualSphereOnlyForkL2Estimate
