module

public import SphericalAging.ActualForkMomentComparison

public section

/-! Genuine L² fork transfer from actual k=1,2 product-current estimates
and the actual full annealed overlap variance. -/
noncomputable section
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualForkL2Estimate
open Set Filter MeasureTheory FiniteModel HardSphereDynamics
open ActualForkOverlapLaw ActualForkMomentComparison ActualModelOverlapVariance
open ActualOverlapConcentration ActualCompactJointOverlapVariance ActualOverlapVarianceLimit
open ActualTensorUniformComparison ForkFisherWindowLimit SphereFisherHelly ActualSphereForkEndpoints
open TwoMomentL2Transfer
open scoped Topology NNReal ENNReal

@[expose] def centeredError {N p : ℕ} (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (T a d c : ℝ) : ℝ :=
  ∫z,(forkOverlap (p:=p) β R hR T.toNNReal a.toNNReal d.toNNReal z-c)^2 ∂forkLaw N p

theorem centeredError_bounds {N p : ℕ} (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (T a d c : ℝ) (hc : |c|≤1) :
    0≤centeredError (N:=N) (p:=p) β R hR T a d c ∧ centeredError (N:=N) (p:=p) β R hR T a d c≤4 := by
  have hm := ((forkOverlap_memLp (p:=p) hN β R hR hNR T.toNNReal a.toNNReal d.toNNReal).sub
    (memLp_const c)).integrable_sq
  refine ⟨integral_nonneg (fun _ => sq_nonneg _),?_⟩
  have hh : ∀ᵐz ∂forkLaw N p,
      (forkOverlap β R hR T.toNNReal a.toNNReal d.toNNReal z-c)^2≤4 := by
    filter_upwards [forkOverlap_abs_le_one (p:=p) hN β R hR hNR T.toNNReal a.toNNReal d.toNNReal]
      with z hz
    have ha := (abs_sub (forkOverlap β R hR T.toNNReal a.toNNReal d.toNNReal z) c).trans
      (add_le_add hz hc)
    have hs := sq_abs (forkOverlap β R hR T.toNNReal a.toNNReal d.toNNReal z-c)
    nlinarith [abs_nonneg (forkOverlap β R hR T.toNNReal a.toNNReal d.toNNReal z-c)]
  exact (integral_mono_ae hm (integrable_const 4) hh).trans_eq (by simp)

theorem comparisonError_one_le_two {N p : ℕ} (β : ℝ≥0) (E : FisherDensity N p β)
    (T L : ℝ) :
    comparisonError (windowCoefficient p 1 β L) L E T≤
      comparisonError (windowCoefficient p 2 β L) L E T := by
  unfold comparisonError windowCoefficient
  simp only [Nat.cast_one,Nat.cast_ofNat]
  nlinarith [Real.exp_pos ((β:ℝ)*(p:ℝ)^2*SphereBadEventFisherMass.cutoff p*(2*L)),
    Real.sqrt_nonneg (L*(∫w in T..(T+L),E.full w))]

/-- Finite-N source fork L² ceiling. The CK mean bridge is deliberately
absent: the mean appearing here is the literal actual SDE overlap mean. -/
theorem actual_fork_centered_secondMoment_le {N p : ℕ} (hN : 3≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (E : FisherDensity N p β) (hLaw : WaitingDensityLaw β R hR E)
    {T L a d c : ℝ} (hT : 0≤T) (ha : a∈Icc 0 L) (hd : d∈Icc 0 L) (hc : |c|≤1) :
    centeredError (N:=N) (p:=p) β R hR T a d c≤
      jointVarianceCeiling p β (T+3*L+1).toNNReal/(N:ℝ)+
      ((∫z,actualOverlap (p:=p) β R hR (T.toNNReal+a.toNNReal)
        ((T.toNNReal+a.toNNReal)+(a.toNNReal+d.toNNReal)) z ∂AnnealedModelLaw.law N p)-c)^2+
      3*comparisonError (windowCoefficient p 2 β L) L E T := by
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
  have h1 := actual_fork_moment_uniform_bound (k:=1) (by omega : 2≤N) hp β R hR hNR E hLaw hT ha hd (by norm_num : 1≤1)
  have h2 := actual_fork_moment_uniform_bound (k:=2) (by omega : 2≤N) hp β R hR hNR E hLaw hT ha hd (by norm_num : 1≤2)
  simp only [pow_one] at h1
  have htransfer := centered_secondMoment_le_of_two_moments (forkLaw N p) (AnnealedModelLaw.law N p)
    (hQ.integrable (by norm_num : (1:ENNReal)≤2)) hQ.integrable_sq
    (hC.integrable (by norm_num : (1:ENNReal)≤2)) hC.integrable_sq hc h1 h2
  rw [centered_square_eq_mean_centered_add (AnnealedModelLaw.law N p)
    (hC.integrable (by norm_num : (1:ENNReal)≤2)) hC.integrable_sq c] at htransfer
  have hv := actual_overlap_centered_secondMoment_le hN hp β R hR hNR s t H hs ht hH
  have he := comparisonError_one_le_two β E T L
  exact htransfer.trans (by dsimp only [s,t,H] at hv ⊢;linarith)

end SphericalAging.ActualForkL2Estimate
