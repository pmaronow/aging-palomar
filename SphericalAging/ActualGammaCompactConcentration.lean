module

public import SphericalAging.ActualGammaFutureObservation

public section

/-! A genuine dimension-uniform Γ concentration ceiling for every pair of
state and Brownian observation times in a compact square. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualGammaCompactConcentration
open HardSphereDynamics ActualBrownianPrimitiveTimeModulus ActualGammaConcentration
open ActualGammaFutureObservation
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def compactVarianceCeiling (p : ℕ) (β : ℝ≥0) (T : ℝ≥0) : ℝ :=
  2*ActualJointGammaVariance.jointVarianceCeiling p β T+(T : ℝ)

theorem compactVarianceCeiling_nonneg (p : ℕ) (β : ℝ≥0) (T : ℝ≥0) :
    0≤compactVarianceCeiling p β T := by
  unfold compactVarianceCeiling
  have := ActualJointGammaVariance.jointVarianceCeiling_nonneg p β T
  positivity

theorem actual_gamma_centered_secondMoment_le_square (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (t s T : ℝ≥0) (ht : t≤T) (hs : s≤T) (hT : 0<T) :
    (∫ω,(actualGamma (p:=p) β R hR t s ω-
      ∫z,actualGamma β R hR t s z ∂AnnealedModelLaw.law N p)^2 ∂AnnealedModelLaw.law N p)≤
      compactVarianceCeiling p β T/(N : ℝ) := by
  let P := AnnealedModelLaw.law N p
  have hn : 1≤N := by omega
  have hC := ActualJointGammaVariance.jointVarianceCeiling_nonneg p β T
  rcases le_total s t with hst|hts
  · refine (actual_gamma_centered_secondMoment_le hN hp β R hR hNR s t T hst ht hT).trans ?_
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    dsimp only [compactVarianceCeiling]
    linarith [T.coe_nonneg]
  have hnoise := actual_futurePairing_secondMoment (p:=p) hn β R hR hNR t s hts
  have hΓst := actualGamma_memLp_two (p:=p) hn β R hR hNR t s
  have hΓtt := actualGamma_memLp_two (p:=p) hn β R hR hNR t t
  have hMean : (∫ω,actualGamma (p:=p) β R hR t s ω ∂P)=∫ω,actualGamma β R hR t t ω ∂P := by
    rw [integral_congr_ae (.of_forall (gamma_eq_diagonal_add_future (p:=p) β R hR t s)),
      integral_add (hΓtt.integrable (by norm_num)) (hnoise.1.integrable (by norm_num)),hnoise.2.1,add_zero]
  let m := ∫ω,actualGamma (p:=p) β R hR t t ω ∂P
  have hA : Integrable (fun ω => (actualGamma (p:=p) β R hR t s ω-m)^2) P :=
    (hΓst.sub (memLp_const m)).integrable_sq
  have hB : Integrable (fun ω => (actualGamma (p:=p) β R hR t t ω-m)^2) P :=
    (hΓtt.sub (memLp_const m)).integrable_sq
  have hD : Integrable (fun ω => 2*(actualGamma (p:=p) β R hR t t ω-m)^2+
      2*(futurePairing β R hR t s ω)^2) P :=
    (hB.const_mul 2).add (hnoise.1.integrable_sq.const_mul 2)
  have hi := integral_mono hA hD (fun ω => by
    rw [gamma_eq_diagonal_add_future]
    nlinarith [sq_nonneg (actualGamma (p:=p) β R hR t t ω-m-futurePairing β R hR t s ω)])
  rw [integral_add (hB.const_mul 2) (hnoise.1.integrable_sq.const_mul 2),integral_const_mul,
    integral_const_mul,hnoise.2.2] at hi
  have hb := actual_gamma_centered_secondMoment_le (p:=p) hN hp β R hR hNR t t T le_rfl ht hT
  have hs' : (s : ℝ)≤T := by exact_mod_cast hs
  have htime : (s : ℝ)-(t : ℝ)≤T := by linarith [t.coe_nonneg]
  change (∫ω,(actualGamma (p:=p) β R hR t s ω-_ )^2 ∂P)≤_
  rw [hMean]
  refine hi.trans ((add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num))
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right htime (by positivity : (0 : ℝ)≤2*N)) (by norm_num))).trans_eq ?_)
  dsimp only [compactVarianceCeiling]
  ring

theorem actual_gamma_variance_le_square (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (t s T : ℝ≥0) (ht : t≤T) (hs : s≤T) (hT : 0<T) :
    variance (actualGamma (p:=p) β R hR t s) (AnnealedModelLaw.law N p)≤
      compactVarianceCeiling p β T/(N : ℝ) := by
  rw [variance_eq_integral (actualGamma_memLp_two (p:=p) (by omega : 1≤N) β R hR hNR t s).aemeasurable]
  exact actual_gamma_centered_secondMoment_le_square hN hp β R hR hNR t s T ht hs hT

theorem actual_gamma_centered_L1_le_square (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (t s T : ℝ≥0) (ht : t≤T) (hs : s≤T) (hT : 0<T) :
    (∫ω,|actualGamma (p:=p) β R hR t s ω-
      ∫z,actualGamma β R hR t s z ∂AnnealedModelLaw.law N p| ∂AnnealedModelLaw.law N p)≤
      Real.sqrt (compactVarianceCeiling p β T/(N : ℝ)) := by
  let f := actualGamma (N:=N) (p:=p) β R hR t s
  let P := AnnealedModelLaw.law N p
  let m := ∫z,f z ∂P
  have hmem : MemLp (fun ω => f ω-m) 2 P :=
    (actualGamma_memLp_two (p:=p) (by omega : 1≤N) β R hR hNR t s).sub (memLp_const m)
  have hCS := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq P (fun ω => |f ω-m|) hmem.norm
  simp only [probReal_univ,one_mul,sq_abs] at hCS
  have hh := hCS.trans (actual_gamma_centered_secondMoment_le_square hN hp β R hR hNR t s T ht hs hT)
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _))
    (div_nonneg (compactVarianceCeiling_nonneg p β T) (Nat.cast_nonneg N))).mpr hh

theorem actual_gamma_variance_tendsto_zero_square (p : ℕ) (hp : 2≤p) (β : ℝ≥0)
    (t s T : ℝ≥0) (ht : t≤T) (hs : s≤T) (hT : 0<T) :
    Tendsto (fun n : ℕ => variance (canonicalGamma (n+3) p β t s)
      (AnnealedModelLaw.law (n+3) p)) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => variance_nonneg _ _) (fun n =>
    actual_gamma_variance_le_square (by omega : 3≤n+3) hp β _ _
      (ActualOverlapVarianceLimit.modelRadius_sphere_bound (n+3)) t s T ht hs hT) ?_
  exact (tendsto_add_atTop_iff_nat 3).mpr (tendsto_const_div_atTop_nhds_zero_nat (compactVarianceCeiling p β T))

end SphericalAging.ActualGammaCompactConcentration
