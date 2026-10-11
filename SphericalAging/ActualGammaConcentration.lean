module

public import SphericalAging.ActualJointGammaVariance
public import SphericalAging.ActualOverlapVarianceLimit

public section

/-! Full actual Γ second-moment concentration, uniformly bounded at every
point of a compact time triangle, and fixed-time dimension limits. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualGammaConcentration
open HardSphereDynamics ActualBrownianPrimitiveTimeModulus ActualJointGammaVariance
open ActualOverlapVarianceLimit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem actual_gamma_centered_secondMoment_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s t T : ℝ≥0) (hst : s≤t) (ht : t≤T) (hT : 0<T) :
    (∫ ω,(actualGamma (p:=p) β R hR t s ω-
      ∫ z,actualGamma β R hR t s z ∂AnnealedModelLaw.law N p)^2 ∂AnnealedModelLaw.law N p)≤
      ActualJointGammaVariance.jointVarianceCeiling p β T/(N : ℝ) := by
  have he : s+(t-s)=t := add_tsub_cancel_of_le hst
  have hh := actual_gamma_variance_le hN hp β R hR hNR s (t-s) T (by rwa [he]) hT
  rw [he] at hh
  rw [variance_eq_integral (actualGamma_memLp_two (p:=p) (by omega : 1≤N) β R hR hNR t s).aemeasurable] at hh
  exact hh

theorem actual_gamma_centered_L1_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s t T : ℝ≥0) (hst : s≤t) (ht : t≤T) (hT : 0<T) :
    (∫ ω,|actualGamma (p:=p) β R hR t s ω-
      ∫ z,actualGamma β R hR t s z ∂AnnealedModelLaw.law N p| ∂AnnealedModelLaw.law N p)≤
      Real.sqrt (ActualJointGammaVariance.jointVarianceCeiling p β T/(N : ℝ)) := by
  let f := actualGamma (N:=N) (p:=p) β R hR t s
  let P := AnnealedModelLaw.law N p
  let m : ℝ := ∫z,f z ∂P
  have hmem : MemLp (fun ω => f ω-m) 2 P :=
    (actualGamma_memLp_two (p:=p) (by omega : 1≤N) β R hR hNR t s).sub (memLp_const m)
  have hCS := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq P (fun ω => |f ω-m|) hmem.norm
  simp only [probReal_univ,one_mul,sq_abs] at hCS
  have hh := hCS.trans (actual_gamma_centered_secondMoment_le hN hp β R hR hNR s t T hst ht hT)
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _))
    (div_nonneg (ActualJointGammaVariance.jointVarianceCeiling_nonneg p β T) (Nat.cast_nonneg N))).mpr hh

theorem actual_gamma_deviation_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T) (ε : ℝ) (hε : 0<ε) :
    (AnnealedModelLaw.law N p) {ω | ε≤|actualGamma β R hR (s+u) s ω-
      ∫ z,actualGamma β R hR (s+u) s z ∂AnnealedModelLaw.law N p|}≤
      ENNReal.ofReal (ActualJointGammaVariance.jointVarianceCeiling p β T/((N : ℝ)*ε^2)) := by
  refine (meas_ge_le_variance_div_sq (actualGamma_memLp_two (p:=p) (by omega : 1≤N) β R hR hNR (s+u) s) hε).trans ?_
  apply ENNReal.ofReal_le_ofReal
  refine (div_le_div_of_nonneg_right (actual_gamma_variance_le hN hp β R hR hNR s u T hsu hT) (sq_nonneg ε)).trans_eq ?_
  ring

@[expose] def canonicalGamma (N p : ℕ) (β : ℝ≥0) (t s : ℝ≥0) :
    AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N→ℝ :=
  actualGamma β (modelRadius N) (modelRadius_pos N) t s

theorem actual_gamma_variance_tendsto_zero (p : ℕ) (hp : 2≤p) (β : ℝ≥0)
    (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T) :
    Tendsto (fun n : ℕ => variance (canonicalGamma (n+3) p β (s+u) s)
      (AnnealedModelLaw.law (n+3) p)) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => variance_nonneg _ _) (fun n =>
    actual_gamma_variance_le (by omega : 3≤n+3) hp β _ _
      (modelRadius_sphere_bound (n+3)) s u T hsu hT) ?_
  exact (tendsto_add_atTop_iff_nat 3).mpr (tendsto_const_div_atTop_nhds_zero_nat
    (ActualJointGammaVariance.jointVarianceCeiling p β T))

theorem actual_gamma_centered_L1_tendsto_zero (p : ℕ) (hp : 2≤p) (β : ℝ≥0)
    (s t T : ℝ≥0) (hst : s≤t) (ht : t≤T) (hT : 0<T) :
    Tendsto (fun n : ℕ => ∫ ω,|canonicalGamma (n+3) p β t s ω-
      ∫ z,canonicalGamma (n+3) p β t s z ∂AnnealedModelLaw.law (n+3) p|
        ∂AnnealedModelLaw.law (n+3) p) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _))
    (fun n => actual_gamma_centered_L1_le (by omega : 3≤n+3) hp β _ _
      (modelRadius_sphere_bound (n+3)) s t T hst ht hT) ?_
  have hh := ((tendsto_add_atTop_iff_nat 3).mpr
    (tendsto_const_div_atTop_nhds_zero_nat (ActualJointGammaVariance.jointVarianceCeiling p β T))).sqrt
  simpa only [Real.sqrt_zero] using hh

end SphericalAging.ActualGammaConcentration
