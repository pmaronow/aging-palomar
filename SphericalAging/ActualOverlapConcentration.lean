module

public import SphericalAging.ActualOverlapVarianceLimit
public import SphericalAging.ActualCompactTransitionRegularity

public section

/-! Genuine fixed-time overlap concentration for the actual independent
ordered-Gaussian, uniform-sphere-initial, and Wiener-path model. Every
analytic transition regularity input is discharged from the actual first
and second variational SDEs and compact C² expectation calculus. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualOverlapConcentration
open FiniteModel HardSphereDynamics ActualSphereBackwardIto ActualModelOverlapVariance
open ActualCompactOverlapInnovation ActualCompactJointOverlapVariance
open ActualOverlapVarianceLimit ActualCompactTransitionRegularity
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem compactOverlapTest_regular (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : Disorder N p) (u : ℝ≥0) :
    SpatialC2Transition β R hR J (compactOverlapTest β R hR J u) :=
  compact_spatialC2Transition β R hR J
    (compactOverlapTest_contDiff β R hR J u) (compactOverlapTest_hasCompactSupport β R hR J u)

/-- Full-law finite-N variance of the actual physical overlap. No
concentration, moment, process-existence, or transition-regularity premise. -/
theorem actual_overlap_variance_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T) :
    variance (actualOverlap (p := p) β R hR s (s+u)) (AnnealedModelLaw.law N p)≤
      jointVarianceCeiling p β T/(N : ℝ) :=
  actual_model_overlap_variance hN hp β R hR hNR s u T hsu hT
    (fun J => compactOverlapTest_regular β R hR J u)

theorem actual_overlap_deviation_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T) (ε : ℝ) (hε : 0<ε) :
    (AnnealedModelLaw.law N p) {ω | ε≤|actualOverlap β R hR s (s+u) ω-
      ∫ z,actualOverlap β R hR s (s+u) z ∂AnnealedModelLaw.law N p|}≤
      ENNReal.ofReal (jointVarianceCeiling p β T/((N : ℝ)*ε^2)) :=
  actual_model_overlap_deviation_le hN hp β R hR hNR s u T hsu hT
    (fun J => compactOverlapTest_regular β R hR J u) ε hε

/-- A single derived O(1/N) second-moment ceiling works for every point
of the fixed time triangle. This does not assert a time-supremum limit. -/
theorem actual_overlap_centered_secondMoment_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s t T : ℝ≥0) (hst : s≤t) (ht : t≤T) (hT : 0<T) :
    (∫ ω,(actualOverlap (p := p) β R hR s t ω-
      ∫ z,actualOverlap β R hR s t z ∂AnnealedModelLaw.law N p)^2 ∂AnnealedModelLaw.law N p)≤
      jointVarianceCeiling p β T/(N : ℝ) := by
  have he : s+(t-s)=t := add_tsub_cancel_of_le hst
  have hh := actual_overlap_variance_le hN hp β R hR hNR s (t-s) T (by rwa [he]) hT
  rw [he] at hh
  rw [variance_eq_integral (actualOverlap_memLp hN β R hR hNR s t).aemeasurable] at hh
  exact hh

theorem actual_overlap_centered_L1_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s t T : ℝ≥0) (hst : s≤t) (ht : t≤T) (hT : 0<T) :
    (∫ ω,|actualOverlap (p := p) β R hR s t ω-
      ∫ z,actualOverlap β R hR s t z ∂AnnealedModelLaw.law N p| ∂AnnealedModelLaw.law N p)≤
      Real.sqrt (jointVarianceCeiling p β T/(N : ℝ)) := by
  let f := actualOverlap (N := N) (p := p) β R hR s t
  let P := AnnealedModelLaw.law N p
  let m : ℝ := ∫ z,f z ∂P
  have hmem : MemLp (fun ω => f ω-m) 2 P := (actualOverlap_memLp hN β R hR hNR s t).sub (memLp_const m)
  have hCS := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq P (fun ω => |f ω-m|) hmem.norm
  simp only [probReal_univ,one_mul,sq_abs] at hCS
  have hsq := hCS.trans (actual_overlap_centered_secondMoment_le hN hp β R hR hNR s t T hst ht hT)
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _))
    (div_nonneg (jointVarianceCeiling_nonneg _ _ _) (Nat.cast_nonneg N))).mpr hsq

theorem actual_overlap_variance_tendsto_zero (p : ℕ) (hp : 2≤p) (β : ℝ≥0)
    (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T) :
    Tendsto (fun n : ℕ => variance (canonicalOverlap (n+3) p β s (s+u))
      (AnnealedModelLaw.law (n+3) p)) atTop (𝓝 0) :=
  canonical_variance_tendsto_zero p hp β s u T hsu hT
    (fun n J => compactOverlapTest_regular β _ _ J u)

theorem actual_overlap_deviation_probability_tendsto_zero (p : ℕ) (hp : 2≤p) (β : ℝ≥0)
    (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T) (ε : ℝ) (hε : 0<ε) :
    Tendsto (fun n : ℕ => (AnnealedModelLaw.law (n+3) p).real
      {ω | ε≤|canonicalOverlap (n+3) p β s (s+u) ω-
        ∫ z,canonicalOverlap (n+3) p β s (s+u) z ∂AnnealedModelLaw.law (n+3) p|})
      atTop (𝓝 0) :=
  canonical_deviation_probability_tendsto_zero p hp β s u T hsu hT
    (fun n J => compactOverlapTest_regular β _ _ J u) ε hε

theorem actual_overlap_centered_L1_tendsto_zero (p : ℕ) (hp : 2≤p) (β : ℝ≥0)
    (s t T : ℝ≥0) (hst : s≤t) (ht : t≤T) (hT : 0<T) :
    Tendsto (fun n : ℕ => ∫ ω,|canonicalOverlap (n+3) p β s t ω-
      ∫ z,canonicalOverlap (n+3) p β s t z ∂AnnealedModelLaw.law (n+3) p|
        ∂AnnealedModelLaw.law (n+3) p) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _))
    (fun n => actual_overlap_centered_L1_le (by omega : 3≤n+3) hp β _ _
      (modelRadius_sphere_bound (n+3)) s t T hst ht hT) ?_
  have hh := ((tendsto_add_atTop_iff_nat 3).mpr
    (tendsto_const_div_atTop_nhds_zero_nat (jointVarianceCeiling p β T))).sqrt
  simpa only [Real.sqrt_zero] using hh

end SphericalAging.ActualOverlapConcentration
