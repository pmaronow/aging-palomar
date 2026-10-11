module

public import SphericalAging.DyadicSquareSupremum
public import SphericalAging.CountableCenteredSup
public import SphericalAging.ActualOverlapDyadicApproximation
public import SphericalAging.ActualMeanKernelTimeCompactness

public section

/-! The literal centered actual correlation supremum is a measurable
countable dyadic supremum on genuine continuous sample paths. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal InnerProductSpace
namespace SphericalAging.ActualOverlapCompactPathConcentration
open HardSphereDynamics ActualStateIncrementMoments ActualNormalizedStateFourthIncrement
open ActualNormalizedOverlap ActualModelOverlapVariance ActualOverlapTimeModulus
open ActualOverlapDyadicApproximation DyadicSquareSupremum CountableCenteredSup
open ActualMeanKernelTimeCompactness
variable {N p : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose] def overlapCenteredSup (N p : ℕ) (β R : ℝ≥0) (hR : 0 < (R:ℝ)) (T : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : ℝ :=
  squareSup (fun z : ℝ≥0×ℝ≥0 => |actualOverlap β R hR z.1 z.2 ω-
    ∫v,actualOverlap β R hR z.1 z.2 v ∂AnnealedModelLaw.law N p|) T

@[expose] def gridOverlap (β R : ℝ≥0) (hR : 0 < (R:ℝ)) (T : ℝ≥0) (i : GridIndex) :
    AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N→ℝ :=
  actualOverlap β R hR (gridPair T i).1 (gridPair T i).2

theorem overlapMean_continuous (hN : 1 ≤ N) (hp : 0 < p) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2) :
    Continuous (fun z : ℝ≥0×ℝ≥0 => ∫ω,actualOverlap (p:=p) β R hR z.1 z.2 ω ∂AnnealedModelLaw.law N p) := by
  exact (actual_overlap_means_equicontinuous (fun _ : Unit => N) (fun _ => hN) p hp β
    (fun _ => R) (fun _ => hR) (fun _ => hNR)).continuous ()

theorem overlapCenteredSup_ae_countable (hN : 1 ≤ N) (hp : 0 < p) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2) (T : ℝ≥0) :
    overlapCenteredSup N p β R hR T =ᵐ[AnnealedModelLaw.law N p]
      centeredSup (gridOverlap (p:=p) β R hR T) (AnnealedModelLaw.law N p) := by
  have hmean (z : ℝ≥0×ℝ≥0) : |∫ω,actualOverlap (p:=p) β R hR z.1 z.2 ω ∂AnnealedModelLaw.law N p| ≤ 1 := by
    refine abs_integral_le_integral_abs.trans ?_
    calc
      _ ≤ ∫ω,(1:ℝ) ∂AnnealedModelLaw.law N p := integral_mono_ae
        ((actualOverlap_memLp_two hN β R hR hNR z.1 z.2).integrable (by norm_num)).abs
        (integrable_const _) ((actualOverlap_uniform_bound hN β R hR hNR).mono (fun ω hω => hω z.1 z.2))
      _ = 1 := by simp
  filter_upwards [normalizedState_continuous (p:=p) β R hR,
    actualOverlap_uniform_bound hN β R hR hNR] with ω hcts hb
  have hC : Continuous (fun z : ℝ≥0×ℝ≥0 => actualOverlap (p:=p) β R hR z.1 z.2 ω) := by
    have he (z : ℝ≥0×ℝ≥0) := actualOverlap_eq_normalized_inner (by omega : 0<N) β R hR z.1 z.2 ω
    simp_rw [he]
    exact (hcts.comp continuous_fst).inner (hcts.comp continuous_snd)
  have hf := (hC.sub (overlapMean_continuous hN hp β R hR hNR)).abs
  have he := squareSup_eq_gridSup _ hf T (M:=2) (fun z _ =>
    (abs_sub _ _).trans (by linarith [hb z.1 z.2,hmean z]))
  exact he

theorem overlapCenteredSup_memLp_two (hN : 1 ≤ N) (hp : 0 < p) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2) (T : ℝ≥0) :
    MemLp (overlapCenteredSup N p β R hR T) 2 (AnnealedModelLaw.law N p) := by
  have hh := centeredSup_memLp_two (gridOverlap (p:=p) β R hR T)
    (fun i => actualOverlap_memLp_two hN β R hR hNR _ _)
    ((actualOverlap_uniform_bound hN β R hR hNR).mono (fun ω hω i => hω _ _))
  exact hh.ae_eq (overlapCenteredSup_ae_countable hN hp β R hR hNR T).symm

theorem overlapCenteredSup_bounds (hN : 1 ≤ N) (hp : 0 < p) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2) (T : ℝ≥0) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,0 ≤ overlapCenteredSup N p β R hR T ω ∧
      overlapCenteredSup N p β R hR T ω ≤ 2 := by
  filter_upwards [overlapCenteredSup_ae_countable hN hp β R hR hNR T,
    centeredSup_bounds (gridOverlap (p:=p) β R hR T)
      (fun i => actualOverlap_memLp_two hN β R hR hNR _ _)
      ((actualOverlap_uniform_bound hN β R hR hNR).mono (fun ω hω i => hω _ _))] with ω he hb
  rwa [he]

end SphericalAging.ActualOverlapCompactPathConcentration
