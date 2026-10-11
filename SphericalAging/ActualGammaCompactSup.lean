module

public import SphericalAging.ActualNormalizedGamma
public import SphericalAging.UnboundedCountableMeshConcentration
public import SphericalAging.ActualCKPathSupremumMeasurability
public import SphericalAging.DyadicSquareSupremum

public section

/-! The full compact centered Γ supremum is a measurable countable dyadic
supremum, with L² integrability proved from the actual Brownian maximum. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualGammaCompactPathConcentration
open HardSphereDynamics ActualBrownianPrimitiveTimeModulus ActualNormalizedGamma
open ActualCKPathSupremumMeasurability ActualMeanKernelTimeCompactness
open DyadicSquareSupremum CountableCenteredSup UnboundedCountableMeshConcentration
variable {N p : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose] def gammaCenteredSup (N p : ℕ) (β R : ℝ≥0) (hR : 0<(R:ℝ)) (T : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : ℝ :=
  squareSup (fun z : ℝ≥0×ℝ≥0 => |actualGamma β R hR z.1 z.2 ω-
    ∫v,actualGamma β R hR z.1 z.2 v ∂AnnealedModelLaw.law N p|) T

@[expose] def gridGamma (β R : ℝ≥0) (hR : 0<(R:ℝ)) (T : ℝ≥0) (i : GridIndex) :
    AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N→ℝ :=
  actualGamma β R hR (gridPair T i).1 (gridPair T i).2

theorem gammaMean_continuous (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) :
    Continuous (fun z : ℝ≥0×ℝ≥0 => ∫ω,actualGamma (p:=p) β R hR z.1 z.2 ω ∂AnnealedModelLaw.law N p) :=
  (actual_gamma_means_equicontinuous (fun _ : Unit => N) (fun _ => hN) p hp β
    (fun _ => R) (fun _ => hR) (fun _ => hNR)).continuous ()

theorem gammaMean_abs_le_envelope_mean (hN : 1≤N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (T t s : ℝ≥0) (hs : s≤T) :
    |∫ω,actualGamma (p:=p) β R hR t s ω ∂AnnealedModelLaw.law N p|≤
      ∫ω,gammaEnvelope T ω ∂AnnealedModelLaw.law N p := by
  exact abs_integral_le_integral_abs.trans (integral_mono_ae
    ((actualGamma_memLp_two hN β R hR hNR t s).integrable (by norm_num)).abs
    ((gammaEnvelope_memLp_two T).integrable (by norm_num))
    ((actualGamma_uniform_envelope hN β R hR hNR T).mono (fun ω hω => hω t s hs)))

theorem gammaCenteredSup_ae_countable (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (T : ℝ≥0) :
    gammaCenteredSup N p β R hR T =ᵐ[AnnealedModelLaw.law N p]
      centeredSup (gridGamma (p:=p) β R hR T) (AnnealedModelLaw.law N p) := by
  filter_upwards [actual_gamma_paths_continuous (p:=p) β R hR,
    actualGamma_uniform_envelope hN β R hR hNR T] with ω hcts hb
  exact squareSup_eq_gridSup _ (hcts.sub (gammaMean_continuous hN hp β R hR hNR)).abs T
    (M:=gammaEnvelope T ω+(∫z,gammaEnvelope T z ∂AnnealedModelLaw.law N p))
    (fun z hz => (abs_sub _ _).trans (add_le_add (hb z.1 z.2 hz.2)
      (gammaMean_abs_le_envelope_mean hN β R hR hNR T z.1 z.2 hz.2)))

theorem gammaCenteredSup_memLp_two (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (T : ℝ≥0) :
    MemLp (gammaCenteredSup N p β R hR T) 2 (AnnealedModelLaw.law N p) := by
  have hh := centeredSup_memLp_two_of_envelope (gridGamma (p:=p) β R hR T)
    (fun i => actualGamma_memLp_two hN β R hR hNR _ _)
    (gammaEnvelope_memLp_two T) (.of_forall (gammaEnvelope_nonneg T))
    ((actualGamma_uniform_envelope hN β R hR hNR T).mono (fun ω hω i =>
      hω _ _ (gridPair_mem_square T i).2))
  exact hh.ae_eq (gammaCenteredSup_ae_countable hN hp β R hR hNR T).symm

theorem gammaCenteredSup_bounds (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (T : ℝ≥0) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,0≤gammaCenteredSup N p β R hR T ω ∧
      gammaCenteredSup N p β R hR T ω≤gammaEnvelope T ω+
        (∫z,gammaEnvelope T z ∂AnnealedModelLaw.law N p) := by
  filter_upwards [gammaCenteredSup_ae_countable hN hp β R hR hNR T,
    centeredSup_bounds_of_envelope (gridGamma (p:=p) β R hR T)
      (fun i => actualGamma_memLp_two hN β R hR hNR _ _)
      (gammaEnvelope_memLp_two T) (.of_forall (gammaEnvelope_nonneg T))
      ((actualGamma_uniform_envelope hN β R hR hNR T).mono (fun ω hω i =>
        hω _ _ (gridPair_mem_square T i).2))] with ω he hb
  rwa [he]

end SphericalAging.ActualGammaCompactPathConcentration
