module

public import SphericalAging.ActualResponsePrimitiveLimit

public section

/-! Dimension-uniform deterministic envelopes for the actual joint-time
response, from the full Gaussian landscape exponential moment. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualResponseCompactEnvelope
open FiniteModel ActualResponsePrimitiveInterchange ActualResponsePrimitiveLimit
  GaussianLandscape GaussianLandscapeMoments
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

lemma responseEnvelope_eq_disorder_integral (β : ℝ≥0) (t : ℝ≥0) :
    responseEnvelope (N := N) (p := p) β t=
      ∫ J : Disorder N p,Real.exp (((β : ℝ)*(p : ℝ)^2*(t : ℝ))*landscapeNorm N p J)
        ∂disorderLaw N p := by
  unfold responseEnvelope AnnealedModelLaw.law AnnealedModelLaw.parameterLaw
  have hfn : (fun q : (Disorder N p×HardSphereDynamics.State N)×VectorBrownian.Space N =>
      Real.exp (((β : ℝ)*(p : ℝ)^2*landscapeNorm N p q.1.1)*(t : ℝ)))=
      fun q => Real.exp (((β : ℝ)*(p : ℝ)^2*(t : ℝ))*landscapeNorm N p q.1.1) := by
    funext q
    congr 1
    ring
  rw [hfn]
  rw [integral_fun_fst (μ := (disorderLaw N p).prod (SphereInitialLaw.sphereLaw N))
    (ν := VectorBrownian.law N) (fun q : Disorder N p×HardSphereDynamics.State N =>
      Real.exp (((β : ℝ)*(p : ℝ)^2*(t : ℝ))*landscapeNorm N p q.1)),
    integral_fun_fst (μ := disorderLaw N p) (ν := SphereInitialLaw.sphereLaw N)
      (fun J : Disorder N p => Real.exp (((β : ℝ)*(p : ℝ)^2*(t : ℝ))*landscapeNorm N p J))]
  simp only [probReal_univ,one_smul]

/-- The literal actual response envelope is bounded independently of N. -/
theorem responseEnvelope_le_momentCeiling (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0) (t : ℝ≥0) :
    responseEnvelope (N := N) (p := p) β t≤
      momentCeiling p ((β : ℝ)*(p : ℝ)^2*(t : ℝ)) := by
  rw [responseEnvelope_eq_disorder_integral]
  exact (uniform_exponential_moment (by omega : 1≤N) (by omega : 0<p) _).2

theorem responseEnvelope_mono (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    {t T : ℝ≥0} (ht : t≤T) :
    responseEnvelope (N := N) (p := p) β t≤responseEnvelope (N := N) (p := p) β T := by
  apply integral_mono_ae (response_envelope_integrable hN hp β t)
    (response_envelope_integrable hN hp β T)
  exact .of_forall (fun q => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (show (t : ℝ)≤T from ht) (by
      have := landscapeNorm_nonnegative N p q.1.1
      positivity)))

/-- Uniform N-independent response bound on compact terminal-time horizons. -/
theorem modelResponse_abs_le_compact (hN : 3≤N) (hp : 2≤p) (β T : ℝ≥0)
    (t s : ℝ≥0) (ht : t≤T) :
    |modelResponse (N := N) (p := p) β t s|≤
      momentCeiling p ((β : ℝ)*(p : ℝ)^2*(T : ℝ)) :=
  (modelResponse_abs_le_envelope hN hp β t s).trans
    ((responseEnvelope_mono hN hp β ht).trans (responseEnvelope_le_momentCeiling hN hp β T))

end SphericalAging.ActualResponseCompactEnvelope
