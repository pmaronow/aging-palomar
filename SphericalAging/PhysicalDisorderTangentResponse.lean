module

public import SphericalAging.HamiltonianDisorderResponseSolution
public import SphericalAging.LpRadiusDerivative

public section

/-! Actual tensor-disorder stochastic variations of the physical sphere
state are tangent. The claim follows from the proved L² disorder derivative
and true sphere support for every disorder, then continuity gives one
common path event for the genuine forced Jacobian process. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.PhysicalDisorderTangentResponse
open HardSphereDynamics LocalSDE HamiltonianPicardDependence
open HamiltonianDisorderTerminalDerivative HamiltonianDisorderResponseSolution
set_option maxHeartbeats 1600000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

 theorem terminalResponse_tangent (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J δ : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t ≤ T) :
    ∀ᵐ omega ∂P,inner ℝ ((stateClass (NullAugmentation.driver D₀) β R hR J x T t) omega)
      ((stateResponse (NullAugmentation.driver D₀) β R hR J x T t δ) omega)=0 := by
  let D := NullAugmentation.driver D₀
  let c : ℝ → FiniteModel.Disorder N p := fun r => J+r • δ
  have hc0 : c 0=J := by simp [c]
  have hc : HasDerivAt c δ 0 := by
    convert (hasDerivAt_const (0 : ℝ) J).add ((hasDerivAt_id (0 : ℝ)).smul_const δ) using 1 <;> first | rfl | simp
  have hstate : HasFDerivAt (fun K : FiniteModel.Disorder N p => stateClass D β R hR K x T t)
      (stateResponse D β R hR J x T t) (c 0) := by
    rw [hc0]
    exact stateClass_hasFDerivAt_disorder D₀ β R hR J x T t
  have hcomp := hstate.comp_hasDerivAt (0 : ℝ) hc
  have hf : HasDerivAt (fun r : ℝ => stateClass D β R hR (c r) x T t)
      (stateResponse D β R hR J x T t δ) 0 := by
    convert hcomp using 1 <;> rfl
  have hr : ∀ᶠ r : ℝ in 𝓝 0,∀ᵐ omega ∂P,‖stateClass D β R hR (c r) x T t omega‖^2=(N : ℝ) :=
    .of_forall (fun r => (stateClass_onSphere hN D₀ β R hR hNR (c r) x hx T t ht).mono
      (fun omega hs => (onSphere_iff_norm_sq _).mp hs))
  simpa only [hc0] using LpRadiusDerivative.tangent_of_constant_radius hf hr

/-- The actual continuous forced Jacobian process has zero radial
component simultaneously throughout its genuine solution horizon. -/
 theorem process_tangent (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J δ : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    ∀ᵐ omega ∂P,∀ t,t ≤ T → inner ℝ
      (baseProcess (NullAugmentation.driver D₀) β R hR J x T t omega)
      (process (NullAugmentation.driver D₀) β R hR J δ x T t omega)=0 := by
  let D := NullAugmentation.driver D₀
  let X := baseProcess D β R hR J x T
  let Y := process D β R hR J δ x T
  have hpoint (t : ℝ≥0) (ht : t ≤ T) : ∀ᵐ omega ∂P,inner ℝ (X t omega) (Y t omega)=0 := by
    filter_upwards [terminalResponse_tangent hN D₀ β R hR hNR J δ x hx T t ht,
      stateClass_ae D β R hR J x T t,terminalResponse_ae D β R hR J δ x T t] with omega htan hX hY
    rwa [hX,hY] at htan
  have hgrid : ∀ᵐ omega ∂P,∀ n k : ℕ,AdaptedContinuous.gridTime n k ≤ T →
      inner ℝ (X (AdaptedContinuous.gridTime n k) omega) (Y (AdaptedContinuous.gridTime n k) omega)=0 :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun k => by
      by_cases ht : AdaptedContinuous.gridTime n k ≤ T
      · exact (hpoint _ ht).mono (fun omega h _ => h)
      · exact .of_forall (fun omega h => False.elim (ht h))))
  have hXc := GlobalSDE.horizonProcess_continuous D
    (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩) (noise_family_lipschitz N R hR) x T
  have hYc := (process_strongSolution D β R hR J δ x T).2.1
  filter_upwards [hgrid,hXc,hYc] with omega hgrid hXc hYc
  intro t ht
  have hcts : Continuous (fun s => inner ℝ (X s omega) (Y s omega)) := hXc.inner hYc
  have hlim := hcts.continuousAt.tendsto.comp (AdaptedContinuous.tendsto_pastGrid t)
  have he : (fun n => inner ℝ (X (AdaptedContinuous.pastGrid t n) omega) (Y (AdaptedContinuous.pastGrid t n) omega)) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    exact hgrid n _ ((AdaptedContinuous.pastGrid_le t n).trans ht)
  simp only [Function.comp_def] at hlim
  rw [he] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds
end SphericalAging.PhysicalDisorderTangentResponse
