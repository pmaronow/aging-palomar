module

public import SphericalAging.HamiltonianTerminalDerivative
public import SphericalAging.LpRadiusDerivative
public import SphericalAging.SphereTangentCurve
public import SphericalAging.CutoffSphere

public section

/-! The true initial-state stochastic derivative maps actual sphere
tangents to sphere tangents. This is proved from sphere curves and
pointwise radius differentiation in L¹, then lifted to a common continuous
path event for the actual strong Jacobian response. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.PhysicalTangentResponse
open HardSphereDynamics LocalSDE VariationalCoefficients HamiltonianTerminalDerivative
set_option maxHeartbeats 1600000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

 theorem native_stateClass_onSphere (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t ≤ T) :
    ∀ᵐ omega ∂P,OnSphere ((stateClass (NullAugmentation.driver D₀) β J R hR x T t) omega) := by
  let D := NullAugmentation.driver D₀
  let hb := (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
  let hs := (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec
  let X := GlobalSDE.horizonProcess D hb hs x T
  have hXa := GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T
  have hXc := GlobalSDE.horizonProcess_continuous D hb hs x T
  obtain ⟨Y,hYa,hYc,hYX⟩ := NullAugmentation.exists_allPath_continuous_modification_augmented F X hXa hXc
  have hYsol := AllPathSDE.IsLocalStrongSolutionOn.path_congr
    (GlobalSDE.horizonProcess_strongSolution D hb hs x T) hYa (.of_forall hYc) hYX
  have hYs := (CutoffSphere.physical_solution_of_cutoff hN D β J R hR hNR x hx Y hYc T
    (fun i j => (hs i j).continuous) hYsol).2
  filter_upwards [stateClass_ae D β J R hR x T t,hYX,hYs] with omega hstate hYX hYs
  rw [hstate]
  change OnSphere (X t omega)
  rw [← hYX t]
  exact hYs t ht

/-- The actual L² terminal derivative has zero radial component almost
surely in every actual initial sphere-tangent direction. -/
 theorem stateResponse_tangent (hN : 0 < N) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x v : State N) (hx : OnSphere x)
    (hv : inner ℝ x v=0) (T t : ℝ≥0) (hT : 0 < T) (ht : t ≤ T) :
    ∀ᵐ omega ∂P,inner ℝ ((stateClass (NullAugmentation.driver D₀) β J R hR x T t) omega)
      ((stateResponse (NullAugmentation.driver D₀) β J R hR x T t v) omega)=0 := by
  let D := NullAugmentation.driver D₀
  let c := SphereTangentCurve.curve x v
  have hc0 : c 0=x := SphereTangentCurve.curve_zero hN x v
  have hc := SphereTangentCurve.curve_hasDerivAt (x := x) (v := v) hN
  have hstate := stateClass_hasFDerivAt_initial D₀ β J R hR x T t hT
  have hstate' : HasFDerivAt (fun y : State N => stateClass D β J R hR y T t)
      (stateResponse D β J R hR x T t) (c 0) := by rw [hc0];exact hstate
  have hcomp := hstate'.comp_hasDerivAt (0 : ℝ) hc
  have hf : HasDerivAt (fun r : ℝ => stateClass D β J R hR (c r) T t)
      (stateResponse D β J R hR x T t v) 0 := by
    convert hcomp using 1 <;> rfl
  have hr : ∀ᶠ r : ℝ in 𝓝 0,∀ᵐ omega ∂P,‖stateClass D β J R hR (c r) T t omega‖^2=(N : ℝ) := by
    apply Filter.Eventually.of_forall
    intro r
    exact (native_stateClass_onSphere (Nat.ne_of_gt hN) D₀ β J R hR hNR (c r)
      (SphereTangentCurve.curve_onSphere hN hx hv r) T t ht).mono
        (fun omega hs => (onSphere_iff_norm_sq _).mp hs)
  simpa only [hc0] using LpRadiusDerivative.tangent_of_constant_radius hf hr

/-- The genuine continuous adapted Jacobian matrix SDE realizes the
sphere-tangent derivative on one common probability-one path event. -/
 theorem exists_tangent_response_solution (hN : 0 < N) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x v : State N) (hx : OnSphere x)
    (hv : inner ℝ x v=0) (T : ℝ≥0) (hT : 0 < T) :
    ∃ Y,
      LinearVariationalSDE.IsStrongSolutionOn
        (StochasticFlowDerivative.driftRows (NullAugmentation.driver D₀) (cutoffDrift_contDiff β J R hR)
          (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
          (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T)
        (StochasticFlowDerivative.noiseRows (NullAugmentation.driver D₀) (cutoffNoise_contDiff R hR)
          (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
          (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T)
        (NullAugmentation.driver D₀) v Y T ∧
      (∀ t,stateResponse (NullAugmentation.driver D₀) β J R hR x T t v =ᵐ[P] Y t) ∧
      (∀ᵐ omega ∂P,∀ t,t ≤ T → inner ℝ
        (GlobalSDE.horizonProcess (NullAugmentation.driver D₀)
          (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
          (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T t omega) (Y t omega)=0) := by
  let D := NullAugmentation.driver D₀
  let hb := (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
  let hs := (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec
  let X := GlobalSDE.horizonProcess D hb hs x T
  obtain ⟨Y,hY,hYterminal⟩ := exists_terminalResponse_solution D β J R hR x v T
  have hpoint (t : ℝ≥0) (ht : t ≤ T) : ∀ᵐ omega ∂P,inner ℝ (X t omega) (Y t omega)=0 := by
    filter_upwards [stateResponse_tangent hN D₀ β J R hR hNR x v hx hv T t hT ht,
      stateClass_ae D β J R hR x T t,hYterminal t] with omega htan hX hY
    rwa [hX,hY] at htan
  have hgrid : ∀ᵐ omega ∂P,∀ n k : ℕ,AdaptedContinuous.gridTime n k ≤ T →
      inner ℝ (X (AdaptedContinuous.gridTime n k) omega) (Y (AdaptedContinuous.gridTime n k) omega)=0 :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun k => by
      by_cases ht : AdaptedContinuous.gridTime n k ≤ T
      · exact (hpoint _ ht).mono (fun omega h _ => h)
      · exact .of_forall (fun omega h => False.elim (ht h))))
  refine ⟨Y,hY,hYterminal,?_⟩
  filter_upwards [hgrid,GlobalSDE.horizonProcess_continuous D hb hs x T,hY.2.1] with omega hgrid hXc hYc
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
end SphericalAging.PhysicalTangentResponse
