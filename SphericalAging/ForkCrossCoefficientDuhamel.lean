module

public import SphericalAging.QuenchedCoefficientDuhamel
public import SphericalAging.GaussianBallEnergyStein

public section

/-! Actual cross-coefficient Duhamel pairing. The test gradient may be
evaluated at the literal finite-fork mean, while the response and earlier
gradient belong to one branch. This retains the complete branch history. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.ForkCrossCoefficientDuhamel
open MeasureTheory ProbabilityTheory StochasticCalculus Filter Set FiniteModel
  HardSphereDynamics HamiltonianDisorderTerminalDerivative HamiltonianCoefficientBounds
  CanonicalDisorderDuhamel CanonicalDisorderDuhamelMatrix ResponseMatrixEnergyContraction
  GaussianIntegrationByParts GaussianObservableDerivative
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
open scoped NNReal ENNReal InnerProductSpace Topology
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem ball_gradient_memLp (hN : 0<N) (I : TensorIndex N p) (M : StateL2 N P)
    (hM : ∀ᵐω ∂P,‖M ω‖≤Real.sqrt (N:ℝ)) :
    MemLp (fun ω => gradient (hamiltonianCoefficient I) (M ω)) 2 P := by
  have hg := HamiltonianDerivativeCovariance.coefficient_contDiff I
  have hc : Continuous (gradient (hamiltonianCoefficient I)) :=
    (InnerProductSpace.toDual ℝ (State N)).symm.continuous.comp (hg.continuous_fderiv (by simp))
  exact MemLp.of_bound (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable M)) (p:ℝ)
    (hM.mono fun ω hω => coefficient_gradient_ball_bound hN I _ hω)

@[expose] def crossKernelPairing (hN : N≠0) (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0)
    (M : StateL2 N P) (I : TensorIndex N p) (s : ℝ≥0) : ℝ :=
  β*(∫ω,⟪gradient (hamiltonianCoefficient I) (M ω),
    sampleMatrix (responseMatrix hN D₀ β J R hR hNR x hx T s) ω
      (gradient (hamiltonianCoefficient I)
        (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR (J,x) s ω))⟫_ℝ ∂P)

theorem actual_cross_coefficient_duhamel (hN : 0<N) (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0)
    (M : StateL2 N P) (hM : ∀ᵐω ∂P,‖M ω‖≤Real.sqrt (N:ℝ)) (I : TensorIndex N p) :
    Integrable (crossKernelPairing (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T M I)
      (finiteTimeMeasure T) ∧
    (∫ω,⟪gradient (hamiltonianCoefficient I) (M ω),
      stateResponse (NullAugmentation.driver D₀) β R hR J x T T (Pi.single I 1) ω⟫_ℝ ∂P)=
      ∫s,crossKernelPairing (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T M I s ∂finiteTimeMeasure T := by
  let K := kernel (Nat.ne_of_gt hN) D₀ β J (basisDisorder I) R hR hNR x hx T
  let G := (ball_gradient_memLp hN I M hM).toLp (fun ω => gradient (hamiltonianCoefficient I) (M ω))
  let L : StateL2 N P→L[ℝ] ℝ := innerSL ℝ G
  have hL (V : StateL2 N P) : L V=∫ω,⟪gradient (hamiltonianCoefficient I) (M ω),V ω⟫_ℝ ∂P := by
    change ⟪G,V⟫_ℝ=_
    rw [L2.inner_def]
    exact integral_congr_ae ((ball_gradient_memLp hN I M hM).coeFn_toLp.mono fun ω hω =>
      congrArg (fun z : State N => ⟪z,V ω⟫_ℝ) hω)
  have hd := terminal_disorder_derivative_duhamel (Nat.ne_of_gt hN) D₀ β J
    (basisDisorder I) R hR hNR x hx T
  have hi := L.integrable_comp hd.1
  have he (s : ℝ≥0) : L (K s)=crossKernelPairing (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T M I s := by
    rw [hL,crossKernelPairing,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [kernel_basis_ae_sampleMatrix (Nat.ne_of_gt hN) D₀ β J R hR hNR x hx T I s]
      with ω hω
    change ⟪_,(K s) ω⟫_ℝ=_
    rw [hω]
    simp only [real_inner_smul_right]
  refine ⟨hi.congr (.of_forall he),?_⟩
  rw [←hL]
  change L (stateResponse (NullAugmentation.driver D₀) β R hR J x T T (basisDisorder I))=_
  calc
    _ = L (∫s,K s ∂finiteTimeMeasure T) := congrArg L hd.2.symm
    _ = ∫s,L (K s) ∂finiteTimeMeasure T := (L.integral_comp_comm hd.1).symm
    _ = _ := integral_congr_ae (.of_forall he)

end SphericalAging.ForkCrossCoefficientDuhamel
