module

public import SphericalAging.CanonicalDisorderDuhamelMatrix
public import SphericalAging.HamiltonianEnergySteinActual

public section

/-! Actual terminal coefficient-gradient / disorder-derivative pairings
are expressed through the genuine canonical two-time Duhamel matrix.
The scalar functional is constructed in L² before commuting it with the
proved Bochner integral; no response representation is a premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.QuenchedCoefficientDuhamel
open HardSphereDynamics FiniteModel HamiltonianPicardDependence
open HamiltonianDisorderTerminalDerivative HamiltonianCoefficientBounds
open CanonicalDisorderDuhamel CanonicalDisorderDuhamelMatrix ResponseMatrixEnergyContraction GaussianIntegrationByParts
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma stateClass_ae_global (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (J : Disorder N p) (x : State N) (T : ℝ≥0) :
    (stateClass (NullAugmentation.driver D₀) β R hR J x T T : Ω → State N)=ᵐ[P]
      HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR (J,x) T := by
  have hg := GlobalSDE.process_eq_horizon (NullAugmentation.driver D₀)
    (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩) (noise_family_lipschitz N R hR) x T
  exact (stateClass_ae (NullAugmentation.driver D₀) β R hR J x T T).trans
    (hg.mono (fun _ h => (h T le_rfl).symm))

lemma terminalGradient_memLp (hN : 0<N) (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) (I : TensorIndex N p) :
    MemLp (fun ω => gradient (hamiltonianCoefficient I)
      ((stateClass (NullAugmentation.driver D₀) β R hR J x T T) ω)) 2 P := by
  have hc : Continuous (gradient (hamiltonianCoefficient I)) := by
    rw [coefficient_eq_basisHamiltonian]
    exact (hamiltonianGradient_contDiff (basisDisorder I)).continuous
  apply MemLp.of_bound (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)) (p : ℝ)
  filter_upwards [stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T T le_rfl] with ω hω
  exact coefficient_gradient_sphere_bound hN I _ ((onSphere_iff_norm_sq _).mp hω)

@[expose] def terminalGradientFunctional (hN : 0<N) (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) (I : TensorIndex N p) :
    Lp (State N) 2 P →L[ℝ] ℝ :=
  innerSL ℝ ((terminalGradient_memLp hN D₀ β R hR hNR J x hx T I).toLp _)

lemma terminalGradientFunctional_apply (hN : 0<N) (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) (I : TensorIndex N p)
    (Y : Lp (State N) 2 P) :
    terminalGradientFunctional hN D₀ β R hR hNR J x hx T I Y=
      ∫ ω,inner ℝ (gradient (hamiltonianCoefficient I)
        ((stateClass (NullAugmentation.driver D₀) β R hR J x T T) ω)) (Y ω) ∂P := by
  change inner ℝ ((terminalGradient_memLp hN D₀ β R hR hNR J x hx T I).toLp _) Y=_
  rw [L2.inner_def]
  exact integral_congr_ae ((terminalGradient_memLp hN D₀ β R hR hNR J x hx T I).coeFn_toLp.mono
    (fun ω hω => congrArg (fun z : State N => inner ℝ z (Y ω)) hω))

@[expose] def coefficientKernelPairing (hN : N≠0) (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) (I : TensorIndex N p) (s : ℝ≥0) : ℝ :=
  β*(∫ ω,inner ℝ
    (gradient (hamiltonianCoefficient I) (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR (J,x) T ω))
    (sampleMatrix (responseMatrix hN D₀ β J R hR hNR x hx T s) ω
      (gradient (hamiltonianCoefficient I) (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR (J,x) s ω))) ∂P)

/-- True ordered terminal derivative pairing equals its actual physical
matrix-times-gradient time integral, with scalar integrability proved. -/
theorem coefficient_pairing_duhamel (hN : 0<N) (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) (I : TensorIndex N p) :
    Integrable (coefficientKernelPairing (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T I) (finiteTimeMeasure T) ∧
      (∫ ω,inner ℝ (gradient (hamiltonianCoefficient I)
        ((stateClass (NullAugmentation.driver D₀) β R hR J x T T) ω))
        ((stateResponse (NullAugmentation.driver D₀) β R hR J x T T (Pi.single I 1)) ω) ∂P)=
      ∫ s,coefficientKernelPairing (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T I s ∂finiteTimeMeasure T := by
  let K := kernel (Nat.ne_of_gt hN) D₀ β J (basisDisorder I) R hR hNR x hx T
  let L := terminalGradientFunctional hN D₀ β R hR hNR J x hx T I
  have hd := terminal_disorder_derivative_duhamel (Nat.ne_of_gt hN) D₀ β J (basisDisorder I) R hR hNR x hx T
  have hLi := L.integrable_comp hd.1
  have he (s : ℝ≥0) : L (K s)=coefficientKernelPairing (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T I s := by
    rw [terminalGradientFunctional_apply]
    have hs := kernel_basis_ae_sampleMatrix (Nat.ne_of_gt hN) D₀ β J R hR hNR x hx T I s
    have hX := stateClass_ae_global D₀ β R hR J x T
    rw [coefficientKernelPairing,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hs,hX] with ω hk hstate
    change inner ℝ _ ((kernel (Nat.ne_of_gt hN) D₀ β J (basisDisorder I) R hR hNR x hx T s) ω)=_
    rw [hk,hstate]
    simp only [real_inner_smul_right]
  have hall : (fun s => L (K s))=coefficientKernelPairing (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T I := funext he
  refine ⟨hLi.congr (.of_forall he),?_⟩
  rw [← terminalGradientFunctional_apply hN D₀ β R hR hNR J x hx T I]
  change L (stateResponse (NullAugmentation.driver D₀) β R hR J x T T (basisDisorder I))=_
  calc
    _ = L (∫ s,K s ∂finiteTimeMeasure T) := congrArg L hd.2.symm
    _ = ∫ s,L (K s) ∂finiteTimeMeasure T := (L.integral_comp_comm hd.1).symm
    _ = _ := integral_congr_ae (.of_forall he)

end SphericalAging.QuenchedCoefficientDuhamel
