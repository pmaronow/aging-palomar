module

public import SphericalAging.CanonicalDisorderDuhamel

public section

/-! Actual matrix-times-gradient representatives of the proved canonical
ordered-disorder Duhamel kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.CanonicalDisorderDuhamelMatrix
open HardSphereDynamics LocalSDE PredictableLinearCoefficient VariationalCoefficients
open HamiltonianPhysicalDuhamel PhysicalCausalImpulseResponse HamiltonianPredictableForcing
open HamiltonianPicardDependence CanonicalDisorderDuhamel
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
variable (hN : N≠0) (D₀ : BrownianDriver N P F) (β : ℝ)
  (J δ : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
  (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x) (T : ℝ≥0)

/-- Actual canonical projected terminal response matrix on the remaining window. -/
@[expose] def responseMatrix (s : ℝ≥0) : State N →L[ℝ] Lp (State N) 2 P :=
  let D := NullAugmentation.driver D₀
  let hb := drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩
  let hs := noise_family_lipschitz N R hR
  let X := HamiltonianJointProcess.globalProcess D β R hR (J,x)
  TwoTimeResponseMatrix.terminalResponse hN D X
    (GlobalSDE.process_stronglyAdapted D hb hs x)
    (HamiltonianJointProcess.globalProcess_continuous D β R hR (J,x)) β J R hR hb hs s (T-s)
    ((CanonicalSphereProcess.globalProcess_onSphere hN D₀ β R hR hNR (J,x) hx).mono (fun _ h => h s)) (T-s)

/-- Literal actual matrix-times-gradient representative, with its
waiting-state projection inside the physical response matrix. -/
theorem kernel_ae_sampleMatrix (s : ℝ≥0) :
    kernel hN D₀ β J δ R hR hNR x hx T s=ᵐ[P]
      (fun omega => β • ResponseMatrixEnergyContraction.sampleMatrix
        (responseMatrix hN D₀ β J R hR hNR x hx T s) omega
        (hamiltonianGradient δ (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR (J,x) s omega))) := by
  unfold kernel responseMatrix
  have hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[NullAugmentation.augment F P 0] A := by
    intro A hA hp
    exact NullAugmentation.augment_null_known_zero F hA hp
  exact disorderKernel_ae_sampleMatrix hN (NullAugmentation.driver D₀)
    (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR (J,x))
    (GlobalSDE.process_stronglyAdapted (NullAugmentation.driver D₀)
      (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩) (noise_family_lipschitz N R hR) x)
    (HamiltonianJointProcess.globalProcess_continuous (NullAugmentation.driver D₀) β R hR (J,x))
    β J δ R hR (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩) (noise_family_lipschitz N R hR)
    (CanonicalSphereProcess.globalProcess_onSphere hN D₀ β R hR hNR (J,x) hx) hnull T s

/-- Basis disorder kernels contain the actual ordered coefficient gradient. -/
theorem kernel_basis_ae_sampleMatrix (I : FiniteModel.TensorIndex N p) (s : ℝ≥0) :
    kernel hN D₀ β J (HamiltonianCoefficientBounds.basisDisorder I) R hR hNR x hx T s=ᵐ[P]
      (fun omega => β • ResponseMatrixEnergyContraction.sampleMatrix
        (responseMatrix hN D₀ β J R hR hNR x hx T s) omega
        (gradient (GaussianIntegrationByParts.hamiltonianCoefficient I)
          (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR (J,x) s omega))) := by
  have he := kernel_ae_sampleMatrix hN D₀ β J (HamiltonianCoefficientBounds.basisDisorder I) R hR hNR x hx T s
  filter_upwards [he] with omega he
  have hg : hamiltonianGradient (HamiltonianCoefficientBounds.basisDisorder I)
      (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR (J,x) s omega)=
      gradient (GaussianIntegrationByParts.hamiltonianCoefficient I)
        (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR (J,x) s omega) := by
    change gradient (FiniteModel.Hamiltonian N p (HamiltonianCoefficientBounds.basisDisorder I)) _=_
    rw [← HamiltonianCoefficientBounds.coefficient_eq_basisHamiltonian I]
  exact he.trans (congrArg (fun v : State N => β • ResponseMatrixEnergyContraction.sampleMatrix
    (responseMatrix hN D₀ β J R hR hNR x hx T s) omega v) hg)

end SphericalAging.CanonicalDisorderDuhamelMatrix
