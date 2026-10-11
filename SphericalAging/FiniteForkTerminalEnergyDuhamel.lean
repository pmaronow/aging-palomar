module

public import SphericalAging.FiniteForkTerminalEnergyStein
public import SphericalAging.ForkCrossCoefficientDuhamel

public section

/-! Exact whole-history finite-fork energy identity before subtracting
the single-branch energy. Every terminal mean, tensor derivative and
branch response kernel comes from the constructed Hamiltonian diffusion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.FiniteForkTerminalEnergyDuhamel
open MeasureTheory ProbabilityTheory StochasticCalculus Filter Set FiniteModel
  HardSphereDynamics HamiltonianDisorderTerminalDerivative HamiltonianCoefficientBounds
  GaussianIntegrationByParts GaussianObservableDerivative FiniteForkTerminalEnergyStein
  ForkCrossCoefficientDuhamel
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
open scoped NNReal ENNReal BigOperators InnerProductSpace Topology
variable {N p K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem coefficient_meanResponse_pairing_duhamel (hN : 0<N) (hK : 0<K)
    (F : Fin K→Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (D : ∀b,BrownianDriver N P (F b)) (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (x : State N) (hx : OnSphere x)
    (T : ℝ≥0) (I : TensorIndex N p) :
    (∫ω,⟪gradient (hamiltonianCoefficient I) (terminalMean F D β R hR J x T T ω),
      meanResponse F D β R hR J x T T (Pi.single I 1) ω⟫_ℝ ∂P)=
      (K:ℝ)⁻¹*∑b,∫s,crossKernelPairing (Nat.ne_of_gt hN) (D b) β R hR hNR J x hx T
        (terminalMean F D β R hR J x T T) I s ∂finiteTimeMeasure T := by
  let M := terminalMean F D β R hR J x T T
  have hM := terminalMean_ball hN hK F D β R hR hNR J x hx T T le_rfl
  let G := (ball_gradient_memLp hN I M hM).toLp (fun ω => gradient (hamiltonianCoefficient I) (M ω))
  let L : StateL2 N P→L[ℝ] ℝ := innerSL ℝ G
  have hL (V : StateL2 N P) : L V=∫ω,⟪gradient (hamiltonianCoefficient I) (M ω),V ω⟫_ℝ ∂P := by
    change ⟪G,V⟫_ℝ=_
    rw [L2.inner_def]
    exact integral_congr_ae ((ball_gradient_memLp hN I M hM).coeFn_toLp.mono fun ω hω =>
      congrArg (fun z : State N => ⟪z,V ω⟫_ℝ) hω)
  have he : L (meanResponse F D β R hR J x T T (Pi.single I 1))=
      (K:ℝ)⁻¹*∑b,L (stateResponse (NullAugmentation.driver (D b)) β R hR J x T T (Pi.single I 1)) := by
    simp only [meanResponse,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
      map_smul,map_sum,smul_eq_mul]
  rw [←hL,he]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [hL]
  exact (actual_cross_coefficient_duhamel hN (D b) β R hR hNR J x hx T M hM I).2

theorem actual_terminalMean_energy_duhamel (hN : 0<N) (hp : 0<p) (hK : 0<K)
    (F : Fin K→Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (D : ∀b,BrownianDriver N P (F b)) (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    (∫J,∫ω,Hamiltonian N p J (terminalMean F D β R hR J x T T ω) ∂P ∂disorderLaw N p)=
      ∑I : TensorIndex N p,∫J,(K:ℝ)⁻¹*∑b,∫s,
        crossKernelPairing (Nat.ne_of_gt hN) (D b) β R hR hNR J x hx T
          (terminalMean F D β R hR J x T T) I s ∂finiteTimeMeasure T ∂disorderLaw N p := by
  rw [actual_terminalMean_energy_stein hN hp hK F D β R hR hNR x hx T T le_rfl]
  apply Finset.sum_congr rfl
  intro I _
  apply integral_congr_ae
  exact .of_forall (fun J => coefficient_meanResponse_pairing_duhamel hN hK F D β R hR hNR J x hx T I)

end SphericalAging.FiniteForkTerminalEnergyDuhamel
