module

public import SphericalAging.ActualForwardDensityMeasurability
public import SphericalAging.ActualSphereForwardDensityLaw

public section

/-! Literal normalized forward-density energy is jointly measurable in
disorder and time, and equals the genuine uniform-initial sphere SDE
energy through its proved waiting law. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualForwardEnergyMeasurability
open FiniteModel HardSphereDynamics LocalSDE SphereInitialLaw ActualSphereTransition
open ActualSphereGibbsDensity ActualForwardDensityMeasurability
open ActualSphereUniformInitialLaw ActualSphereForwardDensityLaw
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def forwardEnergy (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p) (t : ℝ) : ℝ :=
  (∫x : State N,forwardDensity β R hR J t x*Hamiltonian N p J x ∂sphereLaw N)/(N : ℝ)

theorem forwardEnergy_joint_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) :
    StronglyMeasurable (fun z : Disorder N p×ℝ => forwardEnergy β R hR z.1 z.2) := by
  have hH : StronglyMeasurable (fun z : (Disorder N p×ℝ)×State N => Hamiltonian N p z.1.1 z.2) :=
    ((SphereGibbsEntropy.Hamiltonian_joint_continuous N p).measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
  have hm : StronglyMeasurable (fun z : (Disorder N p×ℝ)×State N =>
      forwardDensity β R hR z.1.1 z.1.2 z.2*Hamiltonian N p z.1.1 z.2) :=
    (forwardDensity_joint_stronglyMeasurable β R hR).mul hH
  simpa only [forwardEnergy,div_eq_mul_inv] using
    (hm.integral_prod_right' (ν:=sphereLaw N)).mul_const ((N : ℝ)⁻¹)

theorem forwardEnergy_eq_waitingLaw (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (t : ℝ≥0) :
    forwardEnergy β R hR J t=(∫x : State N,Hamiltonian N p J x ∂waitingLaw β R hR J t)/(N : ℝ) := by
  rw [waitingLaw_eq_densityLaw hN hp β R hR hNR J t,
    densityLaw_test_integral hN hp β R hR hNR J t]
  rfl

theorem forwardEnergy_eq_uniform_initial (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (t : ℝ≥0) :
    forwardEnergy β R hR J t=
      (∫z : State N×VectorBrownian.Space N,Hamiltonian N p J
        (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,z.1) t z.2)
        ∂(sphereLaw N).prod (VectorBrownian.law N))/(N : ℝ) := by
  rw [forwardEnergy_eq_waitingLaw hN hp β R hR hNR J t,waitingLaw,
    integral_map (terminal_measurable _ β R hR J t).aemeasurable
      (Hamiltonian_contDiff J).continuous.aestronglyMeasurable]

end SphericalAging.ActualForwardEnergyMeasurability
