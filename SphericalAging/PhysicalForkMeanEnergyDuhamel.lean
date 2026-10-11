module

public import SphericalAging.FiniteForkTerminalEnergyDuhamel
public import SphericalAging.PhysicalForkDrivers
public import SphericalAging.DriverProcessPullback
public import SphericalAging.PhysicalForkConstruction

public section

/-! Gaussian energy integration by parts for the literal physical fork
mean, on its actual common-trunk and independent-future Wiener seed.
The equality with the driver terminal classes is proved by SDE pullback
and uniqueness, rather than assumed as a law or derivative premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.PhysicalForkMeanEnergyDuhamel
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics FiniteForkTerminalEnergyStein FiniteForkTerminalEnergyDuhamel
  ForkCrossCoefficientDuhamel PhysicalForkDrivers
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
open scoped NNReal ENNReal BigOperators InnerProductSpace Topology
variable {N p K : ℕ}

@[expose] def actualMean (β : ℝ) (t trunk : ℝ≥0) (J : Disorder N p) (x : State N)
    (z : PathSeed N K) : State N :=
  WienerForkTransfer.mean (PhysicalForkConstruction.branch β t trunk)
    (((J,x),z.1),z.2)

theorem terminalMean_eq_actualMean (hN : 0<N) (β : ℝ) (x : State N)
    (hx : OnSphere x) (J : Disorder N p) (t trunk : ℝ≥0) :
    (terminalMean (filtration (N:=N) (K:=K) trunk) (driver (N:=N) (K:=K) trunk) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) J x t t :
        PathSeed N K→State N)=ᵐ[pathSeedLaw N K] actualMean β t trunk J x := by
  let X (b : Fin K) := HamiltonianDisorderTerminalDerivative.stateClass
    (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) J x t t
  have hs (b : Fin K) := DriverProcessPullback.stateClass_pullback hN
    (branchPath_measurePreserving trunk b) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N)
      (AnnealedHamiltonianEnergyStein.modelRadius_sq N) J x hx t t le_rfl
  filter_upwards [Lp.coeFn_smul (K:ℝ)⁻¹ (∑b,X b),
    Lp.coeFn_finsetSum Finset.univ X,ae_all_iff.mpr hs] with z h1 h2 h3
  change ((K:ℝ)⁻¹ • ∑b,X b) z=actualMean β t trunk J x z
  rw [h1]
  simp only [Pi.smul_apply,h2,Finset.sum_apply,actualMean,WienerForkTransfer.mean]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact h3 b

theorem actual_physical_mean_energy_duhamel (hN : 0<N) (hp : 0<p) (hK : 0<K)
    (β : ℝ) (x : State N) (hx : OnSphere x) (t trunk : ℝ≥0) :
    (∫J,∫z,Hamiltonian N p J (actualMean β t trunk J x z)
      ∂pathSeedLaw N K ∂disorderLaw N p)=
      ∑I : TensorIndex N p,∫J,(K:ℝ)⁻¹*∑b : Fin K,∫s,
        crossKernelPairing (Nat.ne_of_gt hN) (driver (N:=N) (K:=K) trunk b) β (N+1)
          (AnnealedHamiltonianEnergyStein.modelRadius_pos N)
          (AnnealedHamiltonianEnergyStein.modelRadius_sq N) J x hx t
          (terminalMean (filtration (N:=N) (K:=K) trunk) (driver (N:=N) (K:=K) trunk) β (N+1)
            (AnnealedHamiltonianEnergyStein.modelRadius_pos N) J x t t) I s
          ∂finiteTimeMeasure t ∂disorderLaw N p := by
  calc
    _=∫J,∫z,Hamiltonian N p J (terminalMean (filtration (N:=N) (K:=K) trunk) (driver (N:=N) (K:=K) trunk) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) J x t t z)
          ∂pathSeedLaw N K ∂disorderLaw N p := by
      apply integral_congr_ae
      exact .of_forall fun J => integral_congr_ae
        ((terminalMean_eq_actualMean hN β x hx J t trunk).symm.mono fun z hz =>
          congrArg (Hamiltonian N p J) hz)
    _=_ := actual_terminalMean_energy_duhamel hN hp hK
      (filtration (N:=N) (K:=K) trunk) (driver (N:=N) (K:=K) trunk) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N)
        (AnnealedHamiltonianEnergyStein.modelRadius_sq N) x hx t

end SphericalAging.PhysicalForkMeanEnergyDuhamel
