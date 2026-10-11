module

public import SphericalAging.ActualForkCoefficientField

public section

/-! Actual finite-fork mean energy under its complete original model
law, expressed by the genuine Gaussian and causal response kernels with
the independent sphere initial law fully averaged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.PhysicalForkAveragedEnergyDuhamel
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics PhysicalForkDrivers PhysicalForkMeanEnergyDuhamel PhysicalForkEnergySections
  FiniteForkTerminalEnergyStein ForkCrossCoefficientDuhamel WienerForkTransfer
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p K : ℕ}

@[expose] def sphereMeanKernel (hN : 0<N) (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (J : Disorder N p) (x : State N) (I : TensorIndex N p) (s : ℝ≥0) : ℝ := by
  classical
  exact if hx : OnSphere x then
    crossKernelPairing (Nat.ne_of_gt hN) (driver (N:=N) (K:=K) trunk b) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N)
      J x hx t (terminalMean (filtration (N:=N) (K:=K) trunk) (driver (N:=N) (K:=K) trunk)
        β (N+1) (AnnealedHamiltonianEnergyStein.modelRadius_pos N) J x t t) I s else 0

theorem actual_fork_mean_energy_duhamel (hN : 0<N) (hp : 0<p) (hK : 0<K)
    (β : ℝ≥0) (t trunk : ℝ≥0) :
    (∫q,Hamiltonian N p q.1.1.1 (mean (PhysicalForkConstruction.branch β t trunk) q)
      ∂forkLaw N p K)=
      ∫x : State N,∑I : TensorIndex N p,∫J,(K:ℝ)⁻¹*∑b : Fin K,∫s,
        sphereMeanKernel hN β t trunk b J x I s ∂finiteTimeMeasure t
          ∂disorderLaw N p ∂SphereInitialLaw.sphereLaw N := by
  rw [actual_fork_energy_sections hK β t trunk]
  apply integral_congr_ae
  filter_upwards [SphereInitialLaw.sphereLaw_support hN] with x hx
  have hxs : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
  simpa only [sphereMeanKernel,dif_pos hxs] using
    actual_physical_mean_energy_duhamel hN hp hK β x hxs t trunk

end SphericalAging.PhysicalForkAveragedEnergyDuhamel
