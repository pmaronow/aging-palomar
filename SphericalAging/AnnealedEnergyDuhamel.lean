module

public import SphericalAging.QuenchedCoefficientDuhamel
public import SphericalAging.AnnealedHamiltonianEnergyStein

public section

/-! Actual finite-N annealed energy expressed through the genuine
physical two-time ordered response kernel. Gaussian integration by parts
and the real terminal disorder derivative Duhamel formula are composed;
no energy/response identity or derivative is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.AnnealedEnergyDuhamel
open HardSphereDynamics FiniteModel QuenchedCoefficientDuhamel
open AnnealedHamiltonianEnergyStein
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def sphereCoefficientKernel (hN : N≠0) (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (x : State N) (T : ℝ≥0) (I : TensorIndex N p) (s : ℝ≥0) : ℝ := by
  classical
  exact if hx : OnSphere x then coefficientKernelPairing hN D₀ β R hR hNR J x hx T I s else 0

/-- Exact finite-dimensional energy/Duhamel identity for the literal
annealed Hamiltonian diffusion with its independent Gaussian tensor and
normalized sphere initial law. -/
theorem actual_energy_duhamel (hN : 0<N) (hp : 0<p) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (T : ℝ≥0) :
    (∫ q,Hamiltonian N p q.1.1 (process D₀ β R hR T q)
      ∂(AnnealedModelLaw.parameterLaw N p).prod P)=
      ∫ x : State N,∑ I : TensorIndex N p,∫ J : Disorder N p,∫ s,
        sphereCoefficientKernel (Nat.ne_of_gt hN) D₀ β R hR hNR J x T I s
          ∂finiteTimeMeasure T ∂disorderLaw N p ∂SphereInitialLaw.sphereLaw N := by
  rw [actual_energy_stein hN hp D₀ β R hR hNR T T le_rfl]
  apply integral_congr_ae
  filter_upwards [SphereInitialLaw.sphereLaw_support hN] with x hx
  have hs : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
  apply Finset.sum_congr rfl
  intro I _
  apply integral_congr_ae
  exact .of_forall (fun J => by
    have he : sphereCoefficientKernel (Nat.ne_of_gt hN) D₀ β R hR hNR J x T I=
        coefficientKernelPairing (Nat.ne_of_gt hN) D₀ β R hR hNR J x hs T I := by
      funext s
      simp only [sphereCoefficientKernel,dif_pos hs]
    exact (coefficient_pairing_duhamel hN D₀ β R hR hNR J x hs T I).2.trans
      (congrArg (fun f : ℝ≥0 → ℝ => ∫ s,f s ∂finiteTimeMeasure T) he).symm)

/-- Concrete actual model receipt with no supplied Brownian driver,
flow, derivative, moments, measurability or energy/response identity. -/
theorem actual_model_energy_duhamel (hN : 0<N) (hp : 0<p) (β : ℝ) (T : ℝ≥0) :
    (∫ q,Hamiltonian N p q.1.1 (modelProcess N p β T q) ∂AnnealedModelLaw.law N p)=
      ∫ x : State N,∑ I : TensorIndex N p,∫ J : Disorder N p,∫ s,
        sphereCoefficientKernel (Nat.ne_of_gt hN) (VectorBrownian.driver N) β (N+1)
          (modelRadius_pos N) (modelRadius_sq N) J x T I s
            ∂finiteTimeMeasure T ∂disorderLaw N p ∂SphereInitialLaw.sphereLaw N :=
  actual_energy_duhamel hN hp (VectorBrownian.driver N) β (N+1) (modelRadius_pos N) (modelRadius_sq N) T

end SphericalAging.AnnealedEnergyDuhamel
