module

public import SphericalAging.SphereEulerRandomInitialApproximation
public import SphericalAging.SphereEulerSeedSpan
public import SphericalAging.ActualSphereMarkovRestart
public import SphericalAging.AnnealedHamiltonianEnergyStein

public section

/-! Fixed-time finite-query approximation under the literal Gaussian,
surface and Wiener model law. Its error is derived from the genuine SDE. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.SphereEulerModelApproximation
open FiniteModel HardSphereDynamics ActualSphereTransition
open SphereEulerAlgorithm SphereEulerMeshRate SphereEulerPredictable
open SphereEulerGaussianApproximation SphereEulerRandomInitialApproximation
open AnnealedHamiltonianEnergyStein ActualSphereMarkovRestart
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] abbrev Sample (N p : ℕ) := (Disorder N p×State N)×VectorBrownian.Space N

@[expose] def output (β T : ℝ≥0) (M : ℕ) (q : Sample N p) : State N :=
  endpoint (NullAugmentation.driver (VectorBrownian.driver N)) β T M q.1.1 q.1.2 q.2

theorem output_measurable (β T : ℝ≥0) (M : ℕ) : Measurable (output (N:=N) (p:=p) β T M) :=
  euler_joint_measurable (VectorBrownian.driver N) β T M

theorem output_norm_le (β T : ℝ≥0) (M : ℕ) (q : Sample N p) :
    ‖output β T M q‖≤Real.sqrt N := endpoint_norm_le _ _ _ _ _ _ _

theorem actual_model_error_le (hN : 2≤N) (hp : 2≤p) (β T : ℝ≥0)
    {M : ℕ} (hM : M≠0) :
    (∫q,‖modelProcess N p β T q-output β T M q‖^2/(N:ℝ) ∂AnnealedModelLaw.law N p)≤
      annealedBound N p β T M := by
  have hρ : ∀ᵐx ∂SphereInitialLaw.sphereLaw N,OnSphere x :=
    (SphereInitialLaw.sphereLaw_support (by omega : 1≤N)).mono
      (fun x hx => (onSphere_iff_norm_sq x).mpr hx)
  have hh := random_initial_error_le hN hp (VectorBrownian.driver N) β
    (N+1) (modelRadius_pos N) (modelRadius_sq N) T hM (SphereInitialLaw.sphereLaw N) hρ
  have he := annealedGlobal_eq_joint (ρ:=AnnealedModelLaw.parameterLaw N p)
    (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1) (modelRadius_pos N)
      (AnnealedModelLaw.parameter_disorder_memLp N p) T
  change modelProcess N p β T=ᵐ[AnnealedModelLaw.law N p]
    (fun q => jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
      β (N+1) (modelRadius_pos N) q.1 T q.2) at he
  have hIntegral : (∫q,‖modelProcess N p β T q-output β T M q‖^2/(N:ℝ) ∂AnnealedModelLaw.law N p)=
      ∫q,error (VectorBrownian.driver N) β (N+1) (modelRadius_pos N) T M q ∂AnnealedModelLaw.law N p := by
    apply integral_congr_ae
    filter_upwards [he] with q hq
    change ‖modelProcess N p β T q-_‖^2/(N:ℝ)=_
    rw [hq]
    rfl
  rw [hIntegral]
  exact hh

@[expose] def querySpan (β T : ℝ≥0) (M k : ℕ) (q : Sample N p) : Submodule ℝ (State N) :=
  SphereEulerSeedSpan.space β (mesh T M) q.1.1 q.1.2
    (fun j => increment (NullAugmentation.driver (VectorBrownian.driver N)) (mesh T M) j q.2) M k

theorem output_mem_querySpan (β T : ℝ≥0) (M : ℕ) (q : Sample N p) :
    output β T M q∈querySpan β T M M q := SphereEulerSeedSpan.output_mem _ _ _ _ _ _

theorem querySpan_mono (β T : ℝ≥0) (M : ℕ) (q : Sample N p) :
    Monotone (fun k => querySpan β T M k q) := SphereEulerSeedSpan.space_mono _ _ _ _ _ _

theorem initial_querySpan_finrank_le (β T : ℝ≥0) (M : ℕ) (q : Sample N p) :
    Module.finrank ℝ (querySpan β T M 0 q)≤M+1 := SphereEulerSeedSpan.initial_finrank_le _ _ _ _ _ _

theorem terminal_querySpan_finrank_le (β T : ℝ≥0) (M : ℕ) (q : Sample N p) :
    Module.finrank ℝ (querySpan β T M M q)≤2*M+1 := SphereEulerSeedSpan.terminal_finrank_le _ _ _ _ _ _

end SphericalAging.SphereEulerModelApproximation
