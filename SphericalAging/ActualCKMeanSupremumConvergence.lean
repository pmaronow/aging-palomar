module

public import SphericalAging.ActualCKMeanKernelConvergence
public import SphericalAging.UniformSupremumError

public section

/-! The deterministic supremum errors needed to transfer actual centered
path concentration to the printed CK kernels tend to zero. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.ActualCKMeanSupremumConvergence
open CompactKernelMemoryLimit ActualCompactCKMemoryLimit ActualCKMeanKernelConvergence
  UniformSupremumError
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

@[expose]  def correlationMeanSupError (N p : ℕ) (β : ℝ≥0) (d : CKSpecification.CKData) (T : ℝ≥0) : ℝ :=
  supError (Function.uncurry (modelCorrelation N p β)) (fun z : ℝ≥0×ℝ≥0 => d.C z.1 z.2) (square T)

@[expose]  def gammaMeanSupError (N p : ℕ) (β : ℝ≥0) (d : CKSpecification.CKData) (T : ℝ≥0) : ℝ :=
  supError (Function.uncurry (modelGamma N p β))
    (fun z : ℝ≥0×ℝ≥0 => ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2) (square T)

 theorem square_nonempty (T : ℝ≥0) : (square T).Nonempty := ⟨(0,0),zero_le,zero_le⟩

 theorem actual_correlation_mean_supError_tendsto_zero {p : ℕ} (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    Tendsto (fun n => correlationMeanSupError (dim n) p β d T) atTop (𝓝 0) :=
  uniform_supError_tendsto_zero (square_nonempty T) (actual_ck_means_uniform_limit dim hdim hp β hβ d hd T).1

 theorem actual_gamma_mean_supError_tendsto_zero {p : ℕ} (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    Tendsto (fun n => gammaMeanSupError (dim n) p β d T) atTop (𝓝 0) :=
  uniform_supError_tendsto_zero (square_nonempty T) (actual_ck_means_uniform_limit dim hdim hp β hβ d hd T).2.1

 theorem actual_mean_supError_sq_tendsto_zero {p : ℕ} (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    Tendsto (fun n => (correlationMeanSupError (dim n) p β d T)^2+
      (gammaMeanSupError (dim n) p β d T)^2) atTop (𝓝 0) := by
  simpa only [zero_pow (by norm_num : (2 : ℕ)≠0),zero_add] using
    ((actual_correlation_mean_supError_tendsto_zero dim hdim hp β hβ d hd T).pow 2).add
      ((actual_gamma_mean_supError_tendsto_zero dim hdim hp β hβ d hd T).pow 2)

end SphericalAging.ActualCKMeanSupremumConvergence
