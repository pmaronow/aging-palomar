module

public import SphericalAging.ResponseIncrementGaussianCeiling

public section

/-! Actual uniform response increment ceilings give a continuous
vanishing modulus in elapsed time. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.ResponseIncrementCeilingContinuity
open ResponseIncrementGaussianCeiling GaussianLandscapeMoments

theorem annealedIncrementCeiling_nonneg (p : ℕ) (β H δ : ℝ≥0) :
    0≤annealedIncrementCeiling p β H δ := by
  unfold annealedIncrementCeiling incrementPrefactor momentCeiling
  positivity

theorem annealedIncrementCeiling_joint_continuous (p : ℕ) (β : ℝ≥0) :
    Continuous (fun z : ℝ≥0×ℝ≥0 => annealedIncrementCeiling p β z.1 z.2) := by
  unfold annealedIncrementCeiling incrementPrefactor momentCeiling
  fun_prop

theorem annealedIncrementCeiling_zero (p : ℕ) (β H : ℝ≥0) :
    annealedIncrementCeiling p β H 0=0 := by
  simp [annealedIncrementCeiling,incrementPrefactor]

theorem terminalModulus_joint_continuous (p : ℕ) (β : ℝ≥0) :
    Continuous (fun z : ℝ≥0×ℝ≥0 => Real.sqrt (annealedIncrementCeiling p β z.1 z.2)) :=
  Real.continuous_sqrt.comp (annealedIncrementCeiling_joint_continuous p β)

theorem terminalModulus_tendsto_zero (p : ℕ) (β H : ℝ≥0) :
    Tendsto (fun δ : ℝ≥0 => Real.sqrt (annealedIncrementCeiling p β (H+δ) δ))
      (𝓝 0) (𝓝 0) := by
  have hh := (terminalModulus_joint_continuous p β).comp
    (((continuous_const (y:=H)).add continuous_id).prodMk continuous_id)
  simpa only [Function.comp_def,Pi.add_apply,id_eq,add_zero,annealedIncrementCeiling_zero,
    Real.sqrt_zero] using hh.tendsto 0

end SphericalAging.ResponseIncrementCeilingContinuity
