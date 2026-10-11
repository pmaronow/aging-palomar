module

public import SphericalAging.ResponseIncrementCeilingContinuity

public section

/-! Compact-horizon, dimension-independent response moduli. -/
noncomputable section
open Filter Topology
open scoped NNReal
namespace SphericalAging.ResponseIncrementCompactCeiling
open ResponseIncrementGaussianCeiling ResponseIncrementCeilingContinuity GaussianLandscapeMoments

theorem landscapeSlope_nonneg (p : ℕ) (β : ℝ≥0) : 0 ≤ landscapeSlope p β := by
  unfold landscapeSlope
  positivity

theorem incrementPrefactor_nonneg (p : ℕ) (β δ : ℝ≥0) : 0 ≤ incrementPrefactor p β δ := by
  unfold incrementPrefactor
  positivity

theorem incrementPrefactor_mono (p : ℕ) (β : ℝ≥0) {δ ε : ℝ≥0} (h : δ ≤ ε) :
    incrementPrefactor p β δ ≤ incrementPrefactor p β ε := by
  have he : (δ:ℝ) ≤ (ε:ℝ) := h
  have hp := pow_le_pow_left₀ δ.coe_nonneg he 2
  unfold incrementPrefactor
  nlinarith [sq_nonneg (1 + landscapeSlope p β)]

theorem momentCeiling_mono_nonneg (p : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    momentCeiling p a ≤ momentCeiling p b := by
  unfold momentCeiling
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply Real.exp_le_exp.mpr
  nlinarith

theorem annealedIncrementCeiling_mono (p : ℕ) (β : ℝ≥0) {H T δ ε : ℝ≥0}
    (hH : H ≤ T) (hδ : δ ≤ ε) :
    annealedIncrementCeiling p β H δ ≤ annealedIncrementCeiling p β T ε := by
  have hα := landscapeSlope_nonneg p β
  have hHr : (H:ℝ) ≤ (T:ℝ) := hH
  have he : Real.exp (11*(H:ℝ)) ≤ Real.exp (11*(T:ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hm : momentCeiling p (2*landscapeSlope p β*(H:ℝ)+2) ≤
      momentCeiling p (2*landscapeSlope p β*(T:ℝ)+2) :=
    momentCeiling_mono_nonneg p (by positivity) (by nlinarith)
  unfold annealedIncrementCeiling
  apply mul_le_mul
  · exact mul_le_mul (incrementPrefactor_mono p β hδ) he
      (Real.exp_nonneg _) (incrementPrefactor_nonneg p β ε)
  · exact hm
  · unfold momentCeiling
    positivity
  · exact mul_nonneg (incrementPrefactor_nonneg p β ε) (Real.exp_nonneg _)

@[expose] def compactTerminalModulus (p : ℕ) (β T δ : ℝ≥0) : ℝ :=
  Real.sqrt (annealedIncrementCeiling p β T δ)

theorem compactTerminalModulus_mono (p : ℕ) (β T : ℝ≥0) :
    Monotone (compactTerminalModulus p β T) := by
  intro δ ε h
  exact Real.sqrt_le_sqrt (annealedIncrementCeiling_mono p β le_rfl h)

theorem compactTerminalModulus_continuous (p : ℕ) (β T : ℝ≥0) :
    Continuous (compactTerminalModulus p β T) := by
  exact (terminalModulus_joint_continuous p β).comp (continuous_const.prodMk continuous_id)

theorem compactTerminalModulus_zero (p : ℕ) (β T : ℝ≥0) :
    compactTerminalModulus p β T 0 = 0 := by
  simp [compactTerminalModulus,annealedIncrementCeiling_zero]

theorem compactTerminalModulus_tendsto_zero (p : ℕ) (β T : ℝ≥0) :
    Tendsto (compactTerminalModulus p β T) (𝓝 0) (𝓝 0) := by
  simpa only [compactTerminalModulus_zero] using (compactTerminalModulus_continuous p β T).tendsto 0

end SphericalAging.ResponseIncrementCompactCeiling
