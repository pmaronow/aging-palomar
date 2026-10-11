module

public import SphericalAging.ActualResponseWaitingTimeModulus
public import SphericalAging.ResponseIncrementCompactCeiling

public section

/-! A single dimension-independent waiting-time modulus controls the
literal actual response on every compact causal time triangle. -/
noncomputable section
open Set Filter Topology
open scoped NNReal
namespace SphericalAging.ActualResponseCompactWaitingModulus
open ActualResponseJointKernel ActualResponseWaitingTimeModulus
open ResponseIncrementGaussianCeiling ResponseIncrementCompactCeiling ResponseIncrementCeilingContinuity
variable {N p : ℕ}

@[expose] def compactWaitingModulus (p : ℕ) (β T δ : ℝ≥0) : ℝ :=
  Real.sqrt (10*annealedIncrementCeiling p β T δ)

lemma compactWaitingModulus_continuous (p : ℕ) (β T : ℝ≥0) :
    Continuous (compactWaitingModulus p β T) := by
  apply Real.continuous_sqrt.comp
  exact continuous_const.mul ((annealedIncrementCeiling_joint_continuous p β).comp
    (continuous_const.prodMk continuous_id))

lemma compactWaitingModulus_zero (p : ℕ) (β T : ℝ≥0) : compactWaitingModulus p β T 0=0 := by
  simp [compactWaitingModulus,annealedIncrementCeiling_zero]

lemma compactWaitingModulus_tendsto_zero (p : ℕ) (β T : ℝ≥0) :
    Tendsto (compactWaitingModulus p β T) (𝓝 0) (𝓝 0) := by
  simpa only [compactWaitingModulus_zero] using (compactWaitingModulus_continuous p β T).tendsto 0

theorem responseMeanPair_waiting_compact_ordered (hN : 3≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (T H s r : ℝ≥0) (hsr : s≤r) (hrH : r≤H) (hHT : H≤T) :
    |responseMeanPair (N:=N) (p:=p) β R hR H s-
      responseMeanPair (N:=N) (p:=p) β R hR H r|≤compactWaitingModulus p β T (r-s) := by
  have hr : s+(r-s)=r := add_tsub_cancel_of_le hsr
  have hH : s+((r-s)+(H-r))=H := by rw [←add_assoc,hr,add_tsub_cancel_of_le hrH]
  have hlag : (r-s)+(H-r)≤T := by
    calc
      _≤s+((r-s)+(H-r)) := le_add_left le_rfl
      _=H := hH
      _≤T := hHT
  have hh := responseMeanPair_waiting_modulus hN hp β R hR hNR s (r-s) (H-r)
  rw [hH,hr] at hh
  exact hh.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (annealedIncrementCeiling_mono p β hlag le_rfl) (by norm_num)))

theorem responseMeanPair_waiting_compact (hN : 3≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (T H s r : ℝ≥0) (hsH : s≤H) (hrH : r≤H) (hHT : H≤T) :
    |responseMeanPair (N:=N) (p:=p) β R hR H s-
      responseMeanPair (N:=N) (p:=p) β R hR H r|≤
        compactWaitingModulus p β T (max s r-min s r) := by
  rcases le_total s r with hsr|hrs
  · simpa only [max_eq_right hsr,min_eq_left hsr] using
      responseMeanPair_waiting_compact_ordered hN hp β R hR hNR T H s r hsr hrH hHT
  · simpa only [max_eq_left hrs,min_eq_right hrs,abs_sub_comm] using
      responseMeanPair_waiting_compact_ordered hN hp β R hR hNR T H r s hrs hsH hHT

end SphericalAging.ActualResponseCompactWaitingModulus
