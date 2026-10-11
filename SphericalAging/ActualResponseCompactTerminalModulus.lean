module

public import SphericalAging.ActualResponseTerminalTimeModulus
public import SphericalAging.ResponseIncrementCompactCeiling

public section

/-! A single terminal-time modulus controls the literal actual response
in every dimension on a compact causal time triangle. -/
noncomputable section
open Set Filter Topology
open scoped NNReal
namespace SphericalAging.ActualResponseCompactTerminalModulus
open ActualResponseJointKernel ActualResponseTerminalTimeModulus
open ResponseIncrementGaussianCeiling ResponseIncrementCompactCeiling
variable {N p : ℕ}

theorem responseMeanPair_terminal_compact_ordered (hN : 3 ≤ N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2)
    (T s H K : ℝ≥0) (hsH : s ≤ H) (hHK : H ≤ K) (hKT : K ≤ T) :
    |responseMeanPair (N:=N) (p:=p) β R hR K s -
      responseMeanPair (N:=N) (p:=p) β R hR H s| ≤
        compactTerminalModulus p β T (K-H) := by
  have hH : s+(H-s)=H := add_tsub_cancel_of_le hsH
  have hK : s+((H-s)+(K-H))=K := by
    rw [←add_assoc,hH,add_tsub_cancel_of_le hHK]
  have hlag : (H-s)+(K-H) ≤ T := by
    calc
      _ ≤ s+((H-s)+(K-H)) := le_add_left le_rfl
      _ = K := hK
      _ ≤ T := hKT
  have hh := responseMeanPair_terminal_modulus hN hp β R hR hNR s (H-s) (K-H)
  rw [hK,hH] at hh
  exact hh.trans (Real.sqrt_le_sqrt (annealedIncrementCeiling_mono p β hlag le_rfl))

theorem responseMeanPair_terminal_compact (hN : 3 ≤ N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2)
    (T s H K : ℝ≥0) (hsH : s ≤ H) (hsK : s ≤ K) (hHT : H ≤ T) (hKT : K ≤ T) :
    |responseMeanPair (N:=N) (p:=p) β R hR K s -
      responseMeanPair (N:=N) (p:=p) β R hR H s| ≤
        compactTerminalModulus p β T (max H K-min H K) := by
  rcases le_total H K with hHK|hKH
  · simpa only [max_eq_right hHK,min_eq_left hHK] using
      responseMeanPair_terminal_compact_ordered hN hp β R hR hNR T s H K hsH hHK hKT
  · simpa only [max_eq_left hKH,min_eq_right hKH,abs_sub_comm] using
      responseMeanPair_terminal_compact_ordered hN hp β R hR hNR T s K H hsK hKH hHT

end SphericalAging.ActualResponseCompactTerminalModulus
