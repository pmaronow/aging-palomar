module

public import SphericalAging.AdaptiveTensorDisclosureSource
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

/-! Literal rank and residual-dimension estimates of arbitrary finite
adaptive spans, and the exact normalization defect used in source10.7. -/
noncomputable section
namespace SphericalAging.AdaptiveDisclosureDimension
open FiniteModel AdaptiveGradientDisclosure AdaptiveTensorDisclosureSource

 theorem rank_succ_le {N : ℕ} (W : Submodule ℝ (Vector N)) (u : Vector N) :
    Module.finrank ℝ (W⊔Submodule.span ℝ {u} : Submodule ℝ (Vector N))≤Module.finrank ℝ W+1 := by
  classical
  by_cases hu : u∈W
  · rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hu)]
    omega
  · rw [Submodule.finrank_sup_span_singleton hu]

 theorem source_rank_le {N p k0 : ℕ} {S : Type} (W0 : S→Submodule ℝ (Vector N))
    (u : ℕ→S×TensorSpace N p→Vector N) (hW0 : ∀s,Module.finrank ℝ (W0 s)≤k0)
    (j : ℕ) (z : S×TensorSpace N p) : Module.finrank ℝ (Space W0 u j z)≤k0+j := by
  induction j with
  | zero => exact hW0 z.1
  | succ j ih => exact (rank_succ_le (Space W0 u j z) (u j z)).trans (by omega)

 theorem source_residual_dimension {N p k0 : ℕ} {S : Type} (W0 : S→Submodule ℝ (Vector N))
    (u : ℕ→S×TensorSpace N p→Vector N) (hW0 : ∀s,Module.finrank ℝ (W0 s)≤k0)
    (j : ℕ) (z : S×TensorSpace N p) :
    N-(k0+j)≤Module.finrank ℝ (Space W0 u j z)ᗮ ∧
      Module.finrank ℝ (Space W0 u j z)ᗮ≤N := by
  have hh := (Space W0 u j z).finrank_add_finrank_orthogonal
  have hr := source_rank_le W0 u hW0 j z
  have hN : Module.finrank ℝ (Vector N)=N := by simp
  rw [hN] at hh
  omega

 theorem sqrt_ratio_defect {N n k : ℕ} (hN : 0<N) (hn : n≤N) (hk : N≤n+k) :
    0≤1-Real.sqrt ((n:ℝ)/(N:ℝ)) ∧ 1-Real.sqrt ((n:ℝ)/(N:ℝ))≤(k:ℝ)/(N:ℝ) := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hqr : 0≤(n:ℝ)/(N:ℝ) := by positivity
  have hq1 : (n:ℝ)/(N:ℝ)≤1 := (div_le_one hNr).mpr (Nat.cast_le.mpr hn)
  have hs1 : Real.sqrt ((n:ℝ)/(N:ℝ))≤1 := (Real.sqrt_le_one).mpr hq1
  have hs0 := Real.sqrt_nonneg ((n:ℝ)/(N:ℝ))
  have hsq := Real.sq_sqrt hqr
  have hqs : (n:ℝ)/(N:ℝ)≤Real.sqrt ((n:ℝ)/(N:ℝ)) := by nlinarith
  constructor
  · linarith
  · have hkr : (N:ℝ)≤(n:ℝ)+(k:ℝ) := by exact_mod_cast hk
    have hh : 1-(n:ℝ)/(N:ℝ)≤(k:ℝ)/(N:ℝ) := by
      apply (le_div_iff₀ hNr).mpr
      have he : (1-(n:ℝ)/(N:ℝ))*(N:ℝ)=(N:ℝ)-(n:ℝ) := by field_simp
      rw [he]
      linarith
    exact (sub_le_sub_left hqs 1).trans hh

end SphericalAging.AdaptiveDisclosureDimension
