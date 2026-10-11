module

public import SphericalAging.TreeExactificationError

public section

/-! Choose the original branching separately from the fixed target
branching in finite tree exactification. All geometric smallness conditions
are obtained from the genuine recursive correction modulus. -/
noncomputable section
namespace SphericalAging.TwoBranchingExactificationParameters
open Filter TreeExactificationError
open scoped Topology

@[expose] def tolerance (K : ℕ) : ℝ := 1 / (K : ℝ)
@[expose] def gramError (δ : ℝ) (K : ℕ) : ℝ := 3 * (1 - δ) / (K : ℝ)

theorem tolerance_pos {K : ℕ} (hK : 0 < K) : 0 < tolerance K := by
  unfold tolerance
  positivity

theorem gramError_eq (δ : ℝ) (K : ℕ) :
    gramError δ K = (1 - δ) * (tolerance K + 2 / (K : ℝ)) := by
  unfold gramError tolerance
  ring

theorem gramError_nonneg {δ : ℝ} (hδ : δ ≤ 1) (K : ℕ) :
    0 ≤ gramError δ K := by
  unfold gramError
  positivity

theorem gramError_tendsto_zero (δ : ℝ) :
    Tendsto (gramError δ) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

theorem gramError_tendsto_within {δ : ℝ} (hδ : δ ≤ 1) :
    Tendsto (gramError δ) atTop (nhdsWithin 0 (Set.Ici 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨gramError_tendsto_zero δ,
    Eventually.of_forall (fun K => gramError_nonneg hδ K)⟩

theorem eventual_exactification_parameters (k D : ℕ) {δ ζ : ℝ}
    (hδ : δ ∈ Set.Ioo 0 1) (hζ : 0 < ζ) :
    ∀ᶠ K : ℕ in atTop,
      SmallConditions k D δ (gramError δ K) ∧
      correctionError k (gramError δ K) D ≤ ζ := by
  have ht := gramError_tendsto_within hδ.2.le
  have hsmall := ht.eventually (eventually_smallConditions k D δ hδ.1)
  have hc : Tendsto (fun K => correctionError k (gramError δ K) D) atTop (𝓝 0) :=
    (correctionError_tendsto_zero k D).comp ht
  have he := hc.eventually (eventually_lt_nhds hζ)
  filter_upwards [hsmall, he] with K hK he
  exact ⟨hK, he.le⟩

theorem exists_exactification_parameters (k D Kmin : ℕ) {δ ζ : ℝ}
    (hk : 0 < k) (hδ : δ ∈ Set.Ioo 0 1) (hζ : 0 < ζ) :
    ∃ K : ℕ, k ≤ K ∧ Kmin ≤ K ∧ 0 < tolerance K ∧
      gramError δ K = (1 - δ) * (tolerance K + 2 / (K : ℝ)) ∧
      SmallConditions k D δ (gramError δ K) ∧
      correctionError k (gramError δ K) D ≤ ζ := by
  have he := eventual_exactification_parameters k D hδ hζ
  have hb : ∀ᶠ K : ℕ in atTop, max k Kmin ≤ K := eventually_ge_atTop _
  obtain ⟨K, hK, hs, hc⟩ := (hb.and he).exists
  have hkK : k ≤ K := (le_max_left _ _).trans hK
  have hmK : Kmin ≤ K := (le_max_right _ _).trans hK
  exact ⟨K, hkK, hmK, tolerance_pos (hk.trans_le hkK),
    gramError_eq δ K, hs, hc⟩

end SphericalAging.TwoBranchingExactificationParameters
