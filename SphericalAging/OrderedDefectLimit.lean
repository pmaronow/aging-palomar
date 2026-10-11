module

public import SphericalAging.PersistentDefectTheorem
public import Mathlib.Topology.Order.MonotoneConvergence

public section

/-! Genuine existence of the outer remote-defect lower-limit limit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalAging.OrderedDefectLimit
open CKSpecification GeneralCenterDeficit StrongBackwardDefect WeightedResponseIdentities
  WeightedSlowRatioTheorem SlowDefectConstants SlowDefectProfile ActualDefectTransport
  PersistentDefectLimits

@[expose] def remoteMassLimit (p : ℕ) (β : ℝ) (d : CKData) (S L : ℝ) : ℝ≥0∞ :=
  liminf (fun t : ℝ => ENNReal.ofReal (∫ u in S..t-max 0 L,positive p β d t u)) atTop

theorem remoteMassLimit_antitone {p : ℕ} {β S : ℝ} {d : CKData}
    (h : CKEquations p β d) (hS : 0≤S) : Antitone (remoteMassLimit p β d S) := by
  intro L₁ L₂ hL
  unfold remoteMassLimit
  exact liminf_le_liminf (by
    filter_upwards [eventually_ge_atTop (S+max 0 L₂)] with t ht
    have hmax : max 0 L₁≤max 0 L₂ := max_le_max_left 0 hL
    have ht0 : 0≤t := by linarith [le_max_left 0 L₂]
    have hc := positive_row_continuous h (t:=t)
    have hI := (hc.mono (Icc_subset_Icc hS (by linarith [le_max_left 0 L₂] : t-max 0 L₂≤t))).intervalIntegrable_of_Icc (μ:=volume) (by linarith : S≤t-max 0 L₂)
    have hJ := (hc.mono (Icc_subset_Icc (by linarith : 0≤t-max 0 L₂)
      (by linarith [le_max_left 0 L₁] : t-max 0 L₁≤t))).intervalIntegrable_of_Icc (μ:=volume) (by linarith : t-max 0 L₂≤t-max 0 L₁)
    have he := intervalIntegral.integral_add_adjacent_intervals hI hJ
    have hn : 0≤∫ u in t-max 0 L₂..t-max 0 L₁,positive p β d t u :=
      intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => le_max_right _ _)
    exact ENNReal.ofReal_le_ofReal (by linarith))

theorem ordered_positive_mass_limit {p : ℕ} {β S : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q) (hS : 0≤S)
    (hE : Tendsto (energy p β d) atTop (𝓝 (PlateauAlgebra.selectedEnergy p β q)))
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (hx0 : 0<slowRatio p q) (hx1 : slowRatio p q<1) :
    ∃ M : ℝ≥0∞,ENNReal.ofReal (limitingMass p q)≤M ∧
      Tendsto (fun L : ℝ => liminf (fun t : ℝ =>
        ENNReal.ofReal (∫ u in S..t-L,positive p β d t u)) atTop) atTop (𝓝 M) := by
  have hlim := tendsto_atTop_iInf (remoteMassLimit_antitone h hS)
  have hh := ENNReal.tendsto_ofReal (mass_tendsto H hx0)
  have hlower : ENNReal.ofReal (limitingMass p q)≤⨅ L : ℝ,remoteMassLimit p β d S L := by
    apply le_of_tendsto_of_tendsto hh hlim
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    simpa only [remoteMassLimit,max_eq_right hL.le] using
      (remote_liminf H hS hL hE hf hx0 hx1).1
  refine ⟨_,hlower,hlim.congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  simp only [remoteMassLimit,max_eq_right hL]

end SphericalAging.OrderedDefectLimit
