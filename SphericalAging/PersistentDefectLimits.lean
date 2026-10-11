module

public import SphericalAging.ActualDefectTransport
public import SphericalAging.SlowDefectProfile

public section

/-! Literal lower limits and physical rate bounds for the actual positive CK defect.
Lower limits use extended nonnegative reals, so an infinite positive mass is
treated correctly and does not require a spurious boundedness assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.PersistentDefectLimits
open CKSpecification CKPhysicalConsequences WeightedResponseIdentities RecentWeightedResponseLimit
  WeightedSlowRatioTheorem RemoteWeightedBudget GeneralCenterDeficit StrongBackwardDefect
  ResponseTransport SlowDefectConstants SlowDefectProfile ActualDefectTransport

theorem remote_liminf {p : ℕ} {β S L : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q) (hS : 0≤S) (hL : 0<L)
    (hE : Tendsto (energy p β d) atTop (𝓝 (PlateauAlgebra.selectedEnergy p β q)))
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (hx0 : 0<slowRatio p q) (hx1 : slowRatio p q<1) :
    ENNReal.ofReal (mass p q c L)≤
      liminf (fun t : ℝ => ENNReal.ofReal (∫ u in S..t-L,positive p β d t u)) atTop ∧
    ENNReal.ofReal (mass p q c L^2)≤
      liminf (fun t : ℝ => ENNReal.ofReal ((t-L-S)*(∫ u in S..t-L,positive p β d t u^2))) atTop := by
  have hd := distance_tendsto H hS hL.le hE hf (mass_positive H hL.le hx0 hx1).le
  constructor
  · rw [←(ENNReal.tendsto_ofReal hd).liminf_eq]
    exact liminf_le_liminf (by
      filter_upwards [eventually_gt_atTop (S+L)] with t ht
      exact ENNReal.ofReal_le_ofReal (distance_bounds h hS hL ht).1)
  · rw [←(ENNReal.tendsto_ofReal (hd.pow 2)).liminf_eq]
    exact liminf_le_liminf (by
      filter_upwards [eventually_gt_atTop (S+L)] with t ht
      exact ENNReal.ofReal_le_ofReal (distance_bounds h hS hL ht).2)

theorem whole_positive_square_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {a : ℝ → ℝ} (ha : FisherMajorant p β d a) :
    Tendsto (fun t : ℝ => ∫ u in (0:ℝ)..t,positive p β d t u^2) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact intervalIntegral.integral_nonneg_of_forall ht (fun u => sq_nonneg _)
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    have hI := (positive_row_continuous h |>.pow 2).intervalIntegrable_of_Icc (μ:=volume) ht
    have hJ := (((slope_row_continuous h).sub (response_row_continuous h)).pow 2).intervalIntegrable_of_Icc (μ:=volume) ht
    apply intervalIntegral.integral_mono_on ht hI hJ
    intro u _
    change (positive p β d t u)^2≤(backwardDefect p β d t u)^2
    have hh : positive p β d t u≤|backwardDefect p β d t u| :=
      max_le (le_abs_self _) (abs_nonneg _)
    have hs := pow_le_pow_left₀ (show 0≤positive p β d t u from le_max_right _ _) hh 2
    change positive p β d t u^2≤|backwardDefect p β d t u|^2 at hs
    rw [sq_abs] at hs
    exact hs
  · exact squared_backward_defect_tendsto h (physical_bounds_of_equations h) hf ha

theorem distance_square_le_whole_rate {p : ℕ} {β L t : ℝ} {d : CKData}
    (h : CKEquations p β d) (hL : 0<L) (ht : L<t) :
    distance p d 0 L t^2≤t*(∫ u in (0:ℝ)..t,positive p β d t u^2) := by
  have ht0 : 0≤t := hL.le.trans ht.le
  have hc := positive_row_continuous h (t:=t) |>.pow 2
  have hI := (hc.mono (Icc_subset_Icc le_rfl (by linarith : t-L≤t))).intervalIntegrable_of_Icc (μ:=volume) (by linarith : 0≤t-L)
  have hJ := (hc.mono (Icc_subset_Icc (by linarith : 0≤t-L) le_rfl)).intervalIntegrable_of_Icc (μ:=volume) (by linarith : t-L≤t)
  have he := intervalIntegral.integral_add_adjacent_intervals hI hJ
  dsimp only [Pi.pow_apply] at he
  have hIn : 0≤∫ u in (0:ℝ)..t-L,positive p β d t u^2 :=
    intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => sq_nonneg _)
  have hJn : 0≤∫ u in t-L..t,positive p β d t u^2 :=
    intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => sq_nonneg _)
  have hb := (distance_bounds h (S:=0) le_rfl hL (by simpa using ht)).2
  simp only [sub_zero] at hb
  nlinarith

theorem whole_rate_liminf {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q)
    (hE : Tendsto (energy p β d) atTop (𝓝 (PlateauAlgebra.selectedEnergy p β q)))
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (hx0 : 0<slowRatio p q) (hx1 : slowRatio p q<1) :
    ENNReal.ofReal (limitingMass p q^2)≤
      liminf (fun t : ℝ => ENNReal.ofReal (t*(∫ u in (0:ℝ)..t,positive p β d t u^2))) atTop := by
  have hfix L (hL : 0<L) : ENNReal.ofReal (mass p q c L^2)≤
      liminf (fun t : ℝ => ENNReal.ofReal (t*(∫ u in (0:ℝ)..t,positive p β d t u^2))) atTop := by
    have hd := distance_tendsto H le_rfl hL.le hE hf (mass_positive H hL.le hx0 hx1).le
    rw [←(ENNReal.tendsto_ofReal (hd.pow 2)).liminf_eq]
    exact liminf_le_liminf (by
      filter_upwards [eventually_gt_atTop L] with t ht
      exact ENNReal.ofReal_le_ofReal (distance_square_le_whole_rate h hL ht))
  exact le_of_tendsto (ENNReal.tendsto_ofReal ((mass_tendsto H hx0).pow 2)) (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    exact hfix L hL)

end SphericalAging.PersistentDefectLimits
