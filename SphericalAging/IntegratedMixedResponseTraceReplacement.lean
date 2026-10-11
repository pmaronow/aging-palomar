module

public import SphericalAging.MixedResponseTraceReplacement

public section

/-! Integration of the quantitative two-correlation signed trace
replacement over an arbitrary finite time measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.IntegratedMixedResponseTraceReplacement
open MixedResponseTraceReplacement
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
  {ν : Measure A} [IsFiniteMeasure ν] {P : Measure Ω} [IsProbabilityMeasure P]

theorem integrated_weighted_product_trace_replacement {a c r : A × Ω → ℝ} {b d : A → ℝ}
    {C ε : ℝ} (n m : ℕ) (hε : 0≤ε) (ha : StronglyMeasurable a)
    (hc : StronglyMeasurable c) (hr : StronglyMeasurable r)
    (hb : StronglyMeasurable b) (hd : StronglyMeasurable d)
    (hab : ∀ x,∀ᵐ ω ∂P,|a (x,ω)|≤1) (hcd : ∀ x,∀ᵐ ω ∂P,|c (x,ω)|≤1)
    (hbb : ∀ x,|b x|≤1) (hdd : ∀ x,|d x|≤1)
    (hr4 : ∀ x,MemLp (fun ω => r (x,ω)) 4 P)
    (hC : ∀ x,(∫ ω,|r (x,ω)|^4 ∂P)≤C)
    (hvariance_a : ∀ x,(∫ ω,(a (x,ω)-b x)^2 ∂P)≤ε^2)
    (hvariance_c : ∀ x,(∫ ω,(c (x,ω)-d x)^2 ∂P)≤ε^2) :
    Integrable (fun q => |((a q)^n*(c q)^m-(b q.1)^n*(d q.1)^m)*r q|) (ν.prod P) ∧
      (∫ q,|((a q)^n*(c q)^m-(b q.1)^n*(d q.1)^m)*r q| ∂ν.prod P)≤
        ν.real univ*(((n : ℝ)+(m : ℝ))*ε*Real.sqrt (1+C)) := by
  let B : ℝ := ((n : ℝ)+(m : ℝ))*ε*Real.sqrt (1+C)
  let f : A × Ω → ℝ := fun q => |((a q)^n*(c q)^m-(b q.1)^n*(d q.1)^m)*r q|
  have hf : StronglyMeasurable f := by
    have h := ((((ha.pow n).mul (hc.pow m)).sub ((hb.comp_fst.pow n).mul (hd.comp_fst.pow m))).mul hr).norm
    simpa only [f,Real.norm_eq_abs,Pi.mul_apply,Pi.pow_apply,Pi.sub_apply] using h
  have hx (x : A) : Integrable (fun ω => f (x,ω)) P ∧ (∫ ω,f (x,ω) ∂P)≤B := by
    have hh := weighted_product_trace_replacement n m
      (ha.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (hc.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (hab x) (hcd x) (hbb x) (hdd x) (hr4 x) (hC x)
    simp only [Function.comp_apply,id_eq] at hh
    refine ⟨hh.1,hh.2.trans ?_⟩
    have hs_a : Real.sqrt (∫ ω,(a (x,ω)-b x)^2 ∂P)≤ε :=
      (Real.sqrt_le_sqrt (hvariance_a x)).trans_eq (Real.sqrt_sq hε)
    have hs_c : Real.sqrt (∫ ω,(c (x,ω)-d x)^2 ∂P)≤ε :=
      (Real.sqrt_le_sqrt (hvariance_c x)).trans_eq (Real.sqrt_sq hε)
    calc
      _≤((n : ℝ)*ε+(m : ℝ)*ε)*Real.sqrt (1+C) := by gcongr
      _=B := by dsimp only [B];ring
  have hF : Integrable (fun x => ∫ ω,f (x,ω) ∂P) ν :=
    (integrable_const B).mono' hf.integral_prod_right'.aestronglyMeasurable
      (.of_forall (fun x => by
        rw [Real.norm_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
        exact (hx x).2))
  have hi : Integrable f (ν.prod P) := by
    apply (integrable_prod_iff hf.aestronglyMeasurable).mpr
    refine ⟨.of_forall (fun x => (hx x).1),?_⟩
    convert hF using 1
    funext x
    exact integral_congr_ae (.of_forall (fun ω => Real.norm_of_nonneg (abs_nonneg _)))
  refine ⟨hi,?_⟩
  rw [integral_prod _ hi]
  calc
    _≤∫ _ : A,B ∂ν := integral_mono_ae hF (integrable_const B) (.of_forall (fun x => (hx x).2))
    _=_ := by rw [integral_const];rfl

end SphericalAging.IntegratedMixedResponseTraceReplacement
