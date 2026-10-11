module

public import SphericalAging.AnnealedResponseTraceReplacement

public section

/-! Integration of the overlap/trace replacement against an arbitrary
finite time measure. This analytic lemma consumes actual joint kernel
measurability, fourth moments, and overlap variance; none is a target
energy identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.FiniteHorizonTraceReplacement
set_option maxHeartbeats 500000
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
  {ν : Measure A} [IsFiniteMeasure ν] {P : Measure Ω} [IsProbabilityMeasure P]

theorem integrated_weighted_trace_replacement {a r : A × Ω → ℝ} {b : A → ℝ}
    {C ε : ℝ} (n : ℕ) (hε : 0≤ε) (ha : StronglyMeasurable a)
    (hr : StronglyMeasurable r) (hb : StronglyMeasurable b)
    (hab : ∀ x,∀ᵐ ω ∂P,|a (x,ω)|≤1) (hbb : ∀ x,|b x|≤1)
    (hr4 : ∀ x,MemLp (fun ω => r (x,ω)) 4 P)
    (hC : ∀ x,(∫ ω,|r (x,ω)|^4 ∂P)≤C)
    (hvariance : ∀ x,(∫ ω,(a (x,ω)-b x)^2 ∂P)≤ε^2) :
    Integrable (fun q => |((a q)^n-(b q.1)^n)*r q|) (ν.prod P) ∧
      (∫ q,|((a q)^n-(b q.1)^n)*r q| ∂ν.prod P)≤
        ν.real univ*((n : ℝ)*ε*Real.sqrt (1+C)) := by
  let B : ℝ := (n : ℝ)*ε*Real.sqrt (1+C)
  let f : A × Ω → ℝ := fun q => |((a q)^n-(b q.1)^n)*r q|
  have hf : StronglyMeasurable f := ((ha.pow n).sub (hb.comp_fst.pow n)).mul hr |>.norm
  have hx (x : A) : Integrable (fun ω => f (x,ω)) P ∧ (∫ ω,f (x,ω) ∂P)≤B := by
    have hh := ResponseTraceReplacement.weighted_trace_replacement n
      (ha.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (hab x) (hbb x) (hr4 x) (hC x)
    refine ⟨hh.1,hh.2.trans ?_⟩
    have hs : Real.sqrt (∫ ω,(a (x,ω)-b x)^2 ∂P)≤ε := by
      exact (Real.sqrt_le_sqrt (hvariance x)).trans_eq (Real.sqrt_sq hε)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)) (Real.sqrt_nonneg _)
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
    _ ≤ ∫ _ : A,B ∂ν := integral_mono_ae hF (integrable_const B) (.of_forall (fun x => (hx x).2))
    _ = _ := by rw [integral_const];rfl

end SphericalAging.FiniteHorizonTraceReplacement
