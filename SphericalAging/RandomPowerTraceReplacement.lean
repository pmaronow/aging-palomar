module

public import SphericalAging.FiniteHorizonTraceReplacement

public section

/-! Signed trace control for two random bounded overlap powers. No
independence between either overlap and the trace is required. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.RandomPowerTraceReplacement
open MeasureTheory ProbabilityTheory Set Filter ResponseTraceReplacement
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem weighted_random_power_difference {a b r : Ω→ℝ} {C : ℝ} (n : ℕ)
    (ha : AEStronglyMeasurable a P) (hb : AEStronglyMeasurable b P)
    (hab : ∀ᵐω ∂P,|a ω|≤1) (hbb : ∀ᵐω ∂P,|b ω|≤1)
    (hr : MemLp r 4 P) (hC : (∫ω,|r ω|^4 ∂P)≤C) :
    Integrable (fun ω => |((a ω)^n-(b ω)^n)*r ω|) P ∧
    (∫ω,|((a ω)^n-(b ω)^n)*r ω| ∂P)≤
      (n:ℝ)*Real.sqrt (∫ω,(a ω-b ω)^2 ∂P)*Real.sqrt (1+C) := by
  have hd : MemLp (fun ω => a ω-b ω) 2 P := MemLp.of_bound (ha.sub hb) 2 (by
    filter_upwards [hab,hbb] with ω haw hbw
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith))
  have ht := fourthMoment_to_secondMoment hr hC
  have hg : Integrable (fun ω => |a ω-b ω| * |r ω|) P := by
    simpa only [Real.norm_eq_abs,Pi.mul_apply] using
      ((hd.norm.fun_mul ht.1.norm).integrable (by norm_num : (1:ℝ≥0∞)≤1))
  have hbound : ∀ᵐω ∂P,|((a ω)^n-(b ω)^n)*r ω|≤(n:ℝ)*(|a ω-b ω| * |r ω|) := by
    filter_upwards [hab,hbb] with ω haw hbw
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (pow_difference_abs_le n haw hbw) (abs_nonneg _)).trans_eq (by ring)
  have hi : Integrable (fun ω => |((a ω)^n-(b ω)^n)*r ω|) P :=
    (hg.const_mul (n:ℝ)).mono' (((ha.pow n).sub (hb.pow n)).mul hr.aestronglyMeasurable).norm
      (hbound.mono fun ω hw => by simpa only [Real.norm_eq_abs,abs_abs] using hw)
  refine ⟨hi,?_⟩
  calc
    _≤∫ω,(n:ℝ)*(|a ω-b ω| * |r ω|) ∂P := integral_mono_ae hi (hg.const_mul _) hbound
    _=(n:ℝ)*(∫ω,|(a ω-b ω)*r ω| ∂P) := by simp only [integral_const_mul,abs_mul]
    _≤(n:ℝ)*(Real.sqrt (∫ω,(a ω-b ω)^2 ∂P)*Real.sqrt (∫ω,(r ω)^2 ∂P)) :=
      mul_le_mul_of_nonneg_left (integral_abs_mul_le_sqrt hd ht.1) (Nat.cast_nonneg n)
    _≤(n:ℝ)*(Real.sqrt (∫ω,(a ω-b ω)^2 ∂P)*Real.sqrt (1+C)) := by
      gcongr
      exact ht.2
    _=_ := by ring

theorem integrated_random_power_difference {A : Type*} [MeasurableSpace A]
    {ν : Measure A} [IsFiniteMeasure ν] {a b r : A×Ω→ℝ} {B C : ℝ} (n : ℕ)
    (ha : StronglyMeasurable a) (hb : StronglyMeasurable b) (hr : StronglyMeasurable r)
    (hab : ∀s,∀ᵐω ∂P,|a (s,ω)|≤1) (hbb : ∀s,∀ᵐω ∂P,|b (s,ω)|≤1)
    (hr4 : ∀s,MemLp (fun ω => r (s,ω)) 4 P)
    (hC : ∀s,(∫ω,|r (s,ω)|^4 ∂P)≤C)
    (hB : ∀s,(∫ω,(a (s,ω)-b (s,ω))^2 ∂P)≤B) :
    Integrable (fun q => |((a q)^n-(b q)^n)*r q|) (ν.prod P) ∧
    (∫q,|((a q)^n-(b q)^n)*r q| ∂ν.prod P)≤
      ν.real univ*((n:ℝ)*Real.sqrt B*Real.sqrt (1+C)) := by
  let f := fun q : A×Ω => |((a q)^n-(b q)^n)*r q|
  let D := (n:ℝ)*Real.sqrt B*Real.sqrt (1+C)
  have hf : StronglyMeasurable f := ((ha.pow n).sub (hb.pow n)).mul hr |>.norm
  have hs (s : A) : Integrable (fun ω => f (s,ω)) P ∧ (∫ω,f (s,ω) ∂P)≤D := by
    have hh := weighted_random_power_difference n
      (ha.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (hb.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (hab s) (hbb s) (hr4 s) (hC s)
    refine ⟨hh.1,hh.2.trans ?_⟩
    dsimp only [D]
    gcongr
    exact hB s
  have hF : Integrable (fun s => ∫ω,f (s,ω) ∂P) ν :=
    (integrable_const D).mono' hf.integral_prod_right'.aestronglyMeasurable (.of_forall fun s => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
      exact (hs s).2)
  have hi : Integrable f (ν.prod P) := by
    apply (integrable_prod_iff hf.aestronglyMeasurable).mpr
    refine ⟨.of_forall fun s => (hs s).1,?_⟩
    simpa only [Real.norm_eq_abs,f,abs_abs] using hF
  refine ⟨hi,?_⟩
  rw [integral_prod _ hi]
  exact (integral_mono_ae hF (integrable_const _) (.of_forall fun s => (hs s).2)).trans_eq (by
    rw [integral_const];rfl)

end SphericalAging.RandomPowerTraceReplacement
