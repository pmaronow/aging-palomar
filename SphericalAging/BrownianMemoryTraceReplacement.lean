module

public import SphericalAging.ResponseTraceReplacement
public import SphericalAging.PredictableProductNorm

public section

/-! Two genuine Hölder replacements for a Brownian response memory:
first the bounded correlation power against the L² product Γ R, then Γ
against R. Neither step requires a variance bound for the response trace. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SphericalAging.BrownianMemoryTraceReplacement
open ResponseTraceReplacement
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

 theorem weighted_power_L2_replacement {a r : Ω→ℝ} {b : ℝ} (n : ℕ)
    (ha : AEStronglyMeasurable a P) (hab : ∀ᵐ ω ∂P,|a ω|≤1) (hb : |b|≤1)
    (hr : MemLp r 2 P) :
    Integrable (fun ω => |((a ω)^n-b^n)*r ω|) P ∧
      (∫ ω,|((a ω)^n-b^n)*r ω| ∂P)≤
        (n : ℝ)*Real.sqrt (∫ ω,(a ω-b)^2 ∂P)*Real.sqrt (∫ ω,(r ω)^2 ∂P) := by
  have hd : MemLp (fun ω => a ω-b) 2 P := MemLp.of_bound (ha.sub aestronglyMeasurable_const) 2
    (hab.mono (fun ω hw => by rw [Real.norm_eq_abs];exact (abs_sub (a ω) b).trans (by linarith)))
  have hg : Integrable (fun ω => |a ω-b| * |r ω|) P := by
    simpa only [Real.norm_eq_abs] using
      ((hd.norm.fun_mul hr.norm : MemLp (fun ω => ‖a ω-b‖*‖r ω‖) 1 P).integrable (by norm_num))
  have hmajor := hg.const_mul (n : ℝ)
  have hbound : ∀ᵐ ω ∂P,|((a ω)^n-b^n)*r ω|≤(n : ℝ)*(|a ω-b| * |r ω|) := by
    filter_upwards [hab] with ω hw
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (pow_difference_abs_le n hw hb) (abs_nonneg _)).trans_eq (by ring)
  have hi : Integrable (fun ω => |((a ω)^n-b^n)*r ω|) P :=
    hmajor.mono' (((ha.pow n).sub aestronglyMeasurable_const).mul hr.aestronglyMeasurable).norm
      (hbound.mono (fun ω hw => by simpa only [Real.norm_eq_abs,abs_abs] using hw))
  refine ⟨hi,?_⟩
  calc
    _≤∫ ω,(n : ℝ)*(|a ω-b| * |r ω|) ∂P := integral_mono_ae hi hmajor hbound
    _=(n : ℝ)*(∫ ω,|(a ω-b)*r ω| ∂P) := by simp only [integral_const_mul,abs_mul]
    _≤(n : ℝ)*(Real.sqrt (∫ ω,(a ω-b)^2 ∂P)*Real.sqrt (∫ ω,(r ω)^2 ∂P)) :=
      mul_le_mul_of_nonneg_left (integral_abs_mul_le_sqrt hd hr) (Nat.cast_nonneg n)
    _=_ := by ring

 theorem fourth_product_secondMoment {g r : Ω→ℝ} (hg : MemLp g 4 P) (hr : MemLp r 4 P) :
    MemLp (fun ω => g ω*r ω) 2 P ∧
      (∫ ω,(g ω*r ω)^2 ∂P)≤
        Real.sqrt (∫ ω,|g ω|^4 ∂P)*Real.sqrt (∫ ω,|r ω|^4 ∂P) := by
  have hgsq : MemLp (fun ω => (g ω)^2) 2 P := by
    simpa only [pow_two] using (hg.fun_mul hg : MemLp (fun ω => g ω*g ω) 2 P)
  have hrsq : MemLp (fun ω => (r ω)^2) 2 P := by
    simpa only [pow_two] using (hr.fun_mul hr : MemLp (fun ω => r ω*r ω) 2 P)
  refine ⟨hg.fun_mul hr,?_⟩
  have hg4 (ω : Ω) : |g ω|^4=((g ω)^2)^2 := by rw [show (4 : ℕ)=2*2 from rfl,pow_mul,sq_abs]
  have hr4 (ω : Ω) : |r ω|^4=((r ω)^2)^2 := by rw [show (4 : ℕ)=2*2 from rfl,pow_mul,sq_abs]
  simp_rw [hg4,hr4]
  simpa only [abs_mul,abs_sq,mul_pow] using integral_abs_mul_le_sqrt hgsq hrsq

 theorem weighted_power_fourth_product_replacement {a g r : Ω→ℝ} {b G R : ℝ} (n : ℕ)
    (ha : AEStronglyMeasurable a P) (hab : ∀ᵐ ω ∂P,|a ω|≤1) (hb : |b|≤1)
    (hg : MemLp g 4 P) (hr : MemLp r 4 P)
    (hG : (∫ ω,|g ω|^4 ∂P)≤G) (hR : (∫ ω,|r ω|^4 ∂P)≤R) :
    Integrable (fun ω => |((a ω)^n-b^n)*g ω*r ω|) P ∧
      (∫ ω,|((a ω)^n-b^n)*g ω*r ω| ∂P)≤
        (n : ℝ)*Real.sqrt (∫ ω,(a ω-b)^2 ∂P)*Real.sqrt (Real.sqrt G*Real.sqrt R) := by
  have hp := fourth_product_secondMoment hg hr
  have hh := weighted_power_L2_replacement n ha hab hb hp.1
  have he : (fun ω => |((a ω)^n-b^n)*(g ω*r ω)|)=
      (fun ω => |((a ω)^n-b^n)*g ω*r ω|) := by funext ω;rw [mul_assoc]
  rw [he] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  gcongr
  exact hp.2.trans (by gcongr)

 theorem weighted_power_gamma_trace_factorization {a g r : Ω→ℝ} {b c G R Va Vg : ℝ} (n : ℕ)
    (ha : AEStronglyMeasurable a P) (hab : ∀ᵐ ω ∂P,|a ω|≤1) (hb : |b|≤1)
    (hg : MemLp g 4 P) (hr : MemLp r 4 P)
    (hG : (∫ ω,|g ω|^4 ∂P)≤G) (hR : (∫ ω,|r ω|^4 ∂P)≤R)
    (hVa : (∫ ω,(a ω-b)^2 ∂P)≤Va) (hVg : (∫ ω,(g ω-c)^2 ∂P)≤Vg) :
    Integrable (fun ω => (a ω)^n*g ω*r ω) P ∧
      |(∫ ω,(a ω)^n*g ω*r ω ∂P)-b^n*c*(∫ ω,r ω ∂P)|≤
        (n : ℝ)*Real.sqrt Va*Real.sqrt (Real.sqrt G*Real.sqrt R)+
          Real.sqrt Vg*Real.sqrt (1+R) := by
  have hgp := fourth_product_secondMoment hg hr
  have hgi := hgp.1.integrable (by norm_num)
  have hri := (hr.mono_exponent (by norm_num : (2 : ℝ≥0∞)≤4)).integrable (by norm_num)
  have hia : Integrable (fun ω => (a ω)^n*g ω*r ω) P := by
    apply hgi.norm.mono' (((ha.pow n).mul hg.aestronglyMeasurable).mul hr.aestronglyMeasurable)
    filter_upwards [hab] with ω hω
    dsimp only [Pi.mul_apply,Pi.pow_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_pow,Real.norm_eq_abs,abs_mul]
    calc
      _≤1*|g ω| * |r ω| := by gcongr;exact pow_le_one₀ (abs_nonneg _) hω
      _=_ := by simp
  have hd : MemLp (fun ω => g ω-c) 2 P := (hg.mono_exponent (by norm_num)).sub (memLp_const c)
  have htr := fourthMoment_to_secondMoment hr hR
  have hdri : Integrable (fun ω => (g ω-c)*r ω) P := by convert hd.integrable_mul htr.1 using 1
  have haeq : (∫ ω,(a ω)^n*g ω*r ω ∂P)-b^n*(∫ ω,g ω*r ω ∂P)=
      ∫ ω,((a ω)^n-b^n)*g ω*r ω ∂P := by
    rw [←integral_const_mul,←integral_sub hia (hgi.const_mul (b^n))]
    congr 1
    funext ω
    ring
  have hgeq : (∫ ω,g ω*r ω ∂P)-c*(∫ ω,r ω ∂P)=∫ ω,(g ω-c)*r ω ∂P := by
    rw [←integral_const_mul,←integral_sub hgi (hri.const_mul c)]
    congr 1
    funext ω
    ring
  have hrep := weighted_power_fourth_product_replacement n ha hab hb hg hr hG hR
  have hbnd1 : |(∫ ω,(a ω)^n*g ω*r ω ∂P)-b^n*(∫ ω,g ω*r ω ∂P)|≤
      (n : ℝ)*Real.sqrt Va*Real.sqrt (Real.sqrt G*Real.sqrt R) := by
    rw [haeq]
    exact abs_integral_le_integral_abs.trans (hrep.2.trans (by gcongr))
  have hbnd2 : |(∫ ω,g ω*r ω ∂P)-c*(∫ ω,r ω ∂P)|≤Real.sqrt Vg*Real.sqrt (1+R) := by
    rw [hgeq]
    exact abs_integral_le_integral_abs.trans ((integral_abs_mul_le_sqrt hd htr.1).trans
      (mul_le_mul (Real.sqrt_le_sqrt hVg) (Real.sqrt_le_sqrt htr.2)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  refine ⟨hia,?_⟩
  have he : (∫ ω,(a ω)^n*g ω*r ω ∂P)-b^n*c*(∫ ω,r ω ∂P)=
      ((∫ ω,(a ω)^n*g ω*r ω ∂P)-b^n*(∫ ω,g ω*r ω ∂P))+
        b^n*((∫ ω,g ω*r ω ∂P)-c*(∫ ω,r ω ∂P)) := by ring
  rw [he]
  calc
    _≤|(∫ ω,(a ω)^n*g ω*r ω ∂P)-b^n*(∫ ω,g ω*r ω ∂P)|+
        |b^n*((∫ ω,g ω*r ω ∂P)-c*(∫ ω,r ω ∂P))| := abs_add_le _ _
    _≤|(∫ ω,(a ω)^n*g ω*r ω ∂P)-b^n*(∫ ω,g ω*r ω ∂P)|+
        |(∫ ω,g ω*r ω ∂P)-c*(∫ ω,r ω ∂P)| := by
      apply add_le_add le_rfl
      rw [abs_mul,abs_pow]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hb)
    _≤_ := add_le_add hbnd1 hbnd2

end SphericalAging.BrownianMemoryTraceReplacement
