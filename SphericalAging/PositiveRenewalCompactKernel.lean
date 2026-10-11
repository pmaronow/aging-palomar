module

public import SphericalAging.PositiveRenewalCellBound
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Group.IntegralConvolution

public section

/-! Actual bounded Lipschitz renewal convolutions for compact kernels,
using positive support alone and the proved first-entry interval bound. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.PositiveRenewalCompactKernel
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PositiveRenewalCellBound PositiveRenewalSeries AbsorptionCutoff.Renewal

@[expose] def renewalConvolution (μ : Measure ℝ) (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y,H (x-y) ∂renewalMeasure μ

theorem shifted_kernel_zero {H : ℝ → ℝ} {R : ℝ}
    (hs : ∀t : ℝ,t∉Icc (-R) R → H t=0) (x y : ℝ)
    (hy : y∉Icc (x-R) (x+R)) : H (x-y)=0 := by
  apply hs
  intro ht
  apply hy
  constructor <;> linarith [ht.1,ht.2]

theorem compact_kernel_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {H : ℝ → ℝ} (hm : Measurable H)
    {R B : ℝ} (hs : ∀t : ℝ,t∉Icc (-R) R → H t=0)
    (hb : ∀t : ℝ,‖H t‖≤B) (x : ℝ) :
    Integrable (fun y : ℝ => H (x-y)) (renewalMeasure μ) := by
  have hfin := positive_renewal_locally_finite hp (x-R) (x+R)
  let : IsFiniteMeasure ((renewalMeasure μ).restrict (Icc (x-R) (x+R))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfin.lt_top⟩
  have hi : IntegrableOn (fun y : ℝ => H (x-y)) (Icc (x-R) (x+R)) (renewalMeasure μ) :=
    Integrable.of_bound
      ((hm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable) B
      (Eventually.of_forall fun y => hb (x-y))
  exact hi.integrable_of_forall_notMem_eq_zero (shifted_kernel_zero hs x)

theorem compact_kernel_renewalSeries {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {H : ℝ → ℝ} (hm : Measurable H)
    {R B : ℝ} (hs : ∀t : ℝ,t∉Icc (-R) R → H t=0)
    (hb : ∀t : ℝ,‖H t‖≤B) (x : ℝ) :
    renewalConvolution μ H x=∑'n : ℕ,∫ y,H (x-y) ∂convPow μ n :=
  integral_sum_measure (compact_kernel_integrable hp hm hs hb x)

theorem compact_kernel_uniform_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {H : ℝ → ℝ}
    {R B : ℝ} (hs : ∀t : ℝ,t∉Icc (-R) R → H t=0)
    (hb : ∀t : ℝ,‖H t‖≤B) :
    ∀x : ℝ,‖renewalConvolution μ H x‖≤
      B*(renewalMeasure μ (Icc 0 (2*R))).toReal := by
  intro x
  have hB : 0≤B := (norm_nonneg (H 0)).trans (hb 0)
  have hfin := positive_renewal_locally_finite hp 0 (2*R)
  have hmass : renewalMeasure μ (Icc (x-R) (x+R))≤renewalMeasure μ (Icc 0 (2*R)) := by
    simpa only [show x-R+2*R=x+R by ring] using positive_renewal_interval_bound hp (x-R) (2*R)
  have hmassReal : (renewalMeasure μ).real (Icc (x-R) (x+R))≤
      (renewalMeasure μ (Icc 0 (2*R))).toReal := ENNReal.toReal_mono hfin hmass
  change ‖∫ y,H (x-y) ∂renewalMeasure μ‖≤_
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (shifted_kernel_zero hs x)]
  exact (norm_setIntegral_le_of_norm_le_const
    (positive_renewal_locally_finite hp (x-R) (x+R)).lt_top
    (fun y _ => hb (x-y))).trans (mul_le_mul_of_nonneg_left hmassReal hB)

/-- Every actual compactly supported Lipschitz renewal convolution is
uniformly bounded and Lipschitz, with an explicit finite first-entry constant.
No moment, nonarithmetic, or renewal-limit assumption is used. -/
theorem compact_kernel_lipschitz {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {H : ℝ → ℝ} {K : ℝ≥0}
    (hL : LipschitzWith K H) {R B : ℝ}
    (hs : ∀t : ℝ,t∉Icc (-R) R → H t=0) (hb : ∀t : ℝ,‖H t‖≤B) :
    LipschitzWith (K*⟨2*(renewalMeasure μ (Icc 0 (2*R))).toReal,by positivity⟩)
      (renewalConvolution μ H) := by
  apply LipschitzWith.of_dist_le_mul
  intro x x'
  let U := renewalMeasure μ
  let S := Icc (x-R) (x+R)∪Icc (x'-R) (x'+R)
  have hfin₁ : U (Icc (x-R) (x+R))<∞ := (positive_renewal_locally_finite hp _ _).lt_top
  have hfin₂ : U (Icc (x'-R) (x'+R))<∞ := (positive_renewal_locally_finite hp _ _).lt_top
  have hfin : U S<∞ := measure_union_lt_top hfin₁ hfin₂
  have hz : ∀y : ℝ,y∉S → H (x-y)-H (x'-y)=0 := by
    intro y hy
    simp only [S,mem_union,not_or] at hy
    rw [shifted_kernel_zero hs x y hy.1,shifted_kernel_zero hs x' y hy.2,sub_self]
  have hmass (a : ℝ) : U.real (Icc (a-R) (a+R))≤(U (Icc 0 (2*R))).toReal := by
    apply ENNReal.toReal_mono (positive_renewal_locally_finite hp 0 (2*R))
    simpa only [show a-R+2*R=a+R by ring] using positive_renewal_interval_bound hp (a-R) (2*R)
  have hS : U.real S≤2*(U (Icc 0 (2*R))).toReal := by
    exact (measureReal_union_le _ _).trans (by linarith [hmass x,hmass x'])
  have hi := compact_kernel_integrable hp hL.continuous.measurable hs hb x
  have hi' := compact_kernel_integrable hp hL.continuous.measurable hs hb x'
  rw [dist_eq_norm,renewalConvolution,renewalConvolution,←integral_sub hi hi',
    ←setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hdiff (y : ℝ) : ‖H (x-y)-H (x'-y)‖≤(K:ℝ)*dist x x' := by
    simpa only [dist_eq_norm,sub_sub_sub_cancel_right] using hL.dist_le_mul (x-y) (x'-y)
  calc
    _≤((K:ℝ)*dist x x')*U.real S := norm_setIntegral_le_of_norm_le_const hfin (fun y _ => hdiff y)
    _≤((K:ℝ)*dist x x')*(2*(U (Icc 0 (2*R))).toReal) :=
      mul_le_mul_of_nonneg_left hS (mul_nonneg K.coe_nonneg dist_nonneg)
    _=_ := by
      change ((K:ℝ)*dist x x')*(2*(U (Icc 0 (2*R))).toReal)=
        ((K:ℝ)*(2*(U (Icc 0 (2*R))).toReal))*dist x x'
      ring

/-- The actual renewal convolution satisfies the renewal equation, obtained
from the proved measure identity and Fubini; it is not a representation premise. -/
theorem compact_kernel_renewal_equation {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {H : ℝ → ℝ} (hm : Measurable H)
    {R B : ℝ} (hs : ∀t : ℝ,t∉Icc (-R) R → H t=0)
    (hb : ∀t : ℝ,‖H t‖≤B) (x : ℝ) :
    renewalConvolution μ H x=H x+∫t,renewalConvolution μ H (x-t) ∂μ := by
  let U := renewalMeasure μ
  let : SFinite U := by dsimp [U,renewalMeasure];infer_instance
  have hi := compact_kernel_integrable hp hm hs hb x
  have hle : U∗μ≤U := by
    calc
      U∗μ≤Measure.dirac 0+U∗μ := Measure.le_add_left le_rfl
      _=U := (renewalMeasure_eq_dirac_add_conv μ).symm
  have hiConv : Integrable (fun y : ℝ => H (x-y)) (μ∗U) := by
    rw [Measure.conv_comm]
    exact hi.mono_measure hle
  have hiDirac : Integrable (fun y : ℝ => H (x-y)) (Measure.dirac 0) :=
    Integrable.of_bound ((hm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
      B (Eventually.of_forall fun y => hb (x-y))
  calc
    _=∫y,H (x-y) ∂(Measure.dirac 0+U∗μ) := by
      unfold renewalConvolution
      rw [renewalMeasure_eq_dirac_add_conv]
    _=H x+∫y,H (x-y) ∂(μ∗U) := by
      rw [Measure.conv_comm U μ,integral_add_measure hiDirac hiConv,integral_dirac,sub_zero]
    _=H x+∫t,∫y,H (x-(t+y)) ∂U ∂μ := by rw [integral_conv hiConv]
    _=_ := by
      congr 1
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by change H (x-(t+y))=H ((x-t)-y);congr 1;ring)

end
end SphericalAging.PositiveRenewalCompactKernel
