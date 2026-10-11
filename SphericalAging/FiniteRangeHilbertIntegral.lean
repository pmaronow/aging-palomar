module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

public section

/-! A direct finite-range Hilbert integral bound. The estimate uses
2ab≤a²+b² and the width of the diagonal strip, with no convolution theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.FiniteRangeHilbertIntegral

@[expose] def band (D : ℝ) (z : ℝ×ℝ) : ℝ := if |z.1-z.2|≤D then 1 else 0

theorem band_measurable (D : ℝ) : Measurable (band D) := by
  exact measurable_const.ite
    (measurableSet_le (by fun_prop : Measurable (fun z : ℝ×ℝ => |z.1-z.2|)) measurable_const)
    measurable_const

theorem band_nonneg (D : ℝ) (z : ℝ×ℝ) : 0≤band D z := by
  unfold band
  split_ifs <;> norm_num

theorem band_le_one (D : ℝ) (z : ℝ×ℝ) : band D z≤1 := by
  unfold band
  split_ifs <;> norm_num

theorem band_symm (D u w : ℝ) : band D (u,w)=band D (w,u) := by
  simp only [band,abs_sub_comm]

theorem band_slice_integrable (a b D u : ℝ) :
    Integrable (fun w => band D (u,w)) (volume.restrict (Icc a b)) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact ((band_measurable D).comp (by fun_prop : Measurable (fun w : ℝ => (u,w)))).aestronglyMeasurable
  · filter_upwards with w
    rw [Real.norm_eq_abs,abs_of_nonneg (band_nonneg _ _)]
    exact band_le_one _ _

theorem band_slice_integral_le (a b D u : ℝ) (hD : 0≤D) :
    (∫w : ℝ, band D (u,w) ∂volume.restrict (Icc a b))≤2*D := by
  have he : (fun w => band D (u,w))=(Icc (u-D) (u+D)).indicator (fun _ => (1 : ℝ)) := by
    funext w
    simp only [band,indicator,mem_Icc,abs_le]
    congr 1
    apply propext
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [he,integral_indicator measurableSet_Icc,setIntegral_const]
  simp only [smul_eq_mul,mul_one,measureReal_def]
  rw [Measure.restrict_apply measurableSet_Icc]
  calc
    _ ≤ (volume (Icc (u-D) (u+D))).toReal :=
      ENNReal.toReal_mono (isCompact_Icc.measure_ne_top) (measure_mono inter_subset_left)
    _ = 2*D := by
      rw [Real.volume_Icc,ENNReal.toReal_ofReal (by linarith)]
      ring

theorem band_weight_integrable (a b D : ℝ) (q : ℝ→ℝ)
    (hq : Integrable q (volume.restrict (Icc a b))) :
    Integrable (fun z : ℝ×ℝ => band D z*q z.1) ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) := by
  have hi := hq.norm.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc a b)))
  apply hi.mono'
  · exact (band_measurable D).aestronglyMeasurable.mul
      (hq.aestronglyMeasurable.comp_fst)
  · filter_upwards with z
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (band_nonneg _ _),mul_one]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (band_le_one _ _) (norm_nonneg _)

theorem band_weight_integral_le (a b D : ℝ) (q : ℝ→ℝ) (hD : 0≤D)
    (hq : Integrable q (volume.restrict (Icc a b))) (hq0 : ∀u,0≤q u) :
    (∫u : ℝ, ∫w : ℝ,band D (u,w)*q u ∂volume.restrict (Icc a b)
      ∂volume.restrict (Icc a b)) ≤ 2*D*(∫u : ℝ,q u ∂volume.restrict (Icc a b)) := by
  rw [←integral_const_mul]
  apply integral_mono_ae
    (band_weight_integrable a b D q hq).integral_prod_left (hq.const_mul (2*D))
  filter_upwards with u
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (band_slice_integral_le a b D u hD) (hq0 u)

theorem norm_integral_sq_le_of_finite_range {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : ℝ→E) (a b D : ℝ) (hD : 0≤D)
    (hf : Integrable f (volume.restrict (Icc a b)))
    (hf2 : Integrable (fun u => ‖f u‖^2) (volume.restrict (Icc a b)))
    (horth : ∀u∈Icc a b,∀w∈Icc a b,D≤|u-w| → inner ℝ (f u) (f w)=0) :
    ‖∫u : ℝ,f u ∂volume.restrict (Icc a b)‖^2 ≤
      2*D*(∫u : ℝ,‖f u‖^2 ∂volume.restrict (Icc a b)) := by
  let μ := volume.restrict (Icc a b)
  have hfi : Integrable f μ := hf
  let q : ℝ→ℝ := fun u => ‖f u‖^2
  have hqi : Integrable q μ := hf2
  have hq0 : ∀u,0≤q u := fun u => sq_nonneg _
  have hB := band_weight_integrable a b D q hqi
  have hB' : Integrable (fun z : ℝ×ℝ => band D z*q z.2) (μ.prod μ) := by
    convert hB.swap using 1
    ext z
    dsimp only [Function.comp_def,Prod.swap]
    rw [band_symm]
  have hbi : Integrable (fun z : ℝ×ℝ => (band D z*q z.1+band D z*q z.2)/2) (μ.prod μ) :=
    (hB.add hB').div_const 2
  have hinner : ∀u, Integrable (fun w => inner ℝ (f u) (f w)) μ := fun u => hfi.const_inner (f u)
  have hnorm : ‖∫u,f u ∂μ‖^2=∫u,∫w,inner ℝ (f u) (f w) ∂μ ∂μ := by
    simp_rw [integral_inner hfi]
    rw [←real_inner_self_eq_norm_sq]
    symm
    calc
      _ = ∫u,inner ℝ (∫v,f v ∂μ) (f u) ∂μ := integral_congr_ae
        (Eventually.of_forall (fun u => real_inner_comm _ _))
      _ = _ := integral_inner hfi _
  rw [hnorm]
  have hle : (∫u,∫w,inner ℝ (f u) (f w) ∂μ ∂μ) ≤
      ∫u,∫w,(band D (u,w)*q u+band D (u,w)*q w)/2 ∂μ ∂μ := by
    apply integral_mono_ae (by
      simp_rw [integral_inner hfi]
      exact hfi.inner_const (∫u,f u ∂μ)) hbi.integral_prod_left
    filter_upwards [ae_restrict_mem measurableSet_Icc,hbi.prod_right_ae] with u hu hbu
    apply integral_mono_ae (hinner u) hbu
    filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
    by_cases hnear : |u-w|≤D
    · simp only [band,hnear,ite_eq_left,one_mul,q]
      have hCS := real_inner_le_norm (f u) (f w)
      nlinarith [sq_nonneg (‖f u‖-‖f w‖)]
    · rw [horth u hu w hw (le_of_not_ge hnear)]
      simp [band,hnear]
  have hs : (∫u,∫w,band D (u,w)*q w ∂μ ∂μ)=(∫u,∫w,band D (u,w)*q u ∂μ ∂μ) := by
    rw [integral_integral_swap hB']
    congr 1
    funext u
    congr 1
    funext w
    rw [band_symm]
  have he : (∫u,∫w,(band D (u,w)*q u+band D (u,w)*q w)/2 ∂μ ∂μ)=
      ∫u,∫w,band D (u,w)*q u ∂μ ∂μ := by
    simp_rw [integral_div]
    have hae : ∀ᵐ u : ℝ ∂μ, Integrable (fun w => band D (u,w)*q u) μ ∧
        Integrable (fun w => band D (u,w)*q w) μ := hB.prod_right_ae.and hB'.prod_right_ae
    rw [integral_congr_ae (hae.mono (fun u hu => integral_add hu.1 hu.2))]
    rw [integral_add hB.integral_prod_left hB'.integral_prod_left,hs]
    ring
  exact hle.trans (he ▸ band_weight_integral_le a b D q hD hqi hq0)

end SphericalAging.FiniteRangeHilbertIntegral
