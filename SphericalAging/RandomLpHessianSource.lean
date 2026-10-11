module

public import SphericalAging.RandomLpCoefficient
public import SphericalAging.LpProductBounds
public import SphericalAging.LpMultiplierTruncation

public section

/-! Actual bounded random Hessian multiplication on genuine fourth
moment directions. The value is its true L² equivalence class. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.RandomLpHessianSource
open HardSphereDynamics
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
local instance : NormedAddCommGroup (State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance

lemma bilinear_bound (H : State N→L[ℝ] State N→L[ℝ] State N) {L : ℝ}
    (hH : ‖H‖≤L) (u v : State N) : ‖H u v‖≤L*‖u‖*‖v‖ :=
  ((H u).le_opNorm v).trans (mul_le_mul_of_nonneg_right
    ((H.le_opNorm u).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _))) (norm_nonneg _))

lemma field_memLp (H : Ω→State N→L[ℝ] State N→L[ℝ] State N)
    (hH : AEStronglyMeasurable H P) (M : ℝ≥0) (hM : ∀ᵐ omega ∂P,‖H omega‖≤M)
    (U V : Lp (State N) 2 P) (hU : MemLp U 4 P) (hV : MemLp V 4 P) :
    MemLp (fun omega => H omega (U omega) (V omega)) 2 P := by
  have hm : AEStronglyMeasurable (fun omega => H omega (U omega) (V omega)) P :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hH.prodMk (Lp.aestronglyMeasurable U))).prodMk (Lp.aestronglyMeasurable V))
  apply (hU.norm.fun_mul hV.norm).of_le_mul hm (c:=(M:ℝ))
  filter_upwards [hM] with omega homega
  simpa only [mul_assoc,Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using
    bilinear_bound (H omega) homega (U omega) (V omega)

@[expose] def source (H : Ω→State N→L[ℝ] State N→L[ℝ] State N)
    (hH : AEStronglyMeasurable H P) (M : ℝ≥0) (hM : ∀ᵐ omega ∂P,‖H omega‖≤M)
    (U V : Lp (State N) 2 P) (hU : MemLp U 4 P) (hV : MemLp V 4 P) : Lp (State N) 2 P :=
  (field_memLp H hH M hM U V hU hV).toLp _

lemma source_coe (H : Ω→State N→L[ℝ] State N→L[ℝ] State N)
    (hH : AEStronglyMeasurable H P) (M : ℝ≥0) (hM : ∀ᵐ omega ∂P,‖H omega‖≤M)
    (U V : Lp (State N) 2 P) (hU : MemLp U 4 P) (hV : MemLp V 4 P) :
    source H hH M hM U V hU hV=ᵐ[P] (fun omega => H omega (U omega) (V omega)) :=
  (field_memLp H hH M hM U V hU hV).coeFn_toLp

lemma source_norm_le (H : Ω→State N→L[ℝ] State N→L[ℝ] State N)
    (hH : AEStronglyMeasurable H P) (M : ℝ≥0) (hM : ∀ᵐ omega ∂P,‖H omega‖≤M)
    (U V : Lp (State N) 2 P) (hU : MemLp U 4 P) (hV : MemLp V 4 P) :
    ‖source H hH M hM U V hU hV‖≤(M:ℝ)*lpNorm U 4 P*lpNorm V 4 P := by
  have hp : MemLp (fun omega => ‖U omega‖*‖V omega‖) 2 P := hU.norm.fun_mul hV.norm
  have hb : lpNorm (source H hH M hM U V hU hV) 2 P≤
      (M:ℝ)*lpNorm (fun omega => ‖U omega‖*‖V omega‖) 2 P := by
    have hh : eLpNorm (source H hH M hM U V hU hV) 2 P≤
        eLpNorm (fun omega => (M:ℝ)*(‖U omega‖*‖V omega‖)) 2 P := by
      apply eLpNorm_mono_ae (Lp.aestronglyMeasurable _)
      filter_upwards [source_coe H hH M hM U V hU hV,hM] with omega he homega
      rw [he,Real.norm_of_nonneg (by positivity : 0≤(M:ℝ)*(‖U omega‖*‖V omega‖))]
      simpa only [mul_assoc] using bilinear_bound (H omega) homega (U omega) (V omega)
    have hn := ENNReal.toReal_mono (hp.const_mul M).eLpNorm_ne_top hh
    change lpNorm (source H hH M hM U V hU hV) 2 P≤
      lpNorm (fun omega => (M:ℝ)*(‖U omega‖*‖V omega‖)) 2 P at hn
    rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg M.coe_nonneg] at hn
    exact hn
  rw [Lp.norm_def]
  exact hb.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (LpProductBounds.lpNorm_product_le hU hV) M.coe_nonneg)
end SphericalAging.RandomLpHessianSource
