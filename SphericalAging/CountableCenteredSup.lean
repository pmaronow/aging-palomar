module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

/-! Measurable centered suprema of bounded countable random families. -/
noncomputable section
open Set MeasureTheory
namespace SphericalAging.CountableCenteredSup
variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [Nonempty ι]
    {P : Measure Ω} [IsProbabilityMeasure P]

@[expose] def centeredSup (Y : ι→Ω→ℝ) (P : Measure Ω) (ω : Ω) : ℝ :=
  ⨆i : ι,|Y i ω-∫z,Y i z ∂P|

theorem mean_abs_le_one (Y : ι→Ω→ℝ) (hY : ∀i,Integrable (Y i) P)
    (hb : ∀ᵐω ∂P,∀i,|Y i ω| ≤ 1) (i : ι) : |∫ω,Y i ω ∂P| ≤ 1 := by
  refine abs_integral_le_integral_abs.trans ?_
  calc
    _ ≤ ∫ω,(1:ℝ) ∂P := integral_mono_ae (hY i).abs (integrable_const _) (hb.mono (fun ω hω => hω i))
    _ = 1 := by simp

theorem centeredSup_aestronglyMeasurable (Y : ι→Ω→ℝ) (hY : ∀i,MemLp (Y i) 2 P) :
    AEStronglyMeasurable (centeredSup Y P) P := by
  apply AEMeasurable.aestronglyMeasurable
  apply AEMeasurable.iSup
  intro i
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using
    ((hY i).sub (memLp_const (∫z,Y i z ∂P))).aestronglyMeasurable.norm.aemeasurable

theorem centeredSup_bounds (Y : ι→Ω→ℝ) (hY : ∀i,MemLp (Y i) 2 P)
    (hb : ∀ᵐω ∂P,∀i,|Y i ω| ≤ 1) :
    ∀ᵐω ∂P,0 ≤ centeredSup Y P ω ∧ centeredSup Y P ω ≤ 2 := by
  have hm := mean_abs_le_one Y (fun i => (hY i).integrable (by norm_num)) hb
  filter_upwards [hb] with ω hω
  have he (i : ι) : |Y i ω-∫z,Y i z ∂P| ≤ 2 :=
    (abs_sub _ _).trans (by linarith [hω i,hm i])
  have hbd : BddAbove (range (fun i : ι => |Y i ω-∫z,Y i z ∂P|)) := ⟨2,by rintro _ ⟨i,rfl⟩;exact he i⟩
  refine ⟨(abs_nonneg _).trans (le_ciSup hbd (Classical.arbitrary ι)),?_⟩
  exact ciSup_le he

theorem centeredSup_memLp_two (Y : ι→Ω→ℝ) (hY : ∀i,MemLp (Y i) 2 P)
    (hb : ∀ᵐω ∂P,∀i,|Y i ω| ≤ 1) : MemLp (centeredSup Y P) 2 P := by
  apply MemLp.of_bound (centeredSup_aestronglyMeasurable Y hY) 2
  filter_upwards [centeredSup_bounds Y hY hb] with ω hω
  simpa only [Real.norm_eq_abs,abs_of_nonneg hω.1] using hω.2

end SphericalAging.CountableCenteredSup
