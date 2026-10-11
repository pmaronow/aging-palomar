module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real

public section

/-! A finite family of actual fourth moments controls the probability of
any large increment. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace SphericalAging.FiniteFourthExceedance
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} [IsFiniteMeasure P]

theorem exceedance_real_le {Y : Ω→E} (hY : MemLp Y 4 P) {a : ℝ} (ha : 0 < a) :
    P.real {ω | a < ‖Y ω‖} ≤ (∫ω,‖Y ω‖^4 ∂P)/a^4 := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (.of_forall (fun ω => pow_nonneg (norm_nonneg (Y ω)) 4)) hY.integrable_norm_pow' (a^4)
  have hs : {ω | a < ‖Y ω‖} ⊆ {ω | a^4 ≤ ‖Y ω‖^4} := by
    intro ω hω
    exact pow_le_pow_left₀ ha.le hω.le 4
  have hh := mul_le_mul_of_nonneg_left (measureReal_mono (μ:=P) hs) (pow_nonneg ha.le 4)
  exact (le_div_iff₀ (pow_pos ha 4)).mpr (by nlinarith [hh,hm])

theorem exceedance_le {Y : Ω→E} (hY : MemLp Y 4 P) {a : ℝ} (ha : 0 < a) :
    P {ω | a < ‖Y ω‖} ≤ ENNReal.ofReal ((∫ω,‖Y ω‖^4 ∂P)/a^4) := by
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top P _) (by positivity)).mpr
  exact exceedance_real_le hY ha

theorem finite_exceedance_le {ι : Type*} [Fintype ι] (Y : ι→Ω→E)
    (hY : ∀i,MemLp (Y i) 4 P) {a b : ℝ} (ha : 0 < a)
    (hb : ∀i,(∫ω,‖Y i ω‖^4 ∂P) ≤ b) :
    P {ω | ∃i,a < ‖Y i ω‖} ≤ ENNReal.ofReal ((Fintype.card ι:ℝ)*b/a^4) := by
  have he : {ω | ∃i,a < ‖Y i ω‖} = ⋃i,{ω | a < ‖Y i ω‖} := by ext; simp
  rw [he]
  refine (measure_iUnion_le _).trans ?_
  calc
    _ ≤ ∑'i : ι,ENNReal.ofReal (b/a^4) := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact (exceedance_le (hY i) ha).trans (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (hb i) (pow_nonneg ha.le 4)))
    _ = _ := by
      rw [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card ι))]
      congr 1
      ring

end SphericalAging.FiniteFourthExceedance
