module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

public section

/-! An integrable first moment from genuine quadratic tail estimates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace SphericalAging.WeakSecondMomentFirstMoment
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
set_option maxHeartbeats 800000

theorem lintegral_le_of_quadratic_tail (f : Ω→ℝ) (hf : AEMeasurable f P)
    (hf0 : ∀ω,0≤f ω) (M : ℝ) (hM : 0≤M)
    (hTail : ∀a : ℝ,0<a→P {ω | a<f ω}≤ENNReal.ofReal (M*a^(-2:ℝ))) :
    (∫⁻ω,ENNReal.ofReal (f ω) ∂P)≤ENNReal.ofReal (1+M) := by
  rw [lintegral_eq_lintegral_meas_lt P (.of_forall hf0) hf]
  have hsplit : Ioi (0:ℝ)=Ioc 0 1∪Ioi 1 := by
    ext x
    simp only [mem_Ioi,mem_union,mem_Ioc]
    constructor
    · intro h
      by_cases h1 : x≤1
      · exact Or.inl ⟨h,h1⟩
      · exact Or.inr (lt_of_not_ge h1)
    · rintro (h|h)
      · exact h.1
      · exact lt_trans zero_lt_one h
  rw [hsplit,lintegral_union measurableSet_Ioi (by simp : Disjoint (Ioc (0:ℝ) 1) (Ioi 1))]
  have hsmall : (∫⁻a in Ioc (0:ℝ) 1,P {ω | a<f ω})≤1 := by
    calc
      _≤∫⁻a in Ioc (0:ℝ) 1,(1:ℝ≥0∞) := lintegral_mono fun a => (measure_mono (subset_univ _)).trans_eq (measure_univ)
      _=1 := by simp
  have hlarge : (∫⁻a in Ioi (1:ℝ),P {ω | a<f ω})≤ENNReal.ofReal M := by
    calc
      _≤∫⁻a in Ioi (1:ℝ),ENNReal.ofReal (M*a^(-2:ℝ)) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro a ha
        exact hTail a (lt_trans zero_lt_one ha)
      _=ENNReal.ofReal M := by
        have hi : IntegrableOn (fun a : ℝ => M*a^(-2:ℝ)) (Ioi 1) :=
          (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) zero_lt_one).const_mul M
        rw [←ofReal_integral_eq_lintegral_ofReal hi]
        · rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) zero_lt_one]
          norm_num
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
          exact mul_nonneg hM (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one ha)) _)
  exact (add_le_add hsmall hlarge).trans_eq (by rw [ENNReal.ofReal_add zero_le_one hM];simp)

theorem integrable_and_integral_le_of_quadratic_tail (f : Ω→ℝ)
    (hf : AEStronglyMeasurable f P) (hf0 : ∀ω,0≤f ω) (M : ℝ) (hM : 0≤M)
    (hTail : ∀a : ℝ,0<a→P {ω | a<f ω}≤ENNReal.ofReal (M*a^(-2:ℝ))) :
    Integrable f P ∧ (∫ω,f ω ∂P)≤1+M := by
  have hb := lintegral_le_of_quadratic_tail f hf.aemeasurable hf0 M hM hTail
  have hi : Integrable f P := by
    refine ⟨hf,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (.of_forall hf0)]
    exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  refine ⟨hi,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hi (.of_forall hf0)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hb
end SphericalAging.WeakSecondMomentFirstMoment
