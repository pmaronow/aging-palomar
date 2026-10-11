module

public import SphericalAging.ActualStateIncrementMoments

public section

/-! Quantitative time modulus of the actual empirical overlap and its
annealed mean. These are genuine full product-law increment estimates;
they do not assert a pathwise time-supremum concentration limit. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualOverlapTimeModulus
open HardSphereDynamics ActualStateIncrementMoments ActualModelOverlapVariance
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem overlap_increment_square_le (hN : 0<N) (x y z : State N) (hx : OnSphere x) :
    (⟪x,y⟫_ℝ/(N : ℝ)-⟪x,z⟫_ℝ/(N : ℝ))^2≤‖y-z‖^2/(N : ℝ) := by
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hcs := (sq_le_sq₀ (abs_nonneg ⟪x,y-z⟫_ℝ)
    (mul_nonneg (norm_nonneg x) (norm_nonneg (y-z)))).mpr
      (norm_inner_le_norm (𝕜 := ℝ) x (y-z))
  rw [sq_abs,mul_pow,(onSphere_iff_norm_sq x).mp hx] at hcs
  rw [← sub_div,← inner_sub_right,div_pow]
  calc
    _≤((N : ℝ)*‖y-z‖^2)/(N : ℝ)^2 :=
      div_le_div_of_nonneg_right hcs (sq_nonneg _)
    _=_ := by field_simp

theorem actualOverlap_eq_state (β R : ℝ≥0) (hR : 0<(R : ℝ)) (s t : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :
    actualOverlap β R hR s t ω=
      ⟪actualState β R hR s ω,actualState β R hR t ω⟫_ℝ/(N : ℝ) := rfl

theorem actualOverlap_symm (β R : ℝ≥0) (hR : 0<(R : ℝ)) (s t : ℝ≥0) :
    actualOverlap (N := N) (p := p) β R hR s t=actualOverlap β R hR t s := by
  funext ω
  rw [actualOverlap_eq_state,actualOverlap_eq_state,real_inner_comm]

theorem actualOverlap_memLp_two (hN : 1≤N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0) :
    MemLp (actualOverlap (p := p) β R hR s t) 2 (AnnealedModelLaw.law N p) := by
  have hm := ((actualState_memLp (p := p) hN β R hR hNR s).aestronglyMeasurable.inner (𝕜 := ℝ)
    (actualState_memLp (p := p) hN β R hR hNR t).aestronglyMeasurable)
  apply MemLp.of_bound ((continuous_id.div_const (N : ℝ)).comp_aestronglyMeasurable hm) 1
  filter_upwards [actualState_onSphere hN β R hR hNR] with ω hω
  exact FiniteCorrelationIto.overlap_abs_le_one (by omega : 0<N) (hω s) (hω t)

theorem actual_overlap_second_time_secondMoment (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (a s u : ℝ≥0) :
    (∫ ω,(actualOverlap (p := p) β R hR a (s+u) ω-actualOverlap β R hR a s ω)^2
      ∂AnnealedModelLaw.law N p)≤ incrementCeiling p β u := by
  have hdiff := (actualOverlap_memLp_two (p := p) hN β R hR hNR a (s+u)).sub
    (actualOverlap_memLp_two (p := p) hN β R hR hNR a s)
  have hstate := (actualState_memLp (p := p) hN β R hR hNR (s+u)).sub
    (actualState_memLp (p := p) hN β R hR hNR s)
  calc
    _≤∫ ω,‖actualState (p := p) β R hR (s+u) ω-actualState β R hR s ω‖^2/(N : ℝ)
        ∂AnnealedModelLaw.law N p := by
      apply integral_mono_ae hdiff.integrable_sq (hstate.integrable_norm_pow'.div_const _)
      filter_upwards [actualState_onSphere hN β R hR hNR] with ω hω
      exact overlap_increment_square_le (by omega : 0<N) _ _ _ (hω a)
    _=(∫ ω,‖actualState (p := p) β R hR (s+u) ω-actualState β R hR s ω‖^2
        ∂AnnealedModelLaw.law N p)/(N : ℝ) := integral_div _ _
    _≤ incrementCeiling p β u := actual_increment_secondMoment hN hp β R hR hNR s u

theorem actual_overlap_first_time_secondMoment (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (a s u : ℝ≥0) :
    (∫ ω,(actualOverlap (p := p) β R hR (s+u) a ω-actualOverlap β R hR s a ω)^2
      ∂AnnealedModelLaw.law N p)≤ incrementCeiling p β u := by
  rw [actualOverlap_symm β R hR (s+u) a,actualOverlap_symm β R hR s a]
  exact actual_overlap_second_time_secondMoment hN hp β R hR hNR a s u

theorem actual_overlap_two_time_secondMoment (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s t u v : ℝ≥0) :
    (∫ ω,(actualOverlap (p := p) β R hR (s+u) (t+v) ω-actualOverlap β R hR s t ω)^2
      ∂AnnealedModelLaw.law N p)≤2*incrementCeiling p β u+2*incrementCeiling p β v := by
  let a := fun ω => actualOverlap (N := N) (p := p) β R hR (s+u) (t+v) ω-actualOverlap β R hR (s+u) t ω
  let b := fun ω => actualOverlap (N := N) (p := p) β R hR (s+u) t ω-actualOverlap β R hR s t ω
  have ha := (actualOverlap_memLp_two (p := p) hN β R hR hNR (s+u) (t+v)).sub
    (actualOverlap_memLp_two (p := p) hN β R hR hNR (s+u) t)
  have hb := (actualOverlap_memLp_two (p := p) hN β R hR hNR (s+u) t).sub
    (actualOverlap_memLp_two (p := p) hN β R hR hNR s t)
  have hwhole := (actualOverlap_memLp_two (p := p) hN β R hR hNR (s+u) (t+v)).sub
    (actualOverlap_memLp_two (p := p) hN β R hR hNR s t)
  have hai : Integrable (fun ω => (a ω)^2) (AnnealedModelLaw.law N p) := ha.integrable_sq
  have hbi : Integrable (fun ω => (b ω)^2) (AnnealedModelLaw.law N p) := hb.integrable_sq
  calc
    _≤∫ ω,2*(a ω)^2+2*(b ω)^2 ∂AnnealedModelLaw.law N p := by
      apply integral_mono hwhole.integrable_sq ((hai.const_mul 2).add (hbi.const_mul 2))
      intro ω
      change (actualOverlap β R hR (s+u) (t+v) ω-actualOverlap β R hR s t ω)^2≤
        2*(actualOverlap β R hR (s+u) (t+v) ω-actualOverlap β R hR (s+u) t ω)^2+
          2*(actualOverlap β R hR (s+u) t ω-actualOverlap β R hR s t ω)^2
      nlinarith [sq_nonneg (actualOverlap β R hR (s+u) (t+v) ω-
        2*actualOverlap β R hR (s+u) t ω+actualOverlap β R hR s t ω)]
    _=2*(∫ ω,(a ω)^2 ∂AnnealedModelLaw.law N p)+2*(∫ ω,(b ω)^2 ∂AnnealedModelLaw.law N p) := by
      rw [integral_add (hai.const_mul _) (hbi.const_mul _),integral_const_mul,integral_const_mul]
    _≤2*incrementCeiling p β v+2*incrementCeiling p β u := add_le_add
      (mul_le_mul_of_nonneg_left (actual_overlap_second_time_secondMoment hN hp β R hR hNR (s+u) t v) (by norm_num))
      (mul_le_mul_of_nonneg_left (actual_overlap_first_time_secondMoment hN hp β R hR hNR t s u) (by norm_num))
    _=_ := add_comm _ _

theorem actual_overlap_two_time_L1 (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s t u v : ℝ≥0) :
    (∫ ω,|actualOverlap (p := p) β R hR (s+u) (t+v) ω-actualOverlap β R hR s t ω|
      ∂AnnealedModelLaw.law N p)≤ Real.sqrt (2*incrementCeiling p β u+2*incrementCeiling p β v) := by
  have hm := (actualOverlap_memLp_two (p := p) hN β R hR hNR (s+u) (t+v)).sub
    (actualOverlap_memLp_two (p := p) hN β R hR hNR s t)
  have hh := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq (AnnealedModelLaw.law N p)
    (fun ω => |actualOverlap (p := p) β R hR (s+u) (t+v) ω-actualOverlap β R hR s t ω|) hm.norm
  simp only [probReal_univ,one_mul,sq_abs] at hh
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _))
    (by have hu := incrementCeiling_nonneg p β u;have hv := incrementCeiling_nonneg p β v;positivity)).mpr
      (hh.trans (actual_overlap_two_time_secondMoment hN hp β R hR hNR s t u v))

theorem actual_overlap_mean_two_time_modulus (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s t u v : ℝ≥0) :
    |(∫ ω,actualOverlap (p := p) β R hR (s+u) (t+v) ω ∂AnnealedModelLaw.law N p)-
      ∫ ω,actualOverlap β R hR s t ω ∂AnnealedModelLaw.law N p|≤
        Real.sqrt (2*incrementCeiling p β u+2*incrementCeiling p β v) := by
  rw [← integral_sub ((actualOverlap_memLp_two (p := p) hN β R hR hNR (s+u) (t+v)).integrable (by norm_num))
    ((actualOverlap_memLp_two (p := p) hN β R hR hNR s t).integrable (by norm_num))]
  exact (abs_integral_le_integral_abs).trans (actual_overlap_two_time_L1 hN hp β R hR hNR s t u v)

end SphericalAging.ActualOverlapTimeModulus
