module

public import SphericalAging.ActualDisorderGammaVariance

public section

/-! Genuine L² time continuity of the actual Brownian vector, including
zero, with its exact square-increment norm. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.BrownianClassTimeContinuity
open HardSphereDynamics ActualDisorderGammaVariance BrownianVectorMoments
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

theorem brownianClass_increment_norm_sq {s t : ℝ≥0} (hst : s≤t) :
    ‖brownianClass (N:=N) t-brownianClass s‖^2=(N : ℝ)*(t-s : ℝ≥0) := by
  rw [←PredictableFamilyLift.integral_norm_sq_Lp]
  have he : (fun ω => ‖(brownianClass (N:=N) t-brownianClass s : Lp (State N) 2 (VectorBrownian.law N)) ω‖^2)=ᵐ[VectorBrownian.law N]
      fun ω => ‖brownianVector t ω-brownianVector s ω‖^2 := by
    filter_upwards [Lp.coeFn_sub (brownianClass (N:=N) t) (brownianClass s),brownianClass_ae (N:=N) t,brownianClass_ae (N:=N) s] with ω h1 h2 h3
    simp only [h1,Pi.sub_apply,h2,h3]
  rw [integral_congr_ae he]
  have hh := brownianVector_increment_secondMoment (N:=N) s (t-s)
  rw [add_tsub_cancel_of_le hst] at hh
  exact hh

theorem brownianClass_distance_sq (s t : ℝ≥0) :
    dist (brownianClass (N:=N) t) (brownianClass s)^2=(N : ℝ)*dist t s := by
  rw [dist_eq_norm]
  by_cases hst : s≤t
  · rw [brownianClass_increment_norm_sq hst]
    simp only [NNReal.dist_eq,NNReal.coe_sub hst,abs_of_nonneg (show (0 : ℝ)≤(t : ℝ)-s by exact sub_nonneg.mpr (show (s : ℝ)≤t by exact_mod_cast hst))]
  · have hts := le_of_not_ge hst
    rw [norm_sub_rev,brownianClass_increment_norm_sq hts]
    simp only [NNReal.dist_eq,NNReal.coe_sub hts,abs_sub_comm]
    rw [abs_of_nonneg (show (0 : ℝ)≤(s : ℝ)-t by exact sub_nonneg.mpr (show (t : ℝ)≤s by exact_mod_cast hts))]

theorem brownianClass_continuous :
    Continuous (brownianClass (N:=N)) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε^2/((N : ℝ)+1),by positivity,?_⟩
  intro t ht
  have he := brownianClass_distance_sq (N:=N) s t
  have hsmall : ((N : ℝ)+1)*dist t s<ε^2 := by simpa only [mul_comm] using (lt_div_iff₀ (by positivity : (0 : ℝ)<(N : ℝ)+1)).mp ht
  nlinarith [show 0≤dist t s from dist_nonneg,show 0≤dist (brownianClass (N:=N) t) (brownianClass s) from dist_nonneg]

end SphericalAging.BrownianClassTimeContinuity
