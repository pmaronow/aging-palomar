module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

public section

/-! A deterministic vector primitive comparison used after actual
additive-noise cancellation. The estimate is derived by norm Gronwall. -/
noncomputable section
namespace SphericalAging.PrimitiveNormGronwall
open Set Filter MeasureTheory
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem primitive_norm_le {g : ℝ→E} (hg : Continuous g) {K ε T : ℝ}
    (hK : 1≤K) (hε : 0≤ε)
    (hbound : ∀t∈Ico 0 T,‖g t‖≤K*‖∫s in (0:ℝ)..t,g s‖+ε)
    {t : ℝ} (ht : t∈Icc 0 T) :
    ‖∫s in (0:ℝ)..t,g s‖≤ε*Real.exp (K*T) := by
  have hKp : 0<K := lt_of_lt_of_le zero_lt_one hK
  let F : ℝ→E := fun t => ∫s in (0:ℝ)..t,g s
  have hd (t : ℝ) : HasDerivAt F (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le
    (δ:=0) (K:=K) (ε:=ε) hc.continuousOn
    (fun s _ => (hd s).hasDerivWithinAt) (by simp [F]) hbound t ht
  rw [sub_zero,gronwallBound_of_K_ne_0 hKp.ne'] at hh
  dsimp only at hh
  simp only [zero_mul,zero_add] at hh
  have hdiv : ε/K≤ε := (div_le_iff₀ hKp).mpr (by nlinarith)
  have hexp : 0≤Real.exp (K*t)-1 := sub_nonneg.mpr
    (Real.one_le_exp_iff.mpr (mul_nonneg hKp.le ht.1))
  calc
    _ ≤ ε/K*(Real.exp (K*t)-1) := hh
    _ ≤ ε*(Real.exp (K*t)-1) := mul_le_mul_of_nonneg_right hdiv hexp
    _ ≤ ε*Real.exp (K*t) := mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) hε
    _ ≤ ε*Real.exp (K*T) := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hKp.le)) hε

end SphericalAging.PrimitiveNormGronwall
