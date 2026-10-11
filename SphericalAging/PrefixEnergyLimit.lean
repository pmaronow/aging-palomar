module

public import SphericalAging.PrefixPicardOrder
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Exact lag-coordinate energy subtraction and its genuine dominated-convergence limit. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace NNReal ENNReal Topology
open Set Filter MeasureTheory
namespace SphericalAging.PrefixEnergyLimit
open CKSpecification PrefixReflection CausalTreeRealization GreenCovariance CKKernelBounds BackwardResponse

/-- A globally continuous representative of the actual lag energy integrand. -/
@[expose] def lagIntegrand {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (T L τ : ℝ) : ℝ := clampedResponse d (T+L) (T+L-τ)*
      (prefixKernel h T (max 0 (T+L-τ)) (max 0 (T+L))^(p-1)-
        clampedCorrelation d (T+L) (T+L-τ)^(p-1))

theorem lagIntegrand_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T L : ℝ) :
    Continuous (lagIntegrand h T L) :=
  ((clampedResponse_continuous h).comp (continuous_const.prodMk (continuous_const.sub continuous_id))).mul
    (((prefixKernel_clamped_continuous h hb T).comp
      ((continuous_const.sub continuous_id).prodMk continuous_const)).pow (p-1) |>.sub
        (((clampedCorrelation_continuous h).comp
          (continuous_const.prodMk (continuous_const.sub continuous_id))).pow (p-1)))

/-- The actual energy-integrand representatives admit a fixed integrable bound,
including outside the lag interval. -/
theorem lagIntegrand_abs_le_two {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T L τ : ℝ) :
    |lagIntegrand h T L τ| ≤ 2 := by
  have hq := prefixKernel_abs_le_one h hb T (t := max 0 (T+L-τ)) (s := max 0 (T+L))
    (le_max_left _ _) (le_max_left _ _)
  have hc : |clampedCorrelation d (T+L) (T+L-τ)| ≤ 1 := by
    rw [abs_of_nonneg (clampedCorrelation_nonnegative hb _ _)]
    exact (hb.1 _ _ (le_max_left _ _) (le_max_left _ _)).2
  have hqp : |prefixKernel h T (max 0 (T+L-τ)) (max 0 (T+L))^(p-1)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hq
  have hcp : |clampedCorrelation d (T+L) (T+L-τ)^(p-1)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hc
  unfold lagIntegrand
  rw [abs_mul]
  calc
    _ ≤ 1*(|prefixKernel h T (max 0 (T+L-τ)) (max 0 (T+L))^(p-1)|+
      |clampedCorrelation d (T+L) (T+L-τ)^(p-1)|) :=
      mul_le_mul (clampedResponse_abs_le_one h hb _ _) (abs_sub _ _)
        (abs_nonneg _) (by norm_num)
    _ ≤ 1*(1+1) := mul_le_mul_of_nonneg_left (add_le_add hqp hcp) (by norm_num)
    _ = 2 := by norm_num

theorem lagIntegrand_eq {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T L τ : ℝ} (hT : 0 ≤ T) (hτ : τ ∈ Icc 0 L) :
    lagIntegrand h T L τ = d.R (T+L) (T+L-τ)*
      (futureKernel h T (L-τ) L^(p-1)-d.C (T+L) (T+L-τ)^(p-1)) := by
  have ht : 0 ≤ T+L := by linarith [hτ.1,hτ.2]
  have hu : 0 ≤ T+L-τ := by linarith [hτ.2]
  unfold lagIntegrand futureKernel
  rw [max_eq_right hu, max_eq_right ht, clampedResponse_eq hu (by linarith [hτ.1]),
    clampedCorrelation_eq ht hu, show T+(L-τ)=T+L-τ from by ring]

/-- Exact prefix energy subtraction in the source's lag variable, before any limit. -/
theorem exact_lag_energy_subtraction {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T L : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) :
    treeEnergy p (prefixVector h T (T+L)) = energy p β d (T+L) +
      β*(p : ℝ)*(∫ τ in (0 : ℝ)..L, lagIntegrand h T L τ) := by
  rw [exact_prefix_energy_subtraction h hb hT hL]
  congr 2
  have hs := intervalIntegral.integral_comp_sub_left
    (fun u => d.R (T+L) u*(futureKernel h T (u-T) L^(p-1)-d.C (T+L) u^(p-1)))
    (a := 0) (b := L) (T+L)
  rw [sub_zero, show T+L-L=T from by ring] at hs
  rw [← hs]
  apply intervalIntegral.integral_congr
  intro τ hτ
  rw [uIcc_of_le hL] at hτ
  rw [lagIntegrand_eq h hT hτ]
  congr 2
  congr 1
  ring

/-- The full CK energy is the actual affine multiplier coordinate. -/
theorem energy_eq_multiplier_quotient {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    energy p β d t = (d.multiplier t-1)/((p : ℝ)*β) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 from by have := h.spin_ge_three; omega)
  have hβ : β ≠ 0 := ne_of_gt h.beta_pos
  apply (eq_div_iff (mul_ne_zero hp hβ)).mpr
  have hi := multiplier_energy_identity h t ht
  nlinarith

/-- The energy conclusion of prefix reflection from precisely the cluster coefficient
and reflected Gram limits. No energy limit or integral limit is assumed. -/
theorem prefix_energy_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T : ℕ → ℝ} (hT : ∀ n, 0 ≤ T n)
    {c r : ℝ → ℝ} {ell L : ℝ} (hL : 0 ≤ L)
    (hR : ∀ τ ∈ Icc 0 L, Tendsto (fun n => d.R (T n+L) (T n+L-τ)) atTop (nhds (r τ)))
    (hC : ∀ τ ∈ Icc 0 L, Tendsto (fun n => d.C (T n+L) (T n+L-τ)) atTop (nhds (c τ)))
    (hQ : ∀ τ ∈ Icc 0 L, Tendsto (fun n => futureKernel h (T n) (L-τ) L) atTop
      (nhds (c (2*L-τ))))
    (hlambda : Tendsto (fun n => d.multiplier (T n+L)) atTop (nhds ell)) :
    Tendsto (fun n => treeEnergy p (prefixVector h (T n) (T n+L))) atTop
      (nhds ((ell-1)/((p : ℝ)*β) + β*(p : ℝ)*
        (∫ τ in (0 : ℝ)..L, r τ*(c (2*L-τ)^(p-1)-c τ^(p-1))))) := by
  have hI : Tendsto (fun n => ∫ τ in (0 : ℝ)..L, lagIntegrand h (T n) L τ) atTop
      (nhds (∫ τ in (0 : ℝ)..L, r τ*(c (2*L-τ)^(p-1)-c τ^(p-1)))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (2 : ℝ))
    · exact Eventually.of_forall (fun n => (lagIntegrand_continuous h hb (T n) L).aestronglyMeasurable)
    · exact Eventually.of_forall (fun n => ae_of_all _ (fun τ _ => by
        simpa only [Real.norm_eq_abs] using lagIntegrand_abs_le_two h hb (T n) L τ))
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro τ hτ
      rw [uIoc_of_le hL] at hτ
      have hτ' : τ ∈ Icc 0 L := Ioc_subset_Icc_self hτ
      have hl := (hR τ hτ').mul ((hQ τ hτ').pow (p-1) |>.sub ((hC τ hτ').pow (p-1)))
      convert hl using 1
      funext n
      exact lagIntegrand_eq h (hT n) hτ'
  have hE : Tendsto (fun n => energy p β d (T n+L)) atTop
      (nhds ((ell-1)/((p : ℝ)*β))) := by
    have hquot : Tendsto (fun n => (d.multiplier (T n+L)-1)/((p : ℝ)*β)) atTop
        (nhds ((ell-1)/((p : ℝ)*β))) :=
      (hlambda.sub tendsto_const_nhds).div_const ((p : ℝ)*β)
    convert hquot using 1
    funext n
    exact energy_eq_multiplier_quotient h (add_nonneg (hT n) hL)
  have hl : Tendsto (fun n => energy p β d (T n+L) +
      β*(p : ℝ)*(∫ τ in (0 : ℝ)..L, lagIntegrand h (T n) L τ)) atTop
      (nhds ((ell-1)/((p : ℝ)*β) + β*(p : ℝ)*
        (∫ τ in (0 : ℝ)..L, r τ*(c (2*L-τ)^(p-1)-c τ^(p-1))))) :=
    hE.add (tendsto_const_nhds.mul hI)
  convert hl using 1
  funext n
  exact exact_lag_energy_subtraction h hb (hT n) hL

end SphericalAging.PrefixEnergyLimit
