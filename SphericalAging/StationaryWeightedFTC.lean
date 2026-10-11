module

public import SphericalAging.StationaryLogProfile

public section

/-! Genuine weighted integration by parts at the singular initial endpoint. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryWeightedFTC
noncomputable section

/-- A linear zero bound controls the singular boundary term and gives the
actual integrability needed for weighted integration by parts. -/
theorem weighted_Q_integrable (Q Q' : ℝ → ℝ) (ρ T : ℝ) (hρ : ρ<1) (hT : 0<T)
    (hd : ∀ t>0,HasDerivAt Q (Q' t) t) (hb : ∀ t>0,0≤Q t ∧ Q t≤t) :
    IntervalIntegrable (fun t => Q t*t^(-1-ρ)) volume 0 T := by
  have hi : IntervalIntegrable (fun t : ℝ => t^(-ρ)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
  apply hi.1.mono'
  · have hc : ContinuousOn Q (Ioc 0 T) := fun t ht => (hd t ht.1).continuousAt.continuousWithinAt
    have hm := hc.aestronglyMeasurable (μ:=volume) measurableSet_Ioc
    exact hm.mul (show AEStronglyMeasurable (fun t : ℝ => t^(-1-ρ)) (volume.restrict (Ioc 0 T)) from (by fun_prop : Measurable (fun t : ℝ => t^(-1-ρ))).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 := ht.1
    have hq0 := (hb t ht0).1
    have hpow := (Real.rpow_pos_of_pos ht0 (-1-ρ)).le
    have he := mul_le_mul_of_nonneg_right (hb t ht0).2 hpow
    have hr : t*t^(-1-ρ)=t^(-ρ) := by
      calc
        _ = t^(1:ℝ)*t^(-1-ρ) := by rw [Real.rpow_one]
        _ = t^(-ρ) := by rw [← Real.rpow_add ht0]; congr 1; ring
    change ‖Q t*t^(-1-ρ)‖≤t^(-ρ)
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hq0 hpow)]
    exact he.trans_eq hr

/-- Genuine improper FTC gives the exact finite-cutoff weighted balance,
without treating integration by parts as an assumed identity. -/
theorem weighted_integration_by_parts (Q Q' : ℝ → ℝ) (ρ T : ℝ) (hρ : ρ<1) (hT : 0<T)
    (hd : ∀ t>0,HasDerivAt Q (Q' t) t) (hb : ∀ t>0,0≤Q t ∧ Q t≤t)
    (hQp : IntervalIntegrable (fun t => Q' t*t^(-ρ)) volume 0 T) :
    (∫ t in 0..T,Q' t*t^(-ρ))=Q T*T^(-ρ)+ρ*(∫ t in 0..T,Q t*t^(-1-ρ)) := by
  let F := fun t : ℝ => Q t*t^(-ρ)
  let F' := fun t : ℝ => Q' t*t^(-ρ)-ρ*(Q t*t^(-1-ρ))
  have hqi := weighted_Q_integrable Q Q' ρ T hρ hT hd hb
  have hfi : IntervalIntegrable F' volume 0 T := hQp.sub (hqi.const_mul ρ)
  have hfd : ∀ t∈Ioo 0 T,HasDerivAt F (F' t) t := by
    intro t ht
    have hp := (hasDerivAt_id t).rpow_const (p:=-ρ) (Or.inl ht.1.ne')
    have he := (hd t ht.1).mul hp
    convert he using 1
    · rfl
    · simp only [F',id_eq,one_mul]
      rw [show -ρ-1=-1-ρ by ring]
      ring
  have hl : Tendsto F (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hp : Tendsto (fun t : ℝ => t^(1-ρ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hc : Tendsto (fun t : ℝ => t^(1-ρ)) (𝓝[>] (0:ℝ)) (𝓝 ((0:ℝ)^(1-ρ))) := (Real.continuousAt_rpow_const 0 (1-ρ) (Or.inr (by linarith))).tendsto.mono_left nhdsWithin_le_nhds
      simpa only [Real.zero_rpow (by linarith : 1-ρ≠0)] using hc
    apply squeeze_zero' _ _ hp
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_nonneg (hb t ht).1 (Real.rpow_pos_of_pos ht _).le
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have he := mul_le_mul_of_nonneg_right (hb t ht).2 (Real.rpow_pos_of_pos ht (-ρ)).le
      have hr : t*t^(-ρ)=t^(1-ρ) := by
        calc
          _ = t^(1:ℝ)*t^(-ρ) := by rw [Real.rpow_one]
          _ = t^(1-ρ) := by rw [← Real.rpow_add ht]; congr 1
      exact he.trans_eq hr
  have hr : Tendsto F (𝓝[<] T) (𝓝 (F T)) := by
    have hp := Real.continuousAt_rpow_const T (-ρ) (Or.inl hT.ne')
    exact ((hd T hT).continuousAt.mul hp).tendsto.mono_left nhdsWithin_le_nhds
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hT hfd hfi hl hr
  dsimp [F',F] at he
  rw [intervalIntegral.integral_sub hQp (hqi.const_mul ρ),intervalIntegral.integral_const_mul,sub_zero] at he
  linarith

end
end SphericalAging.StationaryWeightedFTC
