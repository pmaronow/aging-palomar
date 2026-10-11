module

public import SphericalAging.ScalarConstraints
public import SphericalAging.PlateauAlgebra
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

public section

/-! Actual center-energy age limit from profile FDT and dominated convergence. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.ProfileCenterEnergy
open ScalarConstraints

/-- Exact preceding stationary-profile hypotheses. -/
structure Profile (c r : ℝ → ℝ) (q : ℝ) : Prop where
  continuous_c : ContinuousOn c (Ici 0)
  continuous_r : ContinuousOn r (Ici 0)
  bounds : ∀ t, 0 ≤ t → 0 ≤ c t ∧ c t ≤ 1
  initial : c 0=1
  limit : Tendsto c atTop (nhds q)
  integrable_r : IntegrableOn r (Ioi 0)
  fdt : ∀ t, 0<t → HasDerivAt c (-r t) t

theorem weighted_response_integrable {c r : ℝ → ℝ} {q : ℝ}
    (H : Profile c r q) (k : ℕ) : IntegrableOn (fun u => c u^k*r u) (Ioi 0) := by
  apply H.integrable_r.norm.mono'
    ((((H.continuous_c.pow k).mul H.continuous_r).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change ‖c u^k*r u‖ ≤ ‖r u‖
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg (H.bounds u hu.le).1 k),Real.norm_eq_abs]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (pow_le_one₀ (H.bounds u hu.le).1 (H.bounds u hu.le).2) (abs_nonneg (r u))

/-- FDT determines every exact power-weighted total response mass. -/
theorem weighted_response_integral {c r : ℝ → ℝ} {q : ℝ}
    (H : Profile c r q) (k : ℕ) :
    (∫ u in Ioi (0:ℝ), c u^k*r u)=(1-q^(k+1))/(k+1:ℝ) := by
  have hk : (0:ℝ)<k+1 := by positivity
  have hi := (weighted_response_integrable H k).const_mul (-(k+1:ℝ))
  have hd (t : ℝ) (ht : t∈Ioi (0:ℝ)) :
      HasDerivAt (fun u => c u^(k+1)) (-(k+1:ℝ)*(c t^k*r t)) t := by
    convert (H.fdt t ht).pow (k+1) using 1
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    ring
  have he := integral_Ioi_of_hasDerivAt_of_tendsto
    ((H.continuous_c.pow (k+1)).continuousWithinAt (by simp : (0:ℝ)∈Ici 0))
    hd hi (H.limit.pow (k+1))
  simp only [integral_const_mul,Pi.pow_apply,H.initial,one_pow] at he
  apply (eq_div_iff hk.ne').mpr
  nlinarith

/-- Reflected memory uses 2D-u with the genuine cutoff u≤D. -/
theorem reflected_memory_tendsto (f g : ℝ → ℝ) (q M : ℝ)
    (hf : ContinuousOn f (Ici 0)) (hg : IntegrableOn g (Ioi 0))
    (hbound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M) (hlim : Tendsto f atTop (nhds q)) :
    Tendsto (fun D => ∫ u in (0:ℝ)..D, f (2*D-u)*g u) atTop
      (nhds (q*(∫ u in Ioi (0:ℝ),g u))) := by
  let F : ℝ → ℝ → ℝ := fun D u => if u ≤ D then rayExtension f (2*D-u)*g u else 0
  have hfe := rayExtension_continuous f hf
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbound 0 le_rfl)
  have hFm (D : ℝ) : AEStronglyMeasurable (F D) (volume.restrict (Ioi 0)) := by
    have hh : AEStronglyMeasurable (fun u => rayExtension f (2*D-u)*g u)
        (volume.restrict (Ioi 0)) :=
      ((hfe.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul hg.aestronglyMeasurable
    convert hh.indicator (s:=Iic D) measurableSet_Iic using 1
    ext u
    simp only [F,Set.indicator,mem_Iic]
  have hFb : ∀ᶠ D : ℝ in atTop, ∀ᵐ u ∂volume.restrict (Ioi 0), ‖F D u‖ ≤ M*‖g u‖ := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with D hD
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    dsimp only [F]
    split_ifs with hut
    · have harg : 0 ≤ 2*D-u := by linarith
      rw [Real.norm_eq_abs,abs_mul,rayExtension_eq f _ harg,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hbound _ harg) (abs_nonneg _)
    · simpa using mul_nonneg hM (norm_nonneg (g u))
  have hFlim (u : ℝ) : Tendsto (fun D => F D u) atTop (nhds (q*g u)) := by
    have htwo : Tendsto (fun D : ℝ => 2*D) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos (show (0:ℝ)<2 by norm_num)).mpr tendsto_id
    have harg : Tendsto (fun D : ℝ => 2*D-u) atTop atTop := by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-u) htwo
    apply ((hlim.comp harg).mul_const (g u)).congr'
    filter_upwards [eventually_ge_atTop u,eventually_ge_atTop (0:ℝ)] with D huD hD
    have harg0 : 0≤2*D-u := by linarith
    simp only [F,ite_eq_left huD,rayExtension_eq f _ harg0,Function.comp_def]
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (μ:=volume.restrict (Ioi 0)) (F:=F) (f:=fun u => q*g u) (fun u => M*‖g u‖)
    (Eventually.of_forall hFm) hFb (hg.norm.const_mul M) (Eventually.of_forall hFlim)
  rw [integral_const_mul] at hdct
  apply hdct.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with D hD
  rw [intervalIntegral.integral_of_le hD]
  have hind : (∫ u in Ioi 0,F D u)=
      ∫ u in Iic D,rayExtension f (2*D-u)*g u ∂volume.restrict (Ioi 0) := by
    rw [←integral_indicator measurableSet_Iic]
    apply integral_congr_ae
    exact Eventually.of_forall (fun u => by simp [F,Set.indicator])
  rw [hind,Measure.restrict_restrict measurableSet_Iic,
    show Iic D ∩ Ioi (0:ℝ)=Ioc 0 D by ext u; simp [and_comm]]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  dsimp only
  rw [rayExtension_eq f _ (by linarith [hu.2])]

@[expose] def prefixEnergyLimit (p : ℕ) (β ell : ℝ) (c r : ℝ → ℝ) (D : ℝ) : ℝ :=
  (ell-1)/((p:ℝ)*β)+β*(p:ℝ)*
    (∫ u in (0:ℝ)..D,r u*(c (2*D-u)^(p-1)-c u^(p-1)))

/-- The limit of the actual source finite-age energy formula is derived, not
assumed. FDT supplies both integrals and dominated convergence supplies the age limit. -/
theorem prefixEnergyLimit_tendsto {p : ℕ} {β : ℝ} {c r : ℝ → ℝ} {q : ℝ}
    (hp : 3≤p) (H : Profile c r q) :
    Tendsto (prefixEnergyLimit p β (PlateauAlgebra.multiplier p β q) c r) atTop
      (nhds (PlateauAlgebra.centerEnergy p β q)) := by
  have hp0 : (p:ℝ)≠0 := ne_of_gt (PlateauAlgebra.spin_positive hp)
  have hb : ∀ t : ℝ, 0≤t → |c t^(p-1)|≤1 := by
    intro t ht
    rw [abs_of_nonneg (pow_nonneg (H.bounds t ht).1 _)]
    exact pow_le_one₀ (H.bounds t ht).1 (H.bounds t ht).2
  have href := reflected_memory_tendsto (fun t => c t^(p-1)) r (q^(p-1)) 1
    (H.continuous_c.pow (p-1)) H.integrable_r hb (H.limit.pow (p-1))
  have hplain := intervalIntegral_tendsto_integral_Ioi (0:ℝ)
    (weighted_response_integrable H (p-1)) tendsto_id
  have hmass := weighted_response_integral H 0
  simp only [pow_zero,one_mul,Nat.cast_zero,zero_add,div_one,pow_one] at hmass
  rw [hmass] at href
  have hweighted := weighted_response_integral H (p-1)
  have hpn : p-1+1=p := by omega
  have hpcast : ((p-1:ℕ):ℝ)+1=(p:ℝ) := by exact_mod_cast hpn
  rw [hpn,hpcast] at hweighted
  rw [hweighted] at hplain
  have hlim := ((href.sub hplain).const_mul (β*(p:ℝ))).const_add
    ((PlateauAlgebra.multiplier p β q-1)/((p:ℝ)*β))
  have heq : (PlateauAlgebra.multiplier p β q-1)/((p:ℝ)*β)+
      β*(p:ℝ)*(q^(p-1)*(1-q)-(1-q^p)/(p:ℝ))=PlateauAlgebra.centerEnergy p β q := by
    unfold PlateauAlgebra.centerEnergy PlateauAlgebra.clusterEnergy
    field_simp [hp0]
    ring
  rw [heq] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with D hD
  have hi1 : IntervalIntegrable (fun u => c (2*D-u)^(p-1)*r u) volume 0 D :=
    (((H.continuous_c.comp (by fun_prop) (by intro u hu; change 0≤2*D-u; linarith [hu.2])).pow (p-1)).mul
      (H.continuous_r.mono (by intro u hu; exact hu.1))).intervalIntegrable_of_Icc hD
  have hi2 : IntervalIntegrable (fun u => c u^(p-1)*r u) volume 0 D :=
    (((H.continuous_c.pow (p-1)).mul H.continuous_r).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hD
  unfold prefixEnergyLimit
  simp only [id_eq]
  rw [←intervalIntegral.integral_sub hi1 hi2]
  congr 2
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  ring

end SphericalAging.ProfileCenterEnergy
