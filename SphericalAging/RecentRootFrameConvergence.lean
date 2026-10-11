module

public import SphericalAging.ActualCausalRootFrame
public import SphericalAging.SusceptibilityDiagonalTheorem

public section

/-! The actual recent colored root becomes the source rank-one root. Both the
fixed-window approximation and the discarded old recent mass are derived from
the selected profile and the constructed source diagonal. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.RecentRootFrameConvergence
open CausalTree CausalTree.HilbertDatum CKSpecification CKPhysicalConsequences CausalTreeRealization
open PrefixReflection CenterNormalization CausalCenterAverage TreePolynomialDrift
open CubicResponseLocalization SusceptibilityDiagonal SusceptibilityRecentCenters SusceptibilityWindow
open ActualCausalRootFrame

theorem rankOne_sub_norm_le (A : HilbertDatum) (x y : A.Carrier) :
    ‖pure A A x x-pure A A y y‖≤(‖x‖+‖y‖)*‖x-y‖ := by
  have he : pure A A x x-pure A A y y=pure A A (x-y) x+pure A A y (x-y) := by
    change pureBilinear A A x x-pureBilinear A A y y=
      pureBilinear A A (x-y) x+pureBilinear A A y (x-y)
    simp only [map_sub,ContinuousLinearMap.sub_apply]
    abel
  rw [he]
  apply (norm_add_le _ _).trans_eq
  rw [norm_pure,norm_pure]
  ring

theorem pure_smul_self (A : HilbertDatum) (a : ℝ) (x : A.Carrier) :
    pure A A (a • x) (a • x)=(a*a) • pure A A x x := by
  change pureBilinear A A (a • x) (a • x)=_
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_smul]
  rfl

theorem recent_integral_error_bound {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {a b t T E : ℝ} (ha : 0≤a) (hab : a≤b) (hbt : b≤t)
    (x : Space 2)
    (herror : ∀u∈Icc a b,‖projectedRankOne h T u-pure (spaceDatum 2) (spaceDatum 2) x x‖≤E) :
    ‖(∫u in a..b,d.R t u • projectedRankOne h T u)-
      (∫u in a..b,d.R t u) • pure (spaceDatum 2) (spaceDatum 2) x x‖≤E*(∫u in a..b,d.R t u) := by
  have hr := CausalStripIntegralBound.response_continuousOn_interval h ha hbt
  have hi := projected_row_intervalIntegrable h T ha hab hbt
  have hic : IntervalIntegrable (fun u => d.R t u • pure (spaceDatum 2) (spaceDatum 2) x x) volume a b :=
    (hr.smul continuousOn_const).intervalIntegrable_of_Icc hab
  rw [←intervalIntegral.integral_smul_const,←intervalIntegral.integral_sub hi hic,
    ←intervalIntegral.integral_const_mul]
  apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
  apply intervalIntegral.integral_mono_on hab (hi.sub hic).norm
    ((hr.const_mul E).intervalIntegrable_of_Icc hab)
  intro u hu
  dsimp only
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg ((physical_bounds_of_equations h).2 t u (ha.trans hu.1) (hu.2.trans hbt)),mul_comm E]
  exact mul_le_mul_of_nonneg_left (herror u hu)
    ((physical_bounds_of_equations h).2 t u (ha.trans hu.1) (hu.2.trans hbt))

@[expose]  def recentFrameError {β : ℝ} {d : CKData} (h : CKEquations 3 β d) (q t L : ℝ) :=
  recentRootRow h t (t-L)-(q*susceptibility d t (t-L)) •
    pure (spaceDatum 2) (spaceDatum 2) (normalizedCenter h t L) (normalizedCenter h t L)

 theorem recentFrameError_bound {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {q t L W ε : ℝ} (hq : q∈Icc (0:ℝ) 1) (hT : 0≤t-L) (hW : 0≤W) (hWL : W≤L)
    (hunit : ‖normalizedCenter h t L‖=1)
    (heps : ∀τ∈Icc (0:ℝ) W,
      ‖prefixVector h (t-L) (t-τ)-Real.sqrt q • normalizedCenter h t L‖≤ε) :
    ‖recentFrameError h q t L‖≤
      2*(susceptibility d t (t-L)-windowMass d t W)+2*ε*windowMass d t W := by
  let U := normalizedCenter h t L
  let x := Real.sqrt q • U
  have hL : 0≤L := hW.trans hWL
  have hx : ‖x‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg q),show ‖U‖=1 from hunit,mul_one]
    exact Real.sqrt_le_one.mpr hq.2
  have hqrank : pure (spaceDatum 2) (spaceDatum 2) x x=q • pure (spaceDatum 2) (spaceDatum 2) U U := by
    rw [show x=Real.sqrt q • U from rfl,pure_smul_self]
    congr 1
    nlinarith [Real.sq_sqrt hq.1]
  have hglobal : ∀u∈Icc (t-L) t,‖projectedRankOne h (t-L) u-pure (spaceDatum 2) (spaceDatum 2) x x‖≤2 := by
    intro u hu
    apply (norm_sub_le _ _).trans
    rw [projectedRankOne,norm_pure,norm_pure]
    have hp := prefixVector_norm_le_one h (physical_bounds_of_equations h) (t-L) (hT.trans hu.1)
    nlinarith [norm_nonneg (prefixVector h (t-L) u),norm_nonneg x]
  have hlocal : ∀u∈Icc (t-W) t,‖projectedRankOne h (t-L) u-pure (spaceDatum 2) (spaceDatum 2) x x‖≤2*ε := by
    intro u hu
    have hτ : t-u∈Icc (0:ℝ) W := ⟨by linarith [hu.2],by linarith [hu.1]⟩
    have hp := prefixVector_norm_le_one h (physical_bounds_of_equations h) (t-L) (show 0≤u by linarith [hu.1])
    have hh := rankOne_sub_norm_le (spaceDatum 2) (prefixVector h (t-L) u) x
    have he : ‖prefixVector h (t-L) u-x‖≤ε := by
      simpa only [sub_sub_cancel] using heps (t-u) hτ
    change ‖pure (spaceDatum 2) (spaceDatum 2) (prefixVector h (t-L) u) (prefixVector h (t-L) u)-
      pure (spaceDatum 2) (spaceDatum 2) x x‖≤_
    exact hh.trans ((mul_le_mul_of_nonneg_right (by linarith : ‖prefixVector h (t-L) u‖+‖x‖≤2) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left he (by norm_num)))
  have hleft := recent_integral_error_bound h hT (by linarith : t-L≤t-W) (by linarith : t-W≤t) x
    (fun u hu => hglobal u ⟨hu.1,hu.2.trans (by linarith)⟩)
  have hright := recent_integral_error_bound h (by linarith : 0≤t-W) (by linarith : t-W≤t) le_rfl x hlocal
  have hi1 := projected_row_intervalIntegrable h (t-L) hT (by linarith : t-L≤t-W) (by linarith : t-W≤t)
  have hi2 := projected_row_intervalIntegrable h (t-L) (by linarith : 0≤t-W) (by linarith : t-W≤t) le_rfl
  have hr1 : IntervalIntegrable (fun u => d.R t u) volume (t-L) (t-W) := (CausalStripIntegralBound.response_continuousOn_interval h hT (by linarith : t-W≤t)).intervalIntegrable_of_Icc (by linarith : t-L≤t-W)
  have hr2 : IntervalIntegrable (fun u => d.R t u) volume (t-W) t := (CausalStripIntegralBound.response_continuousOn_interval h (by linarith : 0≤t-W) le_rfl).intervalIntegrable_of_Icc (by linarith : t-W≤t)
  have hsplit : recentFrameError h q t L=
      ((∫u in (t-L)..(t-W),d.R t u • projectedRankOne h (t-L) u)-
        (∫u in (t-L)..(t-W),d.R t u) • pure (spaceDatum 2) (spaceDatum 2) x x)+
      ((∫u in (t-W)..t,d.R t u • projectedRankOne h (t-L) u)-
        (∫u in (t-W)..t,d.R t u) • pure (spaceDatum 2) (spaceDatum 2) x x) := by
    unfold recentFrameError recentRootRow susceptibility
    rw [←intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
      ←intervalIntegral.integral_add_adjacent_intervals hr1 hr2,hqrank,smul_smul]
    dsimp only [U]
    simp only [mul_add,add_smul,smul_smul,mul_comm]
    abel
  rw [hsplit]
  apply (norm_add_le _ _).trans
  have hμ : (∫u in (t-L)..(t-W),d.R t u)=susceptibility d t (t-L)-windowMass d t W := by
    rw [windowMass_eq]
    unfold susceptibility
    rw [←intervalIntegral.integral_add_adjacent_intervals hr1 hr2]
    ring
  have hb := add_le_add hleft hright
  simpa only [hμ,show (∫u in (t-W)..t,d.R t u)=windowMass d t W from (windowMass_eq d t W).symm] using hb

theorem recentFrameError_tendsto_zero {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) {t L : ℕ→ℝ}
    (A : Receipt h c q t L) (ht : Tendsto t atTop atTop) :
    Tendsto (fun n => ‖recentFrameError h q (t n) (L n)‖) atTop (𝓝 (0:ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε8 : 0<ε/8 := by positivity
  obtain ⟨W0,hW0⟩ := eventually_atTop.mp (H.plateau_limit.eventually (Metric.ball_mem_nhds q hε8))
  let W : ℝ := max 1 W0
  have hW : 0<W := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hcW : c W-q<ε/8 := by
    have hh := hW0 W (le_max_right _ _)
    exact (le_abs_self _).trans_lt hh
  have hwindow := (windowMass_tendsto H hW.le).comp ht
  have hboundlim : Tendsto (fun n => 2*(susceptibility d (t n) (t n-L n)-windowMass d (t n) W)+
      2*(ε/8)*windowMass d (t n) W) atTop (𝓝 (2*((1-q)-(1-c W))+2*(ε/8)*(1-c W))) :=
    ((A.recent_mass_tendsto.sub hwindow).const_mul 2).add (hwindow.const_mul (2*(ε/8)))
  have htarget : 2*((1-q)-(1-c W))+2*(ε/8)*(1-c W)<ε := by
    have hc0 := (H.correlation_bounds W hW.le).1
    have hq0 := H.q_positive
    have hmu : 1-c W≤1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hmu (show 0≤2*(ε/8) by positivity)
    linarith
  filter_upwards [A.age_tendsto.eventually (eventually_ge_atTop W),
    recent_centers_uniform H A hW hε8,hboundlim.eventually (gt_mem_nhds htarget)] with n hn hpn hbn
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact (recentFrameError_bound h ⟨H.q_positive.le,H.plateau_lt_one.le⟩ (A.waiting_nonnegative n)
    hW.le hn (A.center_unit n) hpn).trans_lt hbn

end SphericalAging.RecentRootFrameConvergence
