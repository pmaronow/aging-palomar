module

public import SphericalAging.WeightedPrimitiveConvergence

public section

/-! Continuous weights on a fixed late window follow from the preceding
uniform signed primitive limit. No sign of the approximating rows is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SphericalAging.SignedResponseWindowConvergence
open MeasureTheory Set Filter Topology WeightedPrimitiveConvergence

theorem continuous_weighted_window_limit {H a L K : ℝ}
    (ha : 0≤a) (hL : 0≤L) (haL : a+L≤H) (hK : 0≤K)
    (r : ℕ→ℝ→ℝ→ℝ)
    (hrows : ∀n t,t∈Icc 0 H→IntervalIntegrable (r n t) volume 0 t)
    (hvariation : ∀n t,t∈Icc 0 H→(∫u in (0:ℝ)..t,|r n t u|)≤K)
    (hprimitive : TendstoUniformlyOn
      (fun n (q : ℝ×ℝ) => ∫u in (0:ℝ)..q.2,r n q.1 u)
      (fun _ => 0) atTop (compactTriangle H))
    (w : ℝ→ℝ) (hw : Continuous w) :
    Tendsto (fun n => ∫u in a..(a+L),w (a+L-u)*r n (a+L) u)
      atTop (nhds 0) := by
  let t := a+L
  have ht : t∈Icc 0 H := ⟨by dsimp [t];positivity,haL⟩
  let shifted : ℕ→ℝ→ℝ→ℝ := fun n _ u => r n t (u+a)
  have hshiftRows : ∀n x,x∈Icc 0 L→IntervalIntegrable (shifted n x) volume 0 x := by
    intro n x hx
    have hi := (hrows n t ht).mono_set (show uIcc a (x+a)⊆uIcc 0 t by
      rw [uIcc_of_le (by linarith [hx.1] : a≤x+a),uIcc_of_le ht.1]
      exact Icc_subset_Icc ha (by dsimp [t];linarith [hx.2]))
    simpa only [shifted,sub_self,add_sub_cancel_right] using hi.comp_add_right a
  have hshiftVariation : ∀n x,x∈Icc 0 L→(∫u in (0:ℝ)..x,|shifted n x u|)≤K := by
    intro n x hx
    calc
      _ = ∫u in a..(x+a),|r n t u| := by
        simpa only [shifted,zero_add] using
          (intervalIntegral.integral_comp_add_right (a:=(0:ℝ)) (b:=x)
            (fun z => |r n t z|) a)
      _ ≤ ∫u in (0:ℝ)..t,|r n t u| :=
        intervalIntegral.integral_mono_interval ha (by linarith [hx.1] : a≤x+a)
          (by dsimp [t];linarith [hx.2]) (Eventually.of_forall fun _ => abs_nonneg _)
          (hrows n t ht).abs
      _ ≤ K := hvariation n t ht
  have hshiftPrimitive : TendstoUniformlyOn
      (fun n (q : ℝ×ℝ) => ∫u in (0:ℝ)..q.2,shifted n q.1 u)
      (fun _ => 0) atTop (compactTriangle L) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hprimitive) (ε/2) (by positivity)] with n hn
    intro q hq
    have hv : q.2∈Icc 0 L := ⟨hq.2.1,hq.2.2.trans hq.1.2⟩
    have h1 := hn (t,q.2+a) ⟨ht,⟨add_nonneg hv.1 ha,by dsimp [t];linarith [hv.2]⟩⟩
    have h0 := hn (t,a) ⟨ht,⟨ha,by dsimp [t];linarith⟩⟩
    have hia := (hrows n t ht).mono_set (show uIcc 0 a⊆uIcc 0 t by
      rw [uIcc_of_le ha,uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl (by dsimp [t];linarith))
    have hiv := (hrows n t ht).mono_set (show uIcc 0 (q.2+a)⊆uIcc 0 t by
      rw [uIcc_of_le (add_nonneg hv.1 ha),uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl (by dsimp [t];linarith [hv.2]))
    have hid := intervalIntegral.integral_interval_sub_left hiv hia
    change dist 0 (∫u in (0:ℝ)..q.2,r n t (u+a))<ε
    rw [intervalIntegral.integral_comp_add_right,zero_add,Real.dist_eq,zero_sub,abs_neg]
    have he : (∫u in a..(q.2+a),r n t u)=
      (∫u in (0:ℝ)..(q.2+a),r n t u)-(∫u in (0:ℝ)..a,r n t u) := by linarith
    rw [he]
    simp only [Real.dist_eq,zero_sub,abs_neg] at h1 h0
    exact (abs_sub _ _).trans_lt (by linarith)
  have hweighted := weighted_integrals_tendstoUniformlyOn hL hK shifted
    (fun q : ℝ×ℝ => w (L-q.2)) (hw.comp (continuous_const.sub continuous_snd))
    hshiftRows hshiftVariation hshiftPrimitive
  have hlimit := hweighted.tendsto_at (show L∈Icc 0 L from ⟨hL,le_rfl⟩)
  convert hlimit using 1
  funext n
  change (∫u in a..(a+L),w (a+L-u)*r n t u)=
    ∫u in (0:ℝ)..L,w (L-u)*r n t (u+a)
  calc
    _ = ∫u in (0:ℝ)..L,(fun z => w (a+L-z)*r n t z) (u+a) := by
      simpa only [zero_add,add_comm L a] using
        (intervalIntegral.integral_comp_add_right
          (a:=(0:ℝ)) (b:=L) (fun z => w (a+L-z)*r n t z) a).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u _
      congr 2
      ring

/-- The preceding response primitive convergence gives every fixed-window
continuous weighted response limit for the CK solution. -/
theorem ck_continuous_weighted_window_limit {p : ℕ} {β H a L K : ℝ}
    {d : CKSpecification.CKData} (h : CKSpecification.CKEquations p β d)
    (ha : 0≤a) (hL : 0≤L) (haL : a+L≤H) (hK : 0≤K)
    (rbar : ℕ→ℝ→ℝ→ℝ)
    (hrows : ∀n t,t∈Icc 0 H→IntervalIntegrable (rbar n t) volume 0 t)
    (hvariation : ∀n t,t∈Icc 0 H→(∫u in (0:ℝ)..t,|rbar n t u|)≤K)
    (hprimitive : TendstoUniformlyOn
      (fun n (q : ℝ×ℝ) => ∫u in (0:ℝ)..q.2,rbar n q.1 u-d.R q.1 u)
      (fun _ => 0) atTop (compactTriangle H))
    (w : ℝ→ℝ) (hw : Continuous w) :
    Tendsto (fun n => ∫u in a..(a+L),w (a+L-u)*(rbar n (a+L) u-d.R (a+L) u))
      atTop (nhds 0) := by
  have hH : 0≤H := (add_nonneg ha hL).trans haL
  have hRint (t : ℝ) (ht : t∈Icc 0 H) : IntervalIntegrable (fun u => d.R t u) volume 0 t :=
    (h.response_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ⟨hu.1,hu.2⟩)).intervalIntegrable_of_Icc ht.1
  have hdiff (n : ℕ) (t : ℝ) (ht : t∈Icc 0 H) :
      IntervalIntegrable (fun u => rbar n t u-d.R t u) volume 0 t :=
    (hrows n t ht).sub (hRint t ht)
  have hphys := CKPhysicalConsequences.physical_bounds_of_equations h
  have hRbound (t : ℝ) (ht : t∈Icc 0 H) (u : ℝ) (hu : u∈Icc 0 t) : |d.R t u|≤1 := by
    rw [abs_of_nonneg (hphys.2 t u hu.1 hu.2)]
    exact (CKPhysicalConsequences.response_le_correlation h hu.1 hu.2).trans
      (hphys.1 t u ht.1 hu.1).2
  have hdiffvar (n : ℕ) (t : ℝ) (ht : t∈Icc 0 H) :
      (∫u in (0:ℝ)..t,|rbar n t u-d.R t u|)≤K+H := by
    calc
      _ ≤ ∫u in (0:ℝ)..t,|rbar n t u|+1 := by
        apply intervalIntegral.integral_mono_on ht.1
        · exact (hdiff n t ht).abs
        · exact (hrows n t ht).abs.add intervalIntegrable_const
        · intro u hu
          exact (abs_sub _ _).trans (add_le_add le_rfl (hRbound t ht u hu))
      _ = (∫u in (0:ℝ)..t,|rbar n t u|)+t := by
        rw [intervalIntegral.integral_add (hrows n t ht).abs intervalIntegrable_const]
        simp
      _ ≤ K+H := add_le_add (hvariation n t ht) ht.2
  exact continuous_weighted_window_limit ha hL haL (add_nonneg hK hH)
    (fun n t u => rbar n t u-d.R t u) hdiff hdiffvar hprimitive w hw

end SphericalAging.SignedResponseWindowConvergence
