module

public import SphericalAging.TriangleUniqueness
public import SphericalAging.GreenCovariance
public import SphericalAging.CKPhysicalConsequences
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

public section

/-! The signed-response primitive argument in Proposition 4.1, Step 4.
A common L¹ bound and uniform primitive convergence suffice; the signed
response need not be nonnegative or continuous. Smooth approximation is
used only for the deterministic continuous weight. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped BigOperators InnerProductSpace
namespace SphericalAging.WeightedPrimitiveConvergence
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Causal Fubini for an actual integrable rectangle, without a continuity
assumption on either signed response row. -/
theorem triangular_integral_swap_integrable {F : ℝ → ℝ → ℝ} {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t)
    (hF : IntegrableOn (Function.uncurry F) (Ioc 0 s ×ˢ Ioc 0 t)) :
    (∫ u in (0 : ℝ)..s, ∫ z in u..t, F u z) =
      ∫ z in (0 : ℝ)..t, ∫ u in (0 : ℝ)..min z s, F u z := by
  let G : ℝ → ℝ → ℝ := fun u z => if u < z then F u z else 0
  have ht : 0 ≤ t := hs.trans hst
  have hGi : IntegrableOn (Function.uncurry G) (uIoc 0 s ×ˢ uIoc 0 t) := by
    rw [uIoc_of_le hs,uIoc_of_le ht]
    exact hF.indicator (measurableSet_lt measurable_fst measurable_snd)
  have hswap := intervalIntegral_intervalIntegral_swap hGi
  calc
    _ = ∫ u in (0 : ℝ)..s, ∫ z in (0 : ℝ)..t, G u z := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hs] at hu
      exact (TriangleUniqueness.integral_strict_above hu.1 (hu.2.trans hst)).symm
    _ = ∫ z in (0 : ℝ)..t, ∫ u in (0 : ℝ)..s, G u z := hswap
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_le ht] at hz
      exact TriangleUniqueness.integral_strict_below hz.1 hs

/-- Primitive integration by parts for a merely integrable signed row,
derived from actual product integrability and triangular Fubini. -/
theorem weighted_primitive_identity {r g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hr : IntervalIntegrable r volume 0 t) (hg : ContDiff ℝ 1 g) :
    (∫ u in (0 : ℝ)..t, g u*r u) =
      g t*(∫ u in (0 : ℝ)..t,r u)-
        ∫ u in (0 : ℝ)..t, deriv g u*(∫ v in (0 : ℝ)..u,r v) := by
  have hgd : Continuous (deriv g) := hg.continuous_deriv_one
  have hFi : IntegrableOn (fun q : ℝ × ℝ => r q.1*deriv g q.2) (Ioc 0 t ×ˢ Ioc 0 t) := by
    rw [IntegrableOn,Measure.volume_eq_prod,← Measure.prod_restrict]
    exact hr.1.mul_prod ((hgd.intervalIntegrable 0 t).1)
  have hfub := triangular_integral_swap_integrable (F := fun u z => r u*deriv g z) ht le_rfl hFi
  have hleft : (∫ u in (0 : ℝ)..t, ∫ z in u..t, r u*deriv g z) =
      g t*(∫ u in (0 : ℝ)..t,r u)-(∫ u in (0 : ℝ)..t,g u*r u) := by
    calc
      _ = ∫ u in (0 : ℝ)..t, r u*(g t-g u) := by
        apply intervalIntegral.integral_congr
        intro u _
        dsimp only
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun x _ => (hg.differentiable (by norm_num) x).hasDerivAt)
            (hgd.intervalIntegrable u t)]
      _ = _ := by
        simp_rw [mul_sub,mul_comm (r _) (g t),mul_comm (r _) (g _)]
        rw [intervalIntegral.integral_sub (hr.const_mul _) (hr.continuousOn_mul hg.continuous.continuousOn),
          intervalIntegral.integral_const_mul]
  have hright : (∫ z in (0 : ℝ)..t, ∫ u in (0 : ℝ)..min z t, r u*deriv g z)=
      ∫ z in (0 : ℝ)..t, deriv g z*(∫ u in (0 : ℝ)..z,r u) := by
    apply intervalIntegral.integral_congr
    intro z hz
    dsimp only
    rw [uIcc_of_le ht] at hz
    rw [min_eq_left hz.2,intervalIntegral.integral_mul_const,mul_comm]
  rw [hleft,hright] at hfub
  linarith

/-- A direct norm bound in terms of the signed row's actual primitive. -/
theorem weighted_primitive_bound {r g : ℝ → ℝ} {t B η : ℝ}
    (ht : 0 ≤ t) (hr : IntervalIntegrable r volume 0 t) (hg : ContDiff ℝ 1 g)
    (hB : 0 ≤ B) (hη : 0 ≤ η) (hderiv : ∀ u ∈ Icc 0 t, |deriv g u| ≤ B)
    (hprim : ∀ u ∈ Icc 0 t, |∫ v in (0 : ℝ)..u,r v| ≤ η) :
    |∫ u in (0 : ℝ)..t,g u*r u| ≤ (|g t|+t*B)*η := by
  rw [weighted_primitive_identity ht hr hg]
  calc
    _ ≤ |g t*(∫ u in (0 : ℝ)..t,r u)|+
      |∫ u in (0 : ℝ)..t,deriv g u*(∫ v in (0 : ℝ)..u,r v)| := abs_sub _ _
    _ ≤ |g t| *η+(B*η)*t := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hprim t ⟨ht,le_rfl⟩) (abs_nonneg _)
      · have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
          (C := B*η) (f := fun u => deriv g u*(∫ v in (0 : ℝ)..u,r v)) (fun u hu => ?_)
        · simpa only [Real.norm_eq_abs,sub_zero,abs_of_nonneg ht] using hi
        · rw [uIoc_of_le ht] at hu
          rw [Real.norm_eq_abs,abs_mul]
          exact mul_le_mul (hderiv u ⟨hu.1.le,hu.2⟩) (hprim u ⟨hu.1.le,hu.2⟩) (abs_nonneg _) hB
    _ = _ := by ring

/-- The causal compact triangle on which response primitives converge. -/
@[expose] def compactTriangle (T : ℝ) : Set (ℝ × ℝ) := {q | q.1 ∈ Icc 0 T ∧ q.2 ∈ Icc 0 q.1}

lemma smooth_row_deriv {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (t u : ℝ) :
    deriv (fun v => g (t,v)) u=fderiv ℝ g (t,u) (0,1) := by
  exact ((hg.differentiable (by simp) (t,u)).hasFDerivAt.comp_hasDerivAt u
    ((hasDerivAt_const u t).prodMk (hasDerivAt_id u))).deriv

lemma smooth_row_deriv_continuous {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Continuous (fun q : ℝ × ℝ => deriv (fun v => g (q.1,v)) q.2) := by
  simp_rw [smooth_row_deriv hg]
  exact (hg.continuous_fderiv (by simp)).clm_apply continuous_const

/-- Uniformly convergent actual signed primitives and a common total
variation bound imply uniform convergence against every continuous weight.
Rows are merely L¹: no sign or continuity of response is assumed. -/
theorem weighted_integrals_tendstoUniformlyOn {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (r : ℕ → ℝ → ℝ → ℝ) (w : ℝ × ℝ → ℝ) (hw : Continuous w)
    (hrows : ∀ n t, t ∈ Icc 0 T → IntervalIntegrable (r n t) volume 0 t)
    (hvariation : ∀ n t, t ∈ Icc 0 T → (∫ u in (0 : ℝ)..t, |r n t u|) ≤ K)
    (hprimitive : TendstoUniformlyOn (fun n (q : ℝ × ℝ) => ∫ u in (0 : ℝ)..q.2,r n q.1 u)
      (fun _ => 0) atTop (compactTriangle T)) :
    TendstoUniformlyOn (fun n t => ∫ u in (0 : ℝ)..t,w (t,u)*r n t u)
      (fun _ => 0) atTop (Icc 0 T) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε/(2*(K+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨g,hg,happrox,-⟩ := hw.exists_contDiff_approx ⊤
    (continuous_const : Continuous (fun _ : ℝ × ℝ => δ)) (fun _ => hδ)
  obtain ⟨W₀,hW₀⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hg.continuous.abs.continuousOn
    (K := Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T)
  obtain ⟨B₀,hB₀⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (smooth_row_deriv_continuous hg).abs.continuousOn
    (K := Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T)
  let W := max W₀ 0
  let B := max B₀ 0
  have hW : 0 ≤ W := le_max_right _ _
  have hB : 0 ≤ B := le_max_right _ _
  let L := W+T*B+1
  have hL : 0 < L := by dsimp [L]; positivity
  let η := ε/(2*L)
  have hη : 0 < η := by dsimp [η]; positivity
  have hev := (Metric.tendstoUniformlyOn_iff.mp hprimitive) η hη
  filter_upwards [hev] with n hn
  intro t ht
  have hr := hrows n t ht
  have hprim : ∀ u ∈ Icc 0 t, |∫ v in (0 : ℝ)..u,r n t v| ≤ η := by
    intro u hu
    have hh := hn (t,u) ⟨ht,hu⟩
    simpa only [Real.dist_eq,zero_sub,abs_neg] using hh.le
  have hgt : |g (t,t)| ≤ W :=
    (hW₀ ⟨(t,t),⟨ht,ht⟩,rfl⟩).trans (le_max_left _ _)
  have hderiv : ∀ u ∈ Icc 0 t, |deriv (fun v => g (t,v)) u| ≤ B := by
    intro u hu
    exact (hB₀ ⟨(t,u),⟨ht,⟨hu.1,hu.2.trans ht.2⟩⟩,rfl⟩).trans (le_max_left _ _)
  have hrowg : ContDiff ℝ 1 (fun u => g (t,u)) :=
    (hg.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hsmooth := weighted_primitive_bound ht.1 hr hrowg hB hη.le hderiv hprim
  have hsmooth' : |∫ u in (0 : ℝ)..t,g (t,u)*r n t u| ≤ (W+T*B)*η := by
    exact hsmooth.trans (mul_le_mul_of_nonneg_right (by gcongr; exact ht.2) hη.le)
  have herror : |∫ u in (0 : ℝ)..t,(w (t,u)-g (t,u))*r n t u| ≤ δ*K := by
    have hnorm : ‖∫ u in (0 : ℝ)..t,(w (t,u)-g (t,u))*r n t u‖ ≤
        ∫ u in (0 : ℝ)..t,δ*|r n t u| := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht.1
      · exact .of_forall (fun u _ => by
          rw [Real.norm_eq_abs,abs_mul]
          have ha : |w (t,u)-g (t,u)| ≤ δ := by
            simpa only [Real.dist_eq,abs_sub_comm] using (happrox (t,u)).le
          exact mul_le_mul_of_nonneg_right ha (abs_nonneg _))
      · simpa only [Real.norm_eq_abs] using hr.norm.const_mul δ
    rw [intervalIntegral.integral_const_mul,Real.norm_eq_abs] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_left (hvariation n t ht) hδ.le)
  have hsplit : (∫ u in (0 : ℝ)..t,w (t,u)*r n t u)=
      (∫ u in (0 : ℝ)..t,(w (t,u)-g (t,u))*r n t u)+
        (∫ u in (0 : ℝ)..t,g (t,u)*r n t u) := by
    rw [← intervalIntegral.integral_add]
    · apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      ring
    · exact hr.continuousOn_mul
        (((hw.comp (continuous_const.prodMk continuous_id)).sub hrowg.continuous).continuousOn)
    · exact hr.continuousOn_mul hrowg.continuous.continuousOn
  rw [Real.dist_eq,zero_sub,abs_neg,hsplit]
  have hδK : δ*K < ε/2 := by
    have he : δ*(K+1)=ε/2 := by
      dsimp only [δ]
      field_simp
    rw [← he]
    exact mul_lt_mul_of_pos_left (by linarith) hδ
  have hηL : (W+T*B)*η < ε/2 := by
    dsimp only [η]
    have hWL : W+T*B < L := by dsimp only [L]; linarith
    have hh := mul_lt_mul_of_pos_right hWL hη
    have he : L*η=ε/2 := by dsimp only [η]; field_simp
    rw [he] at hh
    exact hh
  exact (abs_add_le _ _).trans_lt ((add_le_add herror hsmooth').trans_lt (by linarith))

/-- The response primitives in Section 3.5 are tails. They yield the prefix
primitive convergence used in Proposition 4.1 by subtracting two actual
integrals; no positivity is needed. -/
theorem prefix_primitives_of_tail_primitives {T : ℝ} (r : ℕ → ℝ → ℝ → ℝ)
    (hrows : ∀ n t, t ∈ Icc 0 T → IntervalIntegrable (r n t) volume 0 t)
    (htail : TendstoUniformlyOn (fun n (q : ℝ × ℝ) => ∫ u in q.2..q.1,r n q.1 u)
      (fun _ => 0) atTop (compactTriangle T)) :
    TendstoUniformlyOn (fun n (q : ℝ × ℝ) => ∫ u in (0 : ℝ)..q.2,r n q.1 u)
      (fun _ => 0) atTop (compactTriangle T) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp htail) (ε/2) (by positivity)] with n hn
  intro q hq
  have h0 := hn (q.1,0) ⟨hq.1,⟨le_refl 0,hq.1.1⟩⟩
  have hs := hn q hq
  have hr := hrows n q.1 hq.1
  have hrs : IntervalIntegrable (r n q.1) volume 0 q.2 := hr.mono_set (by
    rw [uIcc_of_le hq.1.1,uIcc_of_le hq.2.1]
    exact Icc_subset_Icc le_rfl hq.2.2)
  have hid := intervalIntegral.integral_interval_sub_left hr hrs
  have hab : |∫ u in (0 : ℝ)..q.2,r n q.1 u| ≤
      |∫ u in (0 : ℝ)..q.1,r n q.1 u|+|∫ u in q.2..q.1,r n q.1 u| := by
    rw [show (∫ u in (0 : ℝ)..q.2,r n q.1 u)=
      (∫ u in (0 : ℝ)..q.1,r n q.1 u)-(∫ u in q.2..q.1,r n q.1 u) by linarith]
    exact abs_sub _ _
  simp only [Real.dist_eq,zero_sub,abs_neg] at h0 hs ⊢
  exact hab.trans_lt (by linarith)

/-- Source Proposition 4.1, Step 4: the actual CK correlation weight
against a signed annealed-response error. The inputs are precisely
uniform primitive convergence and the response total variation bound. -/
theorem ck_weighted_response_limit {p : ℕ} {β T K : ℝ} {d : CKSpecification.CKData}
    (h : CKSpecification.CKEquations p β d) (hT : 0 ≤ T) (hK : 0 ≤ K)
    (rbar : ℕ → ℝ → ℝ → ℝ)
    (hrows : ∀ n t, t ∈ Icc 0 T → IntervalIntegrable (rbar n t) volume 0 t)
    (hvariation : ∀ n t, t ∈ Icc 0 T → (∫ u in (0 : ℝ)..t, |rbar n t u|) ≤ K)
    (hprimitive : TendstoUniformlyOn
      (fun n (q : ℝ × ℝ) => ∫ u in (0 : ℝ)..q.2,rbar n q.1 u-d.R q.1 u)
      (fun _ => 0) atTop (compactTriangle T)) :
    TendstoUniformlyOn (fun n t =>
      ∫ u in (0 : ℝ)..t,(d.C t u)^(p-1)*(rbar n t u-d.R t u))
      (fun _ => 0) atTop (Icc 0 T) := by
  have hRcont (t : ℝ) (ht : t ∈ Icc 0 T) : ContinuousOn (fun u => d.R t u) (Icc 0 t) := by
    exact h.response_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ⟨hu.1,hu.2⟩)
  have hRint (t : ℝ) (ht : t ∈ Icc 0 T) : IntervalIntegrable (fun u => d.R t u) volume 0 t :=
    (hRcont t ht).intervalIntegrable_of_Icc ht.1
  have hdiff (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
      IntervalIntegrable (fun u => rbar n t u-d.R t u) volume 0 t :=
    (hrows n t ht).sub (hRint t ht)
  have hphysical := CKPhysicalConsequences.physical_bounds_of_equations h
  have hRbound (t : ℝ) (ht : t ∈ Icc 0 T) (u : ℝ) (hu : u ∈ Icc 0 t) : |d.R t u| ≤ 1 := by
    have hnonneg := hphysical.2 t u hu.1 hu.2
    rw [abs_of_nonneg hnonneg]
    exact (CKPhysicalConsequences.response_le_correlation h hu.1 hu.2).trans
      (hphysical.1 t u ht.1 hu.1).2
  have hdiffvar (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
      (∫ u in (0 : ℝ)..t, |rbar n t u-d.R t u|) ≤ K+T := by
    calc
      _ ≤ ∫ u in (0 : ℝ)..t, |rbar n t u|+1 := by
        apply intervalIntegral.integral_mono_on ht.1
        · simpa only [Real.norm_eq_abs] using (hdiff n t ht).norm
        · exact (hrows n t ht).norm.add intervalIntegrable_const
        · intro u hu
          exact (abs_sub _ _).trans (add_le_add le_rfl (hRbound t ht u hu))
      _ = (∫ u in (0 : ℝ)..t, |rbar n t u|)+t := by
        rw [intervalIntegral.integral_add]
        · simp
        · simpa only [Real.norm_eq_abs] using (hrows n t ht).norm
        · exact intervalIntegrable_const
      _ ≤ K+T := add_le_add (hvariation n t ht) ht.2
  have hlimit := weighted_integrals_tendstoUniformlyOn hT (add_nonneg hK hT)
    (fun n t u => rbar n t u-d.R t u)
    (fun q : ℝ × ℝ => (GreenCovariance.clampedCorrelation d q.1 q.2)^(p-1))
    ((GreenCovariance.clampedCorrelation_continuous h).pow (p-1)) hdiff hdiffvar hprimitive
  apply hlimit.congr
  exact .of_forall (fun n t ht => by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [uIcc_of_le ht.1] at hu
    rw [GreenCovariance.clampedCorrelation_eq ht.1 hu.1])

end SphericalAging.WeightedPrimitiveConvergence
