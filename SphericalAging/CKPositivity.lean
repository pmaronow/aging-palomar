module

public import SphericalAging.FiniteGreenCovarianceClosure
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

public section

/-!
# Positivity of the actual CK equations

A nonnegative finite prefix gives a strict integrating-factor response lower
bound. The actual Green identity then makes every correlation strictly positive.
A compact first-zero argument below upgrades this to positivity on any horizon.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology

namespace SphericalAging.CKPositivity
open CKSpecification CKLocalExistence TriangleUniqueness FiniteGreenCovarianceClosure

theorem CKOnHorizon.restrict {p : ℕ} {β T a : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (ha : 0 < a) (haT : a ≤ T) : CKOnHorizon p β a d := by
  refine ⟨h.spin_ge_three,h.beta_pos,ha,h.correlation_continuous,h.response_continuous,
    h.multiplier_continuous,h.correlation_symmetric,?_,?_,?_,?_,?_,
    h.correlation_slope_continuous,h.response_slope_continuous⟩
  · intro t ht
    exact h.correlation_diagonal t ⟨ht.1,ht.2.trans haT⟩
  · intro t ht
    exact h.response_diagonal t ⟨ht.1,ht.2.trans haT⟩
  · intro t ht
    exact h.multiplier_eq t ⟨ht.1,ht.2.trans haT⟩
  · intro t ht s hs
    exact (h.correlation_derivative t ⟨ht.1,ht.2.trans haT⟩ s hs).mono
      (fun _ hx => ⟨hx.1,hx.2.trans haT⟩)
  · intro t ht s hs
    exact (h.response_derivative t ⟨ht.1,ht.2.trans haT⟩ s hs).mono
      (fun _ hx => ⟨hx.1,hx.2.trans haT⟩)

theorem response_exponential_lower_bound {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d)
    {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
    Real.exp (-(∫ u in s..t, d.multiplier u)) ≤ d.R t s := by
  let A : ℝ → ℝ := fun x => ∫ u in s..x, d.multiplier u
  let g : ℝ → ℝ := fun x => Real.exp (A x)*d.R x s
  have hprim (x : ℝ) : HasDerivAt A (d.multiplier x) x :=
    intervalIntegral.integral_hasDerivAt_right (h.multiplier_continuous.intervalIntegrable s x)
      h.multiplier_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      h.multiplier_continuous.continuousAt
  have hA : Continuous A := continuous_iff_continuousAt.mpr (fun x => (hprim x).continuousAt)
  have hg : Continuous g := (Real.continuous_exp.comp hA).mul
    (h.response_continuous.comp (continuous_id.prodMk continuous_const))
  have hderiv {x : ℝ} (hx : x ∈ Ioo s T) :
      HasDerivAt g (Real.exp (A x)*(d.multiplier x*d.R x s+responseSlope p β d x s)) x := by
    have hd := (h.response_derivative x ⟨hs.1.trans hx.1.le,hx.2.le⟩ s ⟨hs.1,hx.1.le⟩).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
    convert ((hprim x).exp).mul hd using 1; first | rfl | ring
  have hforcing {x : ℝ} (hx : x ∈ Ioo s T) :
      0 ≤ d.multiplier x*d.R x s+responseSlope p β d x s := by
    have hxT : x ∈ Icc 0 T := ⟨hs.1.trans hx.1.le,hx.2.le⟩
    have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
    have hp1 : (1 : ℝ) ≤ p := by
      have hp := h.spin_ge_three
      exact_mod_cast (show 1 ≤ p by omega)
    have hi : 0 ≤ ∫ u in s..x, xiDoublePrime p (d.C x u)*d.R x u*d.R u s := by
      apply intervalIntegral.integral_nonneg hx.1.le
      intro u hu
      have huT : u ∈ Icc 0 T := ⟨hs.1.trans hu.1,hu.2.trans hxT.2⟩
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hp1))
          (pow_nonneg (hb.1 x hxT u huT) _)) (hb.2 x hxT u ⟨huT.1,hu.2⟩))
        (hb.2 u huT s ⟨hs.1,hu.1⟩)
    have heq : d.multiplier x*d.R x s+responseSlope p β d x s=
        β ^ 2*(∫ u in s..x, xiDoublePrime p (d.C x u)*d.R x u*d.R u s) := by
      unfold responseSlope
      ring
    rw [heq]
    exact mul_nonneg (sq_nonneg β) hi
  have hm : MonotoneOn g (Icc s T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc s T) hg.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv hx).deriv]
      exact mul_nonneg (Real.exp_pos _).le (hforcing hx)
  have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
  have hh := hm ⟨le_refl s,hsT.2⟩ ⟨hs.2,ht.2⟩ hs.2
  have hgs : g s=1 := by simp [g,A,h.response_diagonal s hsT]
  rw [hgs] at hh
  have hscaled := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-A t)).le
  have hcancel : Real.exp (-A t)*Real.exp (A t)=1 := by rw [← Real.exp_add]; simp
  change Real.exp (-A t)*1 ≤ Real.exp (-A t)*(Real.exp (A t)*d.R t s) at hscaled
  rw [← mul_assoc,hcancel,one_mul,mul_one] at hscaled
  exact hscaled

theorem response_strictly_positive_of_nonnegative {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d)
    {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) : 0 < d.R t s :=
  (Real.exp_pos _).trans_le (response_exponential_lower_bound h hb ht hs)

theorem correlation_strictly_positive_of_nonnegative {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d)
    {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) : 0 < d.C t s := by
  have hwhite : 0 ≤ ∫ u in (0 : ℝ)..min t s, d.R t u*d.R s u := by
    apply intervalIntegral.integral_nonneg (le_min ht.1 hs.1)
    intro u hu
    exact mul_nonneg (hb.2 t ht u ⟨hu.1,hu.2.trans (min_le_left _ _)⟩)
      (hb.2 s hs u ⟨hu.1,hu.2.trans (min_le_right _ _)⟩)
  have hcolored : 0 ≤ ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
      d.R t u*d.R s v*d.C u v ^ (p-1) := by
    apply intervalIntegral.integral_nonneg ht.1
    intro u hu
    apply intervalIntegral.integral_nonneg hs.1
    intro v hv
    exact mul_nonneg (mul_nonneg (hb.2 t ht u hu) (hb.2 s hs v hv))
      (pow_nonneg (hb.1 u ⟨hu.1,hu.2.trans ht.2⟩ v ⟨hv.1,hv.2.trans hs.2⟩) _)
  have hinit : 0 < d.R t 0*d.R s 0 := mul_pos
    (response_strictly_positive_of_nonnegative h hb ht ⟨le_refl 0,ht.1⟩)
    (response_strictly_positive_of_nonnegative h hb hs ⟨le_refl 0,hs.1⟩)
  rw [green_covariance_identity h ht hs]
  unfold greenCovariance
  have hcoef : 0 ≤ β ^ 2*(p : ℝ) := mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  nlinarith [mul_nonneg hcoef hcolored]

@[expose] def minimumField (d : CKData) (t s : ℝ) : ℝ := min (d.C t s) (d.R (max t s) (min t s))
@[expose] def runningMinimum (d : CKData) (t : ℝ) : ℝ :=
  sInf ((fun z : ℝ × ℝ => minimumField d (t*z.1) (t*z.2)) '' unitSquare)

theorem minimumField_continuous {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) : Continuous (Function.uncurry (minimumField d)) :=
  h.correlation_continuous.min (h.response_continuous.comp
    ((continuous_fst.max continuous_snd).prodMk (continuous_fst.min continuous_snd)))

theorem runningMinimum_continuous {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) : Continuous (runningMinimum d) :=
  unitSquare_compact.continuous_sInf
    ((minimumField_continuous h).comp ((continuous_fst.mul continuous_snd.fst).prodMk
      (continuous_fst.mul continuous_snd.snd)))

theorem runningMinimum_image_compact {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (t : ℝ) :
    IsCompact ((fun z : ℝ × ℝ => minimumField d (t*z.1) (t*z.2)) '' unitSquare) :=
  unitSquare_compact.image ((minimumField_continuous h).comp
    ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd)))

theorem runningMinimum_le_field {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) {t u v : ℝ} (ht : 0 ≤ t)
    (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 t) : runningMinimum d t ≤ minimumField d u v := by
  apply csInf_le (runningMinimum_image_compact h t).bddBelow
  by_cases hzero : t=0
  · have hu0 : u=0 := by linarith [hu.1,hu.2]
    have hv0 : v=0 := by linarith [hv.1,hv.2]
    exact ⟨(0,0),by norm_num [unitSquare],by simp [hzero,hu0,hv0]⟩
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    refine ⟨(u/t,v/t),?_,?_⟩
    · exact ⟨⟨div_nonneg hu.1 ht,(div_le_one₀ htpos).mpr hu.2⟩,
        ⟨div_nonneg hv.1 ht,(div_le_one₀ htpos).mpr hv.2⟩⟩
    · have hu' : t*(u/t)=u := by field_simp
      have hv' : t*(v/t)=v := by field_simp
      simp only [hu',hv']

theorem runningMinimum_le_correlation {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) {t u v : ℝ} (ht : 0 ≤ t)
    (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 t) : runningMinimum d t ≤ d.C u v :=
  (runningMinimum_le_field h ht hu hv).trans (min_le_left _ _)

theorem runningMinimum_le_response {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) {t u v : ℝ} (ht : 0 ≤ t)
    (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 u) : runningMinimum d t ≤ d.R u v := by
  have hh := (runningMinimum_le_field h ht hu ⟨hv.1,hv.2.trans hu.2⟩).trans (min_le_right _ _)
  simpa only [minimumField,max_eq_left hv.2,min_eq_right hv.2] using hh

theorem runningMinimum_initial {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) : runningMinimum d 0=1 := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_refl 0,h.horizon_pos.le⟩
  have hf : (fun z : ℝ × ℝ => minimumField d (0*z.1) (0*z.2))=(fun _ => (1 : ℝ)) := by
    funext z
    simp [minimumField,h.correlation_diagonal 0 h0,h.response_diagonal 0 h0]
  rw [runningMinimum,hf,unitSquare_nonempty.image_const,csInf_singleton]

theorem runningMinimum_pos_of_nonnegative {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d) : 0 < runningMinimum d T := by
  have hm := (runningMinimum_image_compact h T).sInf_mem (unitSquare_nonempty.image _)
  obtain ⟨z,hz,hval⟩ := hm
  unfold runningMinimum
  rw [← hval]
  have hu : T*z.1 ∈ Icc 0 T := ⟨mul_nonneg h.horizon_pos.le hz.1.1,
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.1.2 h.horizon_pos.le⟩
  have hv : T*z.2 ∈ Icc 0 T := ⟨mul_nonneg h.horizon_pos.le hz.2.1,
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2.2 h.horizon_pos.le⟩
  have hmax : max (T*z.1) (T*z.2) ∈ Icc 0 T :=
    ⟨hu.1.trans (le_max_left _ _),max_le hu.2 hv.2⟩
  have hmin : min (T*z.1) (T*z.2) ∈ Icc 0 (max (T*z.1) (T*z.2)) :=
    ⟨le_min hu.1 hv.1,min_le_max⟩
  exact lt_min (correlation_strictly_positive_of_nonnegative h hb hu hv)
    (response_strictly_positive_of_nonnegative h hb hmax hmin)

/-- No nonnegativity hypothesis is needed: an alleged first zero of the
continuous running square minimum would give a nonnegative prefix, on which
both fields are already proved strictly positive by their actual equations. -/
theorem ck_horizon_strictly_positive {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) :
    (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, 0 < d.C t s) ∧
      (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, 0 < d.R t s) := by
  have hmin : 0 < runningMinimum d T := by
    by_contra hfail
    have hbad : runningMinimum d T ≤ 0 := le_of_not_gt hfail
    have h0 := runningMinimum_initial h
    obtain ⟨a,ha,hma⟩ := intermediate_value_Icc' h.horizon_pos.le
      (runningMinimum_continuous h).continuousOn (show (0 : ℝ) ∈ Icc (runningMinimum d T) (runningMinimum d 0) from
        ⟨hbad,by rw [h0]; norm_num⟩)
    have haPos : 0 < a := by
      have haNe : a ≠ 0 := by intro hh; rw [hh,h0] at hma; norm_num at hma
      exact lt_of_le_of_ne ha.1 haNe.symm
    have hlocal := CKOnHorizon.restrict h haPos ha.2
    have hnon : NonnegativeOnHorizon a d := by
      constructor
      · intro t ht s hs
        have hh := runningMinimum_le_correlation h haPos.le ht hs
        rw [hma] at hh
        exact hh
      · intro t ht s hs
        have hh := runningMinimum_le_response h haPos.le ht hs
        rw [hma] at hh
        exact hh
    have hh := runningMinimum_pos_of_nonnegative hlocal hnon
    rw [hma] at hh
    exact lt_irrefl 0 hh
  constructor
  · intro t ht s hs
    exact hmin.trans_le (runningMinimum_le_correlation h h.horizon_pos.le ht hs)
  · intro t ht s hs
    exact hmin.trans_le (runningMinimum_le_response h h.horizon_pos.le ht hs)

theorem ck_horizon_nonnegative {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) : NonnegativeOnHorizon T d :=
  ⟨fun t ht s hs => (ck_horizon_strictly_positive h).1 t ht s hs |>.le,
    fun t ht s hs => (ck_horizon_strictly_positive h).2 t ht s hs |>.le⟩

end SphericalAging.CKPositivity
