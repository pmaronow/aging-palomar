module

public import SphericalAging.KeyRenewal
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

public section

/-! Genuine source first-moment and nonarithmetic prerequisites. The full
finite-mean key renewal theorem remains a separate theorem: these results
never replace a finite-mean assumption by a second-moment assumption. -/
open Set Filter MeasureTheory ProbabilityTheory Asymptotics
open scoped Topology ENNReal
namespace SphericalAging.RenewalFirstMoment
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's arithmetic definition, literally positive natural
multiples of some positive span. -/
@[expose] def Arithmetic (μ : Measure ℝ) : Prop :=
  ∃ h : ℝ,0<h ∧ μ {x : ℝ | ∃ n : ℕ,0<n ∧ x=(n:ℝ)*h}=1

/-- Equality of a characteristic function to one forces concentration on the
untranslated lattice, without any moment assumption. -/
theorem ae_lattice_of_charFun_eq_one {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {t : ℝ} (ht : t≠0) (h : charFun μ t=1) :
    ∀ᵐ x ∂μ,∃ k : ℤ,x=k*(2*Real.pi/t) := by
  have hint : Integrable (fun x : ℝ => Complex.exp (t * x * Complex.I)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    have : ((t : ℂ) * x * Complex.I) = ((t * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hcos : Integrable (fun x : ℝ => Real.cos (t * x)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    simpa using Real.abs_cos_le_one (t * x)
  -- The real part of the defining integral of `charFun`.
  have hre : ∫ x, Real.cos (t * x) ∂μ = 1 := by
    have h1 : ∫ x, ((Complex.exp ((t : ℂ) * x * Complex.I)).re) ∂μ = (charFun μ t).re := by
      rw [charFun_apply_real, ← Complex.reCLM_apply,
        ← ContinuousLinearMap.integral_comp_comm _ hint]
      rfl
    have h2 : ∀ x : ℝ, (Complex.exp ((t : ℂ) * x * Complex.I)).re = Real.cos (t * x) := by
      intro x
      have : ((t : ℂ) * x * Complex.I) = ((t * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.exp_ofReal_mul_I_re]
    simp only [h2] at h1
    rw [h1, h]
    simp
  have key : ∫ x, (1 - Real.cos (t * x)) ∂μ = 0 := by
    rw [integral_sub (integrable_const 1) hcos, hre]
    simp
  have hae : ∀ᵐ x ∂μ, Real.cos (t * x) = 1 := by
    have hnn : 0 ≤ᵐ[μ] fun x => 1 - Real.cos (t * x) :=
      Filter.Eventually.of_forall fun x => by simpa using Real.cos_le_one (t * x)
    have := (integral_eq_zero_iff_of_nonneg_ae hnn ((integrable_const 1).sub hcos)).mp key
    filter_upwards [this] with x hx
    simp only [Pi.zero_apply] at hx
    linarith
  -- Hence `μ` is carried by the lattice `(2π/t) ℤ`.
  have hsub : ∀ᵐ x ∂μ,∃ k : ℤ,x=k*(2*Real.pi/t) := by
    filter_upwards [hae] with x hx
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (t * x)).mp hx
    exact ⟨n, by field_simp; linarith [hn]⟩
  exact hsub

/-- A positive-increment source nonarithmetic law has no nonzero Fourier
frequency at which its characteristic function equals one. This requires
source nonarithmeticity, not the stronger translated-lattice exclusion. -/
theorem charFun_ne_one_of_positive_nonarithmetic {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpositive : ∀ᵐ x ∂μ,0<x) (hnot : ¬Arithmetic μ) {t : ℝ} (ht : t≠0) :
    charFun μ t≠1 := by
  intro hchar
  let h : ℝ := 2*Real.pi/|t|
  have hspan : 0<h := div_pos (by positivity) (abs_pos.mpr ht)
  have hlattice := ae_lattice_of_charFun_eq_one ht hchar
  have hsupport : ∀ᵐ x ∂μ,∃ n : ℕ,0<n ∧ x=(n:ℝ)*h := by
    filter_upwards [hpositive,hlattice] with x hx hxl
    obtain ⟨k,hk⟩ := hxl
    have hbase : ∃ j : ℤ,x=(j:ℝ)*h := by
      rcases lt_or_gt_of_ne ht with htneg|htpos
      · refine ⟨-k,?_⟩
        dsimp [h]
        rw [abs_of_neg htneg]
        push_cast
        rw [hk]
        field_simp
      · refine ⟨k,?_⟩
        simpa only [h,abs_of_pos htpos] using hk
    obtain ⟨j,hj⟩ := hbase
    have hjpos : 0<(j:ℝ) := by nlinarith [hspan]
    have hjint : 0<j := by exact_mod_cast hjpos
    have hjnat : ((j.toNat:ℕ):ℝ)=(j:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hjint.le
    refine ⟨j.toNat,?_,?_⟩
    · have hnat : (0:ℝ)<(j.toNat:ℝ) := by rw [hjnat];exact hjpos
      exact_mod_cast hnat
    · rw [hjnat]
      exact hj
  have hcount : {x : ℝ | ∃ n : ℕ,0<n ∧ x=(n:ℝ)*h}.Countable := by
    apply (countable_range (fun n : ℕ => (n:ℝ)*h)).mono
    rintro x ⟨n,hn,hx⟩
    exact ⟨n,hx.symm⟩
  exact hnot ⟨h,hspan,(prob_compl_eq_zero_iff hcount.measurableSet).mp (ae_iff.mp hsupport)⟩

/-- Strictly positive increments with a finite first moment have a genuinely
positive finite mean. -/
theorem mean_positive_of_positive_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpositive : ∀ᵐ x ∂μ,0<x) (hi : Integrable id μ) : 0<∫ x : ℝ,x ∂μ := by
  have hnn : 0≤ᵐ[μ] (fun x : ℝ => x) := hpositive.mono fun x hx => hx.le
  have hne : ¬(fun x : ℝ => x)=ᵐ[μ] 0 := by
    intro hz
    have hfalse : ∀ᵐ x ∂μ,False := by
      filter_upwards [hz,hpositive] with x hx hxp
      simpa only [Pi.zero_apply,hx,lt_self_iff_false] using hxp
    have hbad : (1:ℝ≥0∞)=0 := by simpa using ae_iff.mp hfalse
    exact one_ne_zero hbad
  have hnzero : (∫ x : ℝ,x ∂μ)≠0 := by
    intro hz
    exact hne ((integral_eq_zero_iff_of_nonneg_ae hnn hi).mp hz)
  exact lt_of_le_of_ne (integral_nonneg_of_ae hnn) hnzero.symm

/-- Actual first-order characteristic expansion under only a finite first
moment. The error is o(t); no O(t^2) estimate is asserted. -/
theorem charFun_first_order {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable id μ) :
    (fun t : ℝ => charFun μ t-(1+((∫ x : ℝ,x ∂μ : ℝ):ℂ)*t*Complex.I))
      =o[𝓝 0] (fun t : ℝ => t) := by
  have hint : MemLp id ((1:ℕ):ℝ≥0∞) μ := by simpa using memLp_one_iff_integrable.mpr hi
  have h := taylor_isLittleO_univ (f:=charFun μ) (x₀:=(0:ℝ)) (n:=1) (contDiff_charFun hint)
  simp only [sub_zero,pow_one] at h
  refine h.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards with t
  rw [taylorWithinEval_charFun_zero hint t]
  simp [Finset.sum_range_succ]
  ring

/-- The simple-zero lower bound genuinely needs only a finite first moment. -/
theorem first_moment_simple_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable id μ) (hm : 0<∫ x : ℝ,x ∂μ) :
    ∃ δ : ℝ,0<δ ∧ ∀ t : ℝ,|t|≤δ →
      (∫ x : ℝ,x ∂μ)/2*|t|≤‖1-charFun μ t‖ := by
  let m : ℝ := ∫ x : ℝ,x ∂μ
  obtain ⟨ε,hε,hbound⟩ := Metric.eventually_nhds_iff.mp
    ((charFun_first_order hi).def (by dsimp [m];linarith : 0<m/2))
  refine ⟨ε/2,by linarith,?_⟩
  intro t ht
  have hd : dist t 0<ε := by rw [Real.dist_eq,sub_zero];linarith [abs_nonneg t]
  have hb := hbound hd
  have hmt : ‖(m:ℂ)*(t:ℂ)*Complex.I‖=m*|t| := by simp [abs_of_pos hm,m]
  have hB : ‖(m:ℂ)*(t:ℂ)*Complex.I‖≤
      ‖charFun μ t-(1+(m:ℂ)*t*Complex.I)‖+‖1-charFun μ t‖ := by
    calc
      _=‖-(charFun μ t-(1+(m:ℂ)*t*Complex.I))-(1-charFun μ t)‖ := by congr 1;ring
      _≤_ := by
        simpa only [norm_neg] using (norm_sub_le
          (-(charFun μ t-(1+(m:ℂ)*t*Complex.I))) (1-charFun μ t))
  rw [hmt] at hB
  have hb' : ‖charFun μ t-(1+(m:ℂ)*t*Complex.I)‖≤m/2*|t| := by
    simpa only [integral_complex_ofReal,Real.norm_eq_abs] using hb
  change m/2*|t|≤‖1-charFun μ t‖
  linarith

/-- Source nonarithmeticity gives the true compact-annulus resolvent bound,
without a translated-lattice or moment premise. -/
theorem positive_nonarithmetic_annulus_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpositive : ∀ᵐ x ∂μ,0<x) (hnot : ¬Arithmetic μ) {δ : ℝ} (hδ : 0<δ) (T : ℝ) :
    ∃ c : ℝ,0<c ∧ ∀t : ℝ,|t|≤T → δ≤|t| → c≤‖1-charFun μ t‖ := by
  let K : Set ℝ := Icc (-T) T∩{t : ℝ | δ≤|t|}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hc : Continuous (fun t : ℝ => ‖1-charFun μ t‖) :=
    (continuous_const.sub continuous_charFun).norm
  rcases K.eq_empty_or_nonempty with he|hn
  · refine ⟨1,one_pos,?_⟩
    intro t ht hd
    have hm : t∈K := ⟨abs_le.mp ht,hd⟩
    rw [he] at hm
    exact hm.elim
  · obtain ⟨t,ht,hm⟩ := hK.exists_isMinOn hn hc.continuousOn
    have ht0 : t≠0 := by
      intro ht0
      have hd := ht.2
      change δ≤|t| at hd
      rw [ht0,abs_zero] at hd
      linarith
    have hp : 0<‖1-charFun μ t‖ := by
      rw [norm_pos_iff,sub_ne_zero]
      exact fun h => charFun_ne_one_of_positive_nonarithmetic hpositive hnot ht0 h.symm
    exact ⟨‖1-charFun μ t‖,hp,fun u hu hd => hm (show u∈K from ⟨abs_le.mp hu,hd⟩)⟩

end
end SphericalAging.RenewalFirstMoment
