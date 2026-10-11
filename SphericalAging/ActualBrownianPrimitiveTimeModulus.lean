module

public import SphericalAging.BrownianVectorMoments
public import SphericalAging.ActualOverlapTimeModulus
public import SphericalAging.ResponseTraceReplacement

public section

/-! Actual Brownian primitive uniform integrability and quantitative
time increments under the literal Gaussian × sphere × Wiener law. The
terminal-time estimate uses the true physical increment second moment,
sphere boundedness, and actual Brownian fourth moments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualBrownianPrimitiveTimeModulus
open HardSphereDynamics ActualStateIncrementMoments BrownianVectorMoments
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def actualBrownian (s : ℝ≥0) (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : State N :=
  brownianVector s ω.2

@[expose] def actualGamma (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t s : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : ℝ :=
  ⟪actualState β R hR t ω,actualBrownian s ω⟫_ℝ/(Real.sqrt 2*(N : ℝ))

theorem actualBrownian_memLp (s : ℝ≥0) {q : ℝ≥0∞} (hq : q≠⊤) :
    MemLp (actualBrownian (N := N) (p := p) s) q (AnnealedModelLaw.law N p) :=
  (brownianVector_memLp s hq).comp_measurePreserving
    (measurePreserving_snd (μ := AnnealedModelLaw.parameterLaw N p) (ν := VectorBrownian.law N))

theorem actualBrownian_secondMoment (s : ℝ≥0) :
    (∫ ω,‖actualBrownian (N := N) (p := p) s ω‖^2 ∂AnnealedModelLaw.law N p)=(N : ℝ)*s := by
  simp only [actualBrownian,AnnealedModelLaw.law]
  rw [integral_fun_snd (μ := AnnealedModelLaw.parameterLaw N p) (ν := VectorBrownian.law N)
    (fun ω => ‖brownianVector s ω‖^2)]
  simp only [probReal_univ,one_smul,brownianVector_secondMoment]

theorem actualBrownian_fourthMoment_le (s : ℝ≥0) :
    (∫ ω,‖actualBrownian (N := N) (p := p) s ω‖^4 ∂AnnealedModelLaw.law N p)≤3*(N : ℝ)^2*(s : ℝ)^2 := by
  simp only [actualBrownian,AnnealedModelLaw.law]
  rw [integral_fun_snd (μ := AnnealedModelLaw.parameterLaw N p) (ν := VectorBrownian.law N)
    (fun ω => ‖brownianVector s ω‖^4)]
  simpa only [probReal_univ,one_smul] using brownianVector_fourthMoment_le (N := N) s

theorem actualBrownian_increment_secondMoment (s u : ℝ≥0) :
    (∫ ω,‖actualBrownian (N := N) (p := p) (s+u) ω-actualBrownian s ω‖^2
      ∂AnnealedModelLaw.law N p)=(N : ℝ)*u := by
  simp only [actualBrownian,AnnealedModelLaw.law]
  rw [integral_fun_snd (μ := AnnealedModelLaw.parameterLaw N p) (ν := VectorBrownian.law N)
    (fun ω => ‖brownianVector (s+u) ω-brownianVector s ω‖^2)]
  simp only [probReal_univ,one_smul,brownianVector_increment_secondMoment]

theorem inner_square_le (x y : State N) : ⟪x,y⟫_ℝ^2≤‖x‖^2*‖y‖^2 := by
  have hh := (sq_le_sq₀ (abs_nonneg ⟪x,y⟫_ℝ)
    (mul_nonneg (norm_nonneg x) (norm_nonneg y))).mpr (norm_inner_le_norm (𝕜 := ℝ) x y)
  simpa only [sq_abs,mul_pow] using hh

theorem sphere_pairing_square_le (hN : 0<N) (x y : State N) (hx : OnSphere x) :
    (⟪x,y⟫_ℝ/(Real.sqrt 2*(N : ℝ)))^2≤‖y‖^2/(2*(N : ℝ)) := by
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  calc
    _≤((N : ℝ)*‖y‖^2)/(2*(N : ℝ)^2) :=
      div_le_div_of_nonneg_right (by simpa only [(onSphere_iff_norm_sq x).mp hx] using inner_square_le x y) (by positivity)
    _=_ := by field_simp

theorem actualGamma_memLp_two (hN : 1≤N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (t s : ℝ≥0) :
    MemLp (actualGamma (p := p) β R hR t s) 2 (AnnealedModelLaw.law N p) := by
  have hB := actualBrownian_memLp (N := N) (p := p) s (q := 2) (by norm_num)
  have hm := ((actualState_memLp (p := p) hN β R hR hNR t).aestronglyMeasurable.inner (𝕜 := ℝ)
    hB.aestronglyMeasurable)
  let K : ℝ := Real.sqrt N/(Real.sqrt 2*(N : ℝ))
  apply (hB.norm.const_mul K).mono'
    ((continuous_id.div_const (Real.sqrt 2*(N : ℝ))).comp_aestronglyMeasurable hm)
  filter_upwards [actualState_onSphere hN β R hR hNR] with ω hω
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr (by omega : 0<N)
  have hd : 0<Real.sqrt 2*(N : ℝ) := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hn
  change |actualGamma β R hR t s ω|≤K*‖actualBrownian s ω‖
  rw [actualGamma,abs_div,abs_of_pos hd]
  calc
    _≤(Real.sqrt N*‖actualBrownian s ω‖)/(Real.sqrt 2*(N : ℝ)) := by
      apply div_le_div_of_nonneg_right _ hd.le
      have hh := norm_inner_le_norm (𝕜 := ℝ) (actualState β R hR t ω) (actualBrownian s ω)
      rw [LandscapeDerivatives.sphere_norm _ ((onSphere_iff_norm_sq _).mp (hω t))] at hh
      exact hh
    _=_ := by dsimp only [K];ring

/-- The actual Γ_N observable is uniformly square-integrable on every
fixed time triangle, with the exact sphere/Cauchy--Schwarz ceiling s/2. -/
theorem actualGamma_secondMoment_le (hN : 1≤N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (t s : ℝ≥0) :
    (∫ ω,(actualGamma (p := p) β R hR t s ω)^2 ∂AnnealedModelLaw.law N p)≤(s : ℝ)/2 := by
  calc
    _≤∫ ω,‖actualBrownian (N := N) (p := p) s ω‖^2/(2*(N : ℝ)) ∂AnnealedModelLaw.law N p := by
      apply integral_mono_ae (actualGamma_memLp_two hN β R hR hNR t s).integrable_sq
        ((actualBrownian_memLp s (q := 2) (by norm_num)).integrable_norm_pow'.div_const _)
      filter_upwards [actualState_onSphere hN β R hR hNR] with ω hω
      exact sphere_pairing_square_le (by omega : 0<N) _ _ (hω t)
    _=(s : ℝ)/2 := by
      rw [integral_div,actualBrownian_secondMoment]
      field_simp

theorem actualGamma_prefix_time_secondMoment (hN : 1≤N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (t s u : ℝ≥0) :
    (∫ ω,(actualGamma (p := p) β R hR t (s+u) ω-actualGamma β R hR t s ω)^2
      ∂AnnealedModelLaw.law N p)≤(u : ℝ)/2 := by
  have hG := (actualGamma_memLp_two (p := p) hN β R hR hNR t (s+u)).sub
    (actualGamma_memLp_two (p := p) hN β R hR hNR t s)
  have hB := (actualBrownian_memLp (N := N) (p := p) (s+u) (q := 2) (by norm_num)).sub
    (actualBrownian_memLp s (q := 2) (by norm_num))
  calc
    _≤∫ ω,‖actualBrownian (N := N) (p := p) (s+u) ω-actualBrownian s ω‖^2/(2*(N : ℝ))
        ∂AnnealedModelLaw.law N p := by
      apply integral_mono_ae hG.integrable_sq (hB.integrable_norm_pow'.div_const _)
      filter_upwards [actualState_onSphere hN β R hR hNR] with ω hω
      change (⟪actualState β R hR t ω,actualBrownian (s+u) ω⟫_ℝ/(Real.sqrt 2*(N : ℝ))-
        ⟪actualState β R hR t ω,actualBrownian s ω⟫_ℝ/(Real.sqrt 2*(N : ℝ)))^2≤_
      rw [← sub_div,← inner_sub_right]
      exact sphere_pairing_square_le (by omega : 0<N) _ _ (hω t)
    _=(u : ℝ)/2 := by
      rw [integral_div,actualBrownian_increment_secondMoment]
      field_simp

theorem actualStateIncrement_memLp_four (hN : 1≤N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (t u : ℝ≥0) :
    MemLp (fun ω => actualState (p := p) β R hR (t+u) ω-actualState β R hR t ω) 4
      (AnnealedModelLaw.law N p) := by
  apply MemLp.of_bound ((actualState_memLp (p := p) hN β R hR hNR (t+u)).aestronglyMeasurable.sub
    (actualState_memLp hN β R hR hNR t).aestronglyMeasurable) (2*Real.sqrt N)
  filter_upwards [actualState_onSphere hN β R hR hNR] with ω hω
  have hh := norm_sub_le (actualState β R hR (t+u) ω) (actualState β R hR t ω)
  rw [LandscapeDerivatives.sphere_norm _ ((onSphere_iff_norm_sq _).mp (hω (t+u))),
    LandscapeDerivatives.sphere_norm _ ((onSphere_iff_norm_sq _).mp (hω t))] at hh
  exact hh.trans_eq (by ring)

theorem actualStateIncrement_fourthMoment_le (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (t u : ℝ≥0) :
    (∫ ω,‖actualState (p := p) β R hR (t+u) ω-actualState β R hR t ω‖^4
      ∂AnnealedModelLaw.law N p)≤4*(N : ℝ)^2*incrementCeiling p β u := by
  have h2 := (actualState_memLp (p := p) hN β R hR hNR (t+u)).sub
    (actualState_memLp hN β R hR hNR t)
  have h4 := actualStateIncrement_memLp_four (p := p) hN β R hR hNR t u
  have hh := (div_le_iff₀ (Nat.cast_pos.mpr (by omega : 0<N))).mp
    (actual_increment_secondMoment hN hp β R hR hNR t u)
  calc
    _≤∫ ω,4*(N : ℝ)*‖actualState (p := p) β R hR (t+u) ω-actualState β R hR t ω‖^2
        ∂AnnealedModelLaw.law N p := by
      apply integral_mono_ae h4.integrable_norm_pow' (h2.integrable_norm_pow'.const_mul _)
      filter_upwards [actualState_onSphere hN β R hR hNR] with ω hω
      have hn := norm_sub_le (actualState β R hR (t+u) ω) (actualState β R hR t ω)
      rw [LandscapeDerivatives.sphere_norm _ ((onSphere_iff_norm_sq _).mp (hω (t+u))),
        LandscapeDerivatives.sphere_norm _ ((onSphere_iff_norm_sq _).mp (hω t))] at hn
      have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤Real.sqrt (N : ℝ)+Real.sqrt N)).mpr hn
      have hroot := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
      have hsq' : ‖actualState β R hR (t+u) ω-actualState β R hR t ω‖^2≤4*(N : ℝ) := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hsq' (sq_nonneg ‖actualState β R hR (t+u) ω-actualState β R hR t ω‖)
      convert hm using 1 <;> ring
    _=4*(N : ℝ)*(∫ ω,‖actualState (p := p) β R hR (t+u) ω-actualState β R hR t ω‖^2
        ∂AnnealedModelLaw.law N p) := integral_const_mul _ _
    _≤4*(N : ℝ)^2*incrementCeiling p β u := by
      have he := mul_le_mul_of_nonneg_left hh (by positivity : 0≤4*(N : ℝ))
      convert he using 1 <;> ring

theorem actualGamma_terminal_time_secondMoment (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (t s u : ℝ≥0) :
    (∫ ω,(actualGamma (p := p) β R hR (t+u) s ω-actualGamma β R hR t s ω)^2
      ∂AnnealedModelLaw.law N p)≤Real.sqrt 3*(s : ℝ)*Real.sqrt (incrementCeiling p β u) := by
  let U := fun ω => actualState (N := N) (p := p) β R hR (t+u) ω-actualState β R hR t ω
  let V := actualBrownian (N := N) (p := p) s
  let P := AnnealedModelLaw.law N p
  have hU := actualStateIncrement_memLp_four (p := p) hN β R hR hNR t u
  have hV := actualBrownian_memLp (N := N) (p := p) s (q := 4) (by norm_num)
  have hUs : MemLp (fun ω => ‖U ω‖^2) 2 P :=
    (memLp_two_iff_integrable_sq (hU.aestronglyMeasurable.norm.pow 2)).mpr (by
      simpa only [Pi.pow_apply,← pow_mul,Nat.reduceMul] using hU.integrable_norm_pow')
  have hVs : MemLp (fun ω => ‖V ω‖^2) 2 P :=
    (memLp_two_iff_integrable_sq (hV.aestronglyMeasurable.norm.pow 2)).mpr (by
      simpa only [Pi.pow_apply,← pow_mul,Nat.reduceMul] using hV.integrable_norm_pow')
  have hProd : Integrable (fun ω => ‖U ω‖^2*‖V ω‖^2) P := hUs.integrable_mul hVs
  have hcs := ResponseTraceReplacement.integral_abs_mul_le_sqrt hUs hVs
  simp only [← pow_mul,Nat.reduceMul] at hcs
  have habs : (fun ω => |‖U ω‖^2*‖V ω‖^2|)=(fun ω => ‖U ω‖^2*‖V ω‖^2) :=
    funext (fun _ => abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  rw [habs] at hcs
  have hcap := mul_le_mul
    (Real.sqrt_le_sqrt (actualStateIncrement_fourthMoment_le hN hp β R hR hNR t u))
    (Real.sqrt_le_sqrt (actualBrownian_fourthMoment_le (N := N) (p := p) s))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr (by omega : 0<N)
  have hceil := incrementCeiling_nonneg p β u
  have hrootU : Real.sqrt (4*(N : ℝ)^2*incrementCeiling p β u)=
      2*(N : ℝ)*Real.sqrt (incrementCeiling p β u) := by
    rw [Real.sqrt_mul (by positivity : 0≤4*(N : ℝ)^2),
      Real.sqrt_mul (by norm_num : (0 : ℝ)≤4),Real.sqrt_sq hn.le]
    norm_num
  have hrootV : Real.sqrt (3*(N : ℝ)^2*(s : ℝ)^2)=Real.sqrt 3*(N : ℝ)*s := by
    rw [Real.sqrt_mul (by positivity : 0≤3*(N : ℝ)^2),
      Real.sqrt_mul (by norm_num : (0 : ℝ)≤3),Real.sqrt_sq hn.le,Real.sqrt_sq s.coe_nonneg]
  rw [hrootU,hrootV] at hcap
  have hG := (actualGamma_memLp_two (p := p) hN β R hR hNR (t+u) s).sub
    (actualGamma_memLp_two (p := p) hN β R hR hNR t s)
  calc
    _≤(∫ ω,‖U ω‖^2*‖V ω‖^2 ∂P)/(2*(N : ℝ)^2) := by
      rw [← integral_div]
      apply integral_mono_ae hG.integrable_sq (hProd.div_const _)
      filter_upwards [] with ω
      change (⟪actualState β R hR (t+u) ω,V ω⟫_ℝ/(Real.sqrt 2*(N : ℝ))-
        ⟪actualState β R hR t ω,V ω⟫_ℝ/(Real.sqrt 2*(N : ℝ)))^2≤_
      rw [← sub_div,← inner_sub_left,div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
      exact div_le_div_of_nonneg_right (inner_square_le (U ω) (V ω)) (by positivity)
    _≤(2*(N : ℝ)*Real.sqrt (incrementCeiling p β u)*(Real.sqrt 3*(N : ℝ)*s))/(2*(N : ℝ)^2) :=
      div_le_div_of_nonneg_right (hcs.trans hcap) (by positivity)
    _=_ := by field_simp

theorem actualGamma_two_time_secondMoment (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (t s u v : ℝ≥0) :
    (∫ ω,(actualGamma (p := p) β R hR (t+u) (s+v) ω-actualGamma β R hR t s ω)^2
      ∂AnnealedModelLaw.law N p)≤(v : ℝ)+2*Real.sqrt 3*(s : ℝ)*Real.sqrt (incrementCeiling p β u) := by
  let a := fun ω => actualGamma (N := N) (p := p) β R hR (t+u) (s+v) ω-actualGamma β R hR (t+u) s ω
  let b := fun ω => actualGamma (N := N) (p := p) β R hR (t+u) s ω-actualGamma β R hR t s ω
  have ha := (actualGamma_memLp_two (p := p) hN β R hR hNR (t+u) (s+v)).sub
    (actualGamma_memLp_two (p := p) hN β R hR hNR (t+u) s)
  have hb := (actualGamma_memLp_two (p := p) hN β R hR hNR (t+u) s).sub
    (actualGamma_memLp_two (p := p) hN β R hR hNR t s)
  have hw := (actualGamma_memLp_two (p := p) hN β R hR hNR (t+u) (s+v)).sub
    (actualGamma_memLp_two (p := p) hN β R hR hNR t s)
  have hai : Integrable (fun ω => (a ω)^2) (AnnealedModelLaw.law N p) := ha.integrable_sq
  have hbi : Integrable (fun ω => (b ω)^2) (AnnealedModelLaw.law N p) := hb.integrable_sq
  calc
    _≤∫ ω,2*(a ω)^2+2*(b ω)^2 ∂AnnealedModelLaw.law N p := by
      apply integral_mono hw.integrable_sq ((hai.const_mul 2).add (hbi.const_mul 2))
      intro ω
      change (actualGamma β R hR (t+u) (s+v) ω-actualGamma β R hR t s ω)^2≤
        2*(actualGamma β R hR (t+u) (s+v) ω-actualGamma β R hR (t+u) s ω)^2+
          2*(actualGamma β R hR (t+u) s ω-actualGamma β R hR t s ω)^2
      nlinarith [sq_nonneg (actualGamma β R hR (t+u) (s+v) ω-
        2*actualGamma β R hR (t+u) s ω+actualGamma β R hR t s ω)]
    _=2*(∫ ω,(a ω)^2 ∂AnnealedModelLaw.law N p)+2*(∫ ω,(b ω)^2 ∂AnnealedModelLaw.law N p) := by
      rw [integral_add (hai.const_mul _) (hbi.const_mul _),integral_const_mul,integral_const_mul]
    _≤2*((v : ℝ)/2)+2*(Real.sqrt 3*(s : ℝ)*Real.sqrt (incrementCeiling p β u)) :=
      add_le_add (mul_le_mul_of_nonneg_left (actualGamma_prefix_time_secondMoment hN β R hR hNR (t+u) s v) (by norm_num))
        (mul_le_mul_of_nonneg_left (actualGamma_terminal_time_secondMoment hN hp β R hR hNR t s u) (by norm_num))
    _=_ := by ring

theorem actualGamma_two_time_L1 (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (t s u v : ℝ≥0) :
    (∫ ω,|actualGamma (p := p) β R hR (t+u) (s+v) ω-actualGamma β R hR t s ω|
      ∂AnnealedModelLaw.law N p)≤
        Real.sqrt ((v : ℝ)+2*Real.sqrt 3*(s : ℝ)*Real.sqrt (incrementCeiling p β u)) := by
  have hm := (actualGamma_memLp_two (p := p) hN β R hR hNR (t+u) (s+v)).sub
    (actualGamma_memLp_two (p := p) hN β R hR hNR t s)
  have hh := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq (AnnealedModelLaw.law N p)
    (fun ω => |actualGamma (p := p) β R hR (t+u) (s+v) ω-actualGamma β R hR t s ω|) hm.norm
  simp only [probReal_univ,one_mul,sq_abs] at hh
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _)) (by positivity)).mpr
    (hh.trans (actualGamma_two_time_secondMoment hN hp β R hR hNR t s u v))

theorem actualGamma_mean_two_time_modulus (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (t s u v : ℝ≥0) :
    |(∫ ω,actualGamma (p := p) β R hR (t+u) (s+v) ω ∂AnnealedModelLaw.law N p)-
      ∫ ω,actualGamma β R hR t s ω ∂AnnealedModelLaw.law N p|≤
        Real.sqrt ((v : ℝ)+2*Real.sqrt 3*(s : ℝ)*Real.sqrt (incrementCeiling p β u)) := by
  rw [← integral_sub ((actualGamma_memLp_two (p := p) hN β R hR hNR (t+u) (s+v)).integrable (by norm_num))
    ((actualGamma_memLp_two (p := p) hN β R hR hNR t s).integrable (by norm_num))]
  exact abs_integral_le_integral_abs.trans (actualGamma_two_time_L1 hN hp β R hR hNR t s u v)

end SphericalAging.ActualBrownianPrimitiveTimeModulus
