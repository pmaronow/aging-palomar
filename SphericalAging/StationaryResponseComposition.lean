module

public import SphericalAging.StationaryRayConvolution
public import SphericalAging.ScalarConstraints
public import SphericalAging.BackwardResponse

public section

/-! A genuine finite-time resolvent composition identity. It follows from
one-sided response derivatives and Volterra uniqueness, without transforms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.StationaryResponseComposition
open StationaryNormalization StationaryRayConvolution StationaryConvolutionDerivative
open BackwardResponse TriangleUniqueness

/-- Only the physical response ODE and its actual initial value are inputs. -/
structure ResponseInput (ell : ℝ) (r sigma : ℝ → ℝ) : Prop where
  response_continuous : ContinuousOn r (Ici 0)
  memory_continuous : ContinuousOn sigma (Ici 0)
  initial : r 0=1
  derivative : ∀ t≥0,HasDerivWithinAt r
    (-ell*r t+causalConvolution sigma r t) (Ici 0) t

@[expose] def responseSlope (ell : ℝ) (r sigma : ℝ → ℝ) (t : ℝ) :=
  -ell*r t+causalConvolution sigma r t

@[expose] def sigmaExtension (sigma : ℝ → ℝ) (t : ℝ) := sigma (max 0 t)

theorem sigmaExtension_continuous {sigma : ℝ → ℝ} (h : ContinuousOn sigma (Ici 0)) :
    Continuous (sigmaExtension sigma) :=
  h.comp_continuous (continuous_const.max continuous_id) (fun t => by change 0 ≤ max 0 t; exact le_max_left _ _)

theorem sigmaExtension_eq (sigma : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) : sigmaExtension sigma t=sigma t := by
  simp only [sigmaExtension,max_eq_right ht]

theorem responseSlope_continuousOn {ell : ℝ} {r sigma : ℝ → ℝ} (h : ResponseInput ell r sigma) :
    ContinuousOn (responseSlope ell r sigma) (Ici 0) := by
  have hr := ScalarConstraints.rayExtension_continuous r h.response_continuous
  have hs := ScalarConstraints.rayExtension_continuous sigma h.memory_continuous
  have hc : Continuous (causalConvolution (ScalarConstraints.rayExtension sigma)
      (ScalarConstraints.rayExtension r)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact (hs.comp (continuous_fst.sub continuous_snd)).mul (hr.comp continuous_snd)
    · exact continuous_id
  have he (t : ℝ) (ht : 0 ≤ t) :
      causalConvolution (ScalarConstraints.rayExtension sigma) (ScalarConstraints.rayExtension r) t=
        causalConvolution sigma r t := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp only
    rw [ScalarConstraints.rayExtension_eq sigma (t-u) (sub_nonneg.mpr hu.2),
      ScalarConstraints.rayExtension_eq r u hu.1]
  exact (h.response_continuous.const_mul (-ell)).add (hc.continuousOn.congr (fun t ht => (he t ht).symm))

theorem response_rayC1 {ell : ℝ} {r sigma : ℝ → ℝ} (h : ResponseInput ell r sigma) :
    RayC1Input r (responseSlope ell r sigma) :=
  ⟨h.derivative,responseSlope_continuousOn h⟩

/-- The genuine matched linear extension has an actual derivative everywhere. -/
theorem linearExtension_hasDerivAt {F F' : ℝ → ℝ} (h : RayC1Input F F') (t : ℝ) :
    HasDerivAt (StationaryRayConvolution.rayExtension F F')
      (rayDerivativeExtension F' t) t := by
  by_cases ht : -1 < t
  · exact (rayExtension_C1Input F F' h).derivative t ht
  · have ht0 : t < 0 := by linarith
    have he : StationaryRayConvolution.rayExtension F F'=ᶠ[nhds t]
        (fun x => F 0+F' 0*x) := by
      filter_upwards [Iio_mem_nhds ht0] with x hx
      exact StationaryPatchedProfiles.joinAt_left 0 _ F x hx.le
    have hd : HasDerivAt (fun x : ℝ => F 0+F' 0*x) (F' 0) t := by
      convert ((hasDerivAt_id t).const_mul (F' 0)).const_add (F 0) using 1
      · rfl
      · ring
    rw [rayDerivativeExtension,StationaryPatchedProfiles.joinAt_left 0 _ F' t ht0.le]
    exact hd.congr_of_eventuallyEq he

theorem linearExtension_continuous {F F' : ℝ → ℝ} (h : RayC1Input F F') :
    Continuous (StationaryRayConvolution.rayExtension F F') :=
  continuous_iff_continuousAt.mpr (fun t => (linearExtension_hasDerivAt h t).continuousAt)

/-- A moving-upper-limit integral is differentiated from the real fixed
Leibniz rule and the actual boundary strip. -/
theorem moving_integral_derivative_all {F D : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (hD : Continuous (Function.uncurry D))
    (hd : ∀ x u,HasDerivAt (fun z => F z u) (D x u) x) (a x : ℝ) :
    HasDerivAt (fun z => ∫ u in a..z,F z u)
      ((∫ u in a..x,D x u)+F x x) x := by
  have hf := fixed_integral_derivative_all hF hD hd a x x
  have hb := GreenCovariance.moving_boundary_hasDerivAt hF x
  apply (hf.add hb).congr_of_eventuallyEq
  filter_upwards with z
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a x)
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable x z)).symm

/-- The response extension agrees with the physical data on its ray. -/
@[expose] def extendedResponse (ell : ℝ) (r sigma : ℝ → ℝ) :=
  StationaryRayConvolution.rayExtension r (responseSlope ell r sigma)

@[expose] def extendedDerivative (ell : ℝ) (r sigma : ℝ → ℝ) :=
  rayDerivativeExtension (responseSlope ell r sigma)

theorem extendedResponse_continuous {ell : ℝ} {r sigma : ℝ → ℝ} (h : ResponseInput ell r sigma) :
    Continuous (extendedResponse ell r sigma) := linearExtension_continuous (response_rayC1 h)

theorem extendedDerivative_continuous {ell : ℝ} {r sigma : ℝ → ℝ} (h : ResponseInput ell r sigma) :
    Continuous (extendedDerivative ell r sigma) :=
  rayDerivativeExtension_continuous _ (responseSlope_continuousOn h)

theorem extendedResponse_eq (ell : ℝ) (r sigma : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    extendedResponse ell r sigma t=r t := rayExtension_nonnegative _ _ t ht

theorem extendedDerivative_eq (ell : ℝ) (r sigma : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    extendedDerivative ell r sigma t=responseSlope ell r sigma t := rayDerivativeExtension_nonnegative _ t ht

/-- The linear extension satisfies the actual response equation on physical times. -/
theorem extended_derivative_equation {ell : ℝ} {r sigma : ℝ → ℝ}
    (_h : ResponseInput ell r sigma) {t : ℝ} (ht : 0 ≤ t) :
    extendedDerivative ell r sigma t= -ell*extendedResponse ell r sigma t+
      ∫ u in (0 : ℝ)..t,sigmaExtension sigma (t-u)*extendedResponse ell r sigma u := by
  rw [extendedDerivative_eq ell r sigma ht,extendedResponse_eq ell r sigma ht]
  unfold responseSlope causalConvolution
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  rw [sigmaExtension_eq sigma (sub_nonneg.mpr hu.2),extendedResponse_eq ell r sigma hu.1]

/-- Forcing from the portion of response memory preceding the split time. -/
@[expose] def splitForcing (ell : ℝ) (r sigma : ℝ → ℝ) (b t : ℝ) :=
  ∫ v in (0 : ℝ)..b,extendedResponse ell r sigma (b-v)*sigmaExtension sigma (t+v)

@[expose] def splitConvolution (ell : ℝ) (r sigma : ℝ → ℝ) (b t : ℝ) :=
  ∫ u in (0 : ℝ)..t,extendedResponse ell r sigma (t-u)*splitForcing ell r sigma b u

theorem splitForcing_continuous {ell : ℝ} {r sigma : ℝ → ℝ} (h : ResponseInput ell r sigma) (b : ℝ) :
    Continuous (splitForcing ell r sigma b) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (((extendedResponse_continuous h).comp (continuous_const.sub continuous_snd)).mul
      ((sigmaExtension_continuous h.memory_continuous).comp (continuous_fst.add continuous_snd))) 0 b

theorem splitConvolution_continuous {ell : ℝ} {r sigma : ℝ → ℝ} (h : ResponseInput ell r sigma) (b : ℝ) :
    Continuous (splitConvolution ell r sigma b) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (((extendedResponse_continuous h).comp (continuous_fst.sub continuous_snd)).mul
      ((splitForcing_continuous h b).comp continuous_snd)) continuous_id

/-- The convolution has its genuine moving-limit derivative, even at zero. -/
theorem splitConvolution_hasDerivAt {ell : ℝ} {r sigma : ℝ → ℝ}
    (h : ResponseInput ell r sigma) (b t : ℝ) :
    HasDerivAt (splitConvolution ell r sigma b)
      ((∫ u in (0 : ℝ)..t,extendedDerivative ell r sigma (t-u)*splitForcing ell r sigma b u)+
        splitForcing ell r sigma b t) t := by
  have hR := extendedResponse_continuous h
  have hD := extendedDerivative_continuous h
  have hF := splitForcing_continuous h b
  have hd := moving_integral_derivative_all
    (F := fun x u => extendedResponse ell r sigma (x-u)*splitForcing ell r sigma b u)
    (D := fun x u => extendedDerivative ell r sigma (x-u)*splitForcing ell r sigma b u)
    ((hR.comp (continuous_fst.sub continuous_snd)).mul (hF.comp continuous_snd))
    ((hD.comp (continuous_fst.sub continuous_snd)).mul (hF.comp continuous_snd))
    (fun x u => by
      have hh := ((linearExtension_hasDerivAt (response_rayC1 h) (x-u)).comp x
        ((hasDerivAt_id x).sub_const u)).mul_const (splitForcing ell r sigma b u)
      convert hh using 1
      · rfl
      · simp only [mul_one,extendedDerivative]) 0 t
  have h0 : extendedResponse ell r sigma 0=1 := by rw [extendedResponse_eq ell r sigma le_rfl,h.initial]
  rw [sub_self,h0,one_mul] at hd
  convert hd using 1
  funext z
  rfl

/-- Actual translation of the compact response memory interval. -/
theorem response_memory_translate (R S : ℝ → ℝ) (t u : ℝ) :
    (∫ v in (0 : ℝ)..t-u,S (t-u-v)*R v)=∫ z in u..t,S (t-z)*R (z-u) := by
  have hh := intervalIntegral.integral_comp_add_left (fun z => S (t-z)*R (z-u)) u
    (a := 0) (b := t-u)
  rw [add_zero,show u+(t-u)=t by ring] at hh
  convert hh using 1
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [show t-(u+v)=t-u-v by ring,show u+v-u=v by ring]

/-- The true triangular Fubini identity supplies the memory of the forcing
convolution, yielding its actual inhomogeneous Volterra equation. -/
theorem splitConvolution_derivative_equation {ell : ℝ} {r sigma : ℝ → ℝ}
    (h : ResponseInput ell r sigma) (b : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t,extendedDerivative ell r sigma (t-u)*splitForcing ell r sigma b u)+
      splitForcing ell r sigma b t =
      -ell*splitConvolution ell r sigma b t+
        (∫ z in (0 : ℝ)..t,sigmaExtension sigma (t-z)*splitConvolution ell r sigma b z)+
        splitForcing ell r sigma b t := by
  have hR := extendedResponse_continuous h
  have hS := sigmaExtension_continuous h.memory_continuous
  have hF := splitForcing_continuous h b
  have hmem : Continuous (fun u => ∫ z in u..t,
      sigmaExtension sigma (t-z)*extendedResponse ell r sigma (z-u)) :=
    continuous_integral_endpoints
      ((hS.comp (continuous_const.sub continuous_snd)).mul
        (hR.comp (continuous_snd.sub continuous_fst))) continuous_id continuous_const
  have he (u : ℝ) (hu : u ∈ Icc 0 t) :
      extendedDerivative ell r sigma (t-u)*splitForcing ell r sigma b u=
        -ell*(extendedResponse ell r sigma (t-u)*splitForcing ell r sigma b u)+
        splitForcing ell r sigma b u*(∫ z in u..t,
          sigmaExtension sigma (t-z)*extendedResponse ell r sigma (z-u)) := by
    rw [extended_derivative_equation h (sub_nonneg.mpr hu.2),
      response_memory_translate _ _ t u]
    ring
  have hI : (∫ u in (0 : ℝ)..t,extendedDerivative ell r sigma (t-u)*splitForcing ell r sigma b u)=
      -ell*splitConvolution ell r sigma b t+
      ∫ u in (0 : ℝ)..t,splitForcing ell r sigma b u*(∫ z in u..t,
        sigmaExtension sigma (t-z)*extendedResponse ell r sigma (z-u)) := by
    calc
      _ = ∫ u in (0 : ℝ)..t,
          -ell*(extendedResponse ell r sigma (t-u)*splitForcing ell r sigma b u)+
          splitForcing ell r sigma b u*(∫ z in u..t,
            sigmaExtension sigma (t-z)*extendedResponse ell r sigma (z-u)) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le ht] at hu
        exact he u hu
      _ = _ := by
        rw [intervalIntegral.integral_add
          (f := fun u => -ell*(extendedResponse ell r sigma (t-u)*splitForcing ell r sigma b u))
          (g := fun u => splitForcing ell r sigma b u*(∫ z in u..t,
            sigmaExtension sigma (t-z)*extendedResponse ell r sigma (z-u)))
          ((((hR.comp (continuous_const.sub continuous_id)).mul hF).const_mul (-ell)).intervalIntegrable 0 t)
          ((hF.mul hmem).intervalIntegrable 0 t),intervalIntegral.integral_const_mul]
        rfl
  have hswap := weighted_triangle_memory_diagonal
    (R := fun z u => extendedResponse ell r sigma (z-u))
    (Sigma := fun t z => sigmaExtension sigma (t-z))
    (hR.comp (continuous_fst.sub continuous_snd))
    (hS.comp (continuous_fst.sub continuous_snd)) hF ht
  rw [hI,hswap]
  rfl

/-- The shifted response has a genuine forcing from times preceding b. -/
theorem shifted_response_derivative_equation {ell : ℝ} {r sigma : ℝ → ℝ}
    (h : ResponseInput ell r sigma) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    extendedDerivative ell r sigma (t+b)=
      -ell*extendedResponse ell r sigma (t+b)+
        (∫ u in (0 : ℝ)..t,sigmaExtension sigma (t-u)*extendedResponse ell r sigma (u+b))+
        splitForcing ell r sigma b t := by
  have hR := extendedResponse_continuous h
  have hS := sigmaExtension_continuous h.memory_continuous
  have hi : Continuous (fun u => sigmaExtension sigma (t+b-u)*extendedResponse ell r sigma u) :=
    (hS.comp (continuous_const.sub continuous_id)).mul hR
  rw [extended_derivative_equation h (add_nonneg ht hb)]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (μ := volume) 0 b)
    (hi.intervalIntegrable (μ := volume) b (t+b))
  have hpast : (∫ u in (0 : ℝ)..b,sigmaExtension sigma (t+b-u)*extendedResponse ell r sigma u)=
      splitForcing ell r sigma b t := by
    have hh' := intervalIntegral.integral_comp_sub_left
      (fun u => sigmaExtension sigma (t+b-u)*extendedResponse ell r sigma u) b
      (a := 0) (b := b)
    rw [sub_zero,sub_self] at hh'
    change (∫ v in (0 : ℝ)..b,sigmaExtension sigma (t+b-(b-v))*extendedResponse ell r sigma (b-v))=
      ∫ u in (0 : ℝ)..b,sigmaExtension sigma (t+b-u)*extendedResponse ell r sigma u at hh'
    rw [←hh']
    unfold splitForcing
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [show t+b-(b-v)=t+v by ring,mul_comm]
  have hfuture : (∫ u in b..t+b,sigmaExtension sigma (t+b-u)*extendedResponse ell r sigma u)=
      ∫ u in (0 : ℝ)..t,sigmaExtension sigma (t-u)*extendedResponse ell r sigma (u+b) := by
    have hh := intervalIntegral.integral_comp_add_right
      (fun u => sigmaExtension sigma (t+b-u)*extendedResponse ell r sigma u) b (a := 0) (b := t)
    rw [zero_add] at hh
    rw [←hh]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [show t+b-(u+b)=t-u by ring]
  rw [←hsplit,hpast,hfuture]
  ring

/-- The actual composition error, without any zero-error hypothesis. -/
@[expose] def compositionError (ell : ℝ) (r sigma : ℝ → ℝ) (b t : ℝ) :=
  extendedResponse ell r sigma (t+b)-
    extendedResponse ell r sigma b*extendedResponse ell r sigma t-splitConvolution ell r sigma b t

@[expose] def compositionErrorSlope (ell : ℝ) (r sigma : ℝ → ℝ) (b t : ℝ) :=
  extendedDerivative ell r sigma (t+b)-extendedResponse ell r sigma b*extendedDerivative ell r sigma t-
    ((∫ u in (0 : ℝ)..t,extendedDerivative ell r sigma (t-u)*splitForcing ell r sigma b u)+
      splitForcing ell r sigma b t)

theorem compositionError_continuous {ell : ℝ} {r sigma : ℝ → ℝ}
    (h : ResponseInput ell r sigma) (b : ℝ) : Continuous (compositionError ell r sigma b) := by
  exact (((extendedResponse_continuous h).comp (continuous_id.add continuous_const)).sub
    ((extendedResponse_continuous h).const_mul _)).sub (splitConvolution_continuous h b)

theorem compositionError_hasDerivAt {ell : ℝ} {r sigma : ℝ → ℝ}
    (h : ResponseInput ell r sigma) (b t : ℝ) :
    HasDerivAt (compositionError ell r sigma b) (compositionErrorSlope ell r sigma b t) t := by
  have hd := (((linearExtension_hasDerivAt (response_rayC1 h) (t+b)).comp t
    ((hasDerivAt_id t).add_const b)).sub
      ((linearExtension_hasDerivAt (response_rayC1 h) t).const_mul (extendedResponse ell r sigma b))).sub
        (splitConvolution_hasDerivAt h b t)
  convert hd using 1
  · rfl
  · simp only [compositionErrorSlope,extendedDerivative,mul_one]

/-- The error really satisfies a homogeneous Volterra ODE. -/
theorem compositionError_equation {ell : ℝ} {r sigma : ℝ → ℝ}
    (h : ResponseInput ell r sigma) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    compositionErrorSlope ell r sigma b t= -ell*compositionError ell r sigma b t+
      ∫ u in (0 : ℝ)..t,sigmaExtension sigma (t-u)*compositionError ell r sigma b u := by
  have hR := extendedResponse_continuous h
  have hS := sigmaExtension_continuous h.memory_continuous
  have hJ := splitConvolution_continuous h b
  have h1 : Continuous (fun u => sigmaExtension sigma (t-u)*extendedResponse ell r sigma (u+b)) :=
    (hS.comp (continuous_const.sub continuous_id)).mul (hR.comp (continuous_id.add continuous_const))
  have h2 : Continuous (fun u => sigmaExtension sigma (t-u)*
      (extendedResponse ell r sigma b*extendedResponse ell r sigma u)) :=
    (hS.comp (continuous_const.sub continuous_id)).mul (hR.const_mul _)
  have h3 : Continuous (fun u => sigmaExtension sigma (t-u)*splitConvolution ell r sigma b u) :=
    (hS.comp (continuous_const.sub continuous_id)).mul hJ
  have hmem : (∫ u in (0 : ℝ)..t,sigmaExtension sigma (t-u)*compositionError ell r sigma b u)=
      (∫ u in (0 : ℝ)..t,sigmaExtension sigma (t-u)*extendedResponse ell r sigma (u+b))-
        extendedResponse ell r sigma b*(∫ u in (0 : ℝ)..t,sigmaExtension sigma (t-u)*extendedResponse ell r sigma u)-
        (∫ u in (0 : ℝ)..t,sigmaExtension sigma (t-u)*splitConvolution ell r sigma b u) := by
    have he : (fun u => sigmaExtension sigma (t-u)*compositionError ell r sigma b u)=
        (fun u => sigmaExtension sigma (t-u)*extendedResponse ell r sigma (u+b)-
          sigmaExtension sigma (t-u)*(extendedResponse ell r sigma b*extendedResponse ell r sigma u)-
          sigmaExtension sigma (t-u)*splitConvolution ell r sigma b u) := by
      funext u
      unfold compositionError
      ring
    rw [he,intervalIntegral.integral_sub
      (f := fun u => sigmaExtension sigma (t-u)*extendedResponse ell r sigma (u+b)-
        sigmaExtension sigma (t-u)*(extendedResponse ell r sigma b*extendedResponse ell r sigma u))
      (g := fun u => sigmaExtension sigma (t-u)*splitConvolution ell r sigma b u)
      ((h1.sub h2).intervalIntegrable 0 t) (h3.intervalIntegrable 0 t),
      intervalIntegral.integral_sub
      (f := fun u => sigmaExtension sigma (t-u)*extendedResponse ell r sigma (u+b))
      (g := fun u => sigmaExtension sigma (t-u)*(extendedResponse ell r sigma b*extendedResponse ell r sigma u))
      (h1.intervalIntegrable 0 t) (h2.intervalIntegrable 0 t)]
    have he2 : (∫ u in (0 : ℝ)..t,sigmaExtension sigma (t-u)*
        (extendedResponse ell r sigma b*extendedResponse ell r sigma u))=
        extendedResponse ell r sigma b*(∫ u in (0 : ℝ)..t,sigmaExtension sigma (t-u)*extendedResponse ell r sigma u) := by
      rw [←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      ring
    rw [he2]
  unfold compositionErrorSlope
  rw [shifted_response_derivative_equation h hb ht,extended_derivative_equation h ht,
    splitConvolution_derivative_equation h b ht,hmem]
  unfold compositionError
  ring

/-- Compact homogeneous uniqueness proves that the actual composition
error vanishes on every finite physical interval. -/
theorem compositionError_zero {ell : ℝ} {r sigma : ℝ → ℝ}
    (h : ResponseInput ell r sigma) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    compositionError ell r sigma b a=0 := by
  have hS := sigmaExtension_continuous h.memory_continuous
  obtain ⟨S,hSb⟩ := isCompact_Icc.bddAbove_image
    (hS.abs.continuousOn : ContinuousOn (fun u => |sigmaExtension sigma u|) (Icc 0 a))
  have hzero : compositionError ell r sigma b 0=0 := by
    unfold compositionError splitConvolution
    rw [extendedResponse_eq ell r sigma le_rfl,h.initial]
    simp only [zero_add,intervalIntegral.integral_same,mul_one,sub_self]
  have hh := VolterraUniqueness.homogeneous_row_eq_zero
    (compositionError ell r sigma b) (compositionErrorSlope ell r sigma b) (fun _ => ell)
    (fun t u => sigmaExtension sigma (t-u)) 0 a |ell| (max 0 S) ha (abs_nonneg _) (le_max_left _ _)
    (compositionError_continuous h b) hzero
    (fun t _ => (compositionError_hasDerivAt h b t).hasDerivWithinAt)
    (fun t ht => compositionError_equation h hb ht.1)
    (fun _ _ => le_refl _)
    (fun t _ => ((hS.comp (continuous_const.sub continuous_id)).mul
      (compositionError_continuous h b)).intervalIntegrable 0 t)
    (fun t ht u hu => by
      have hz : t-u ∈ Icc 0 a := ⟨sub_nonneg.mpr hu.2,by linarith [ht.2,hu.1]⟩
      exact (hSb ⟨t-u,hz,rfl⟩).trans (le_max_right _ _))
  exact hh a ⟨ha,le_refl a⟩

/-- The genuine finite-time resolvent composition, derived from the
physical response ODE. No transform identity is assumed. -/
theorem response_composition {ell : ℝ} {r sigma : ℝ → ℝ}
    (h : ResponseInput ell r sigma) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    r (a+b)=r a*r b+
      ∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,r (a-u)*r (b-v)*sigma (u+v) := by
  have hz := compositionError_zero h ha hb
  unfold compositionError at hz
  rw [extendedResponse_eq ell r sigma (add_nonneg ha hb),
    extendedResponse_eq ell r sigma hb,extendedResponse_eq ell r sigma ha] at hz
  have hJ : splitConvolution ell r sigma b a=
      ∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,r (a-u)*r (b-v)*sigma (u+v) := by
    unfold splitConvolution
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ha] at hu
    dsimp only
    rw [extendedResponse_eq ell r sigma (sub_nonneg.mpr hu.2)]
    unfold splitForcing
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hb] at hv
    dsimp only
    rw [extendedResponse_eq ell r sigma (sub_nonneg.mpr hv.2),sigmaExtension_eq sigma (add_nonneg hu.1 hv.1)]
    ring
  rw [hJ] at hz
  linarith only [hz]

end SphericalAging.StationaryResponseComposition
