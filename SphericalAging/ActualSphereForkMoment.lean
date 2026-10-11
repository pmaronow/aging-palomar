module

public import SphericalAging.ActualSphereTensorSemigroup
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.HasLaw

public section

/-! The source10.3 endpoint receipt. Two independent actual Wiener
restarts have normalized-overlap moment equal to the genuine tensor
semigroup product. This proves the fork identification, rather than
assuming a fork-moment formula. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualSphereForkMoment
open FiniteModel HardSphereDynamics LocalSDE AdaptiveGradientDisclosure
  ActualSphereTransition SphereTensorObservable ActualSphereTensorSemigroup
variable {N p k : ℕ}

/-- A genuine canonical Wiener restart from the physical waiting state. -/
@[expose] def endpoint (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    (t : ℝ≥0) (x : State N) (ω : VectorBrownian.Space N) : State N :=
  jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) t ω

@[expose] def forkMoment (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    (a b : ℝ≥0) (x : State N) : ℝ :=
  ∫ω : VectorBrownian.Space N×VectorBrownian.Space N,
    (⟪endpoint β R hR J a x ω.1,endpoint β R hR J b x ω.2⟫_ℝ/(N:ℝ))^k
      ∂(VectorBrownian.law N).prod (VectorBrownian.law N)

theorem integral_inner_product {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {f : A→E} {g : B→E} (hf : Integrable f μ) (hg : Integrable g ν) :
    (∫z : A×B,⟪f z.1,g z.2⟫_ℝ ∂μ.prod ν)=⟪∫x,f x ∂μ,∫y,g y ∂ν⟫_ℝ := by
  have hi : Integrable (fun z : A×B => ⟪f z.1,g z.2⟫_ℝ) (μ.prod ν) :=
    hf.op_fst_snd (continuous_fst.inner continuous_snd)
      ⟨1,fun x y => by simpa only [one_mul] using norm_inner_le_norm x y⟩ hg
  rw [integral_prod _ hi]
  simp_rw [integral_inner hg]
  rw [show (fun x => ⟪f x,∫y,g y ∂ν⟫_ℝ)=
    (fun x => ⟪∫y,g y ∂ν,f x⟫_ℝ) by funext x;exact real_inner_comm _ _]
  rw [integral_inner hf,real_inner_comm]

theorem endpoint_measurable (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (t : ℝ≥0) :
    Measurable (fun z : State N×VectorBrownian.Space N => endpoint β R hR J t z.1 z.2) :=
  terminal_measurable _ β R hR J t

theorem compact_pair_ae_eq (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (a b : ℝ≥0)
    (x : State N) (hx : OnSphere x) :
    (fun ω : VectorBrownian.Space N×VectorBrownian.Space N =>
      ⟪compactObservable (k:=k) R hR (endpoint β R hR J a x ω.1),
        compactObservable (k:=k) R hR (endpoint β R hR J b x ω.2)⟫_ℝ) =ᵐ[
        (VectorBrownian.law N).prod (VectorBrownian.law N)]
    (fun ω => (⟪endpoint β R hR J a x ω.1,endpoint β R hR J b x ω.2⟫_ℝ/(N:ℝ))^k) := by
  have hs := jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J x hx
  have h1 := (measurePreserving_fst (μ:=VectorBrownian.law N) (ν:=VectorBrownian.law N)).quasiMeasurePreserving.ae hs
  have h2 := (measurePreserving_snd (μ:=VectorBrownian.law N) (ν:=VectorBrownian.law N)).quasiMeasurePreserving.ae hs
  filter_upwards [h1,h2] with ω hω1 hω2
  dsimp only [endpoint]
  rw [(compactObservable_eventuallyEq R hR hNR (hω1 a)).eq_of_nhds,
    (compactObservable_eventuallyEq R hR hNR (hω2 b)).eq_of_nhds]
  exact observable_inner hN _ _

/-- Literal two-independent-future endpoint moment, for arbitrary k. -/
theorem forkMoment_eq_tensorMean (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (a b : ℝ≥0)
    (x : State N) (hx : OnSphere x) :
    forkMoment (k:=k) β R hR J a b x=
      ⟪tensorMean (k:=k) β R hR J a x,tensorMean (k:=k) β R hR J b x⟫_ℝ := by
  rw [forkMoment,←integral_congr_ae (compact_pair_ae_eq (k:=k) hN β R hR hNR J a b x hx)]
  exact integral_inner_product (compact_terminal_integrable β R hR J a x)
    (compact_terminal_integrable β R hR J b x)

@[expose] def compactPair (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    (a b : ℝ≥0) (x : State N) (ω : VectorBrownian.Space N×VectorBrownian.Space N) : ℝ :=
  ⟪compactObservable (k:=k) R hR (endpoint β R hR J a x ω.1),
    compactObservable (k:=k) R hR (endpoint β R hR J b x ω.2)⟫_ℝ

@[expose] def momentIntegrand (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    (a b : ℝ≥0) (x : State N) (ω : VectorBrownian.Space N×VectorBrownian.Space N) : ℝ :=
  (⟪endpoint β R hR J a x ω.1,endpoint β R hR J b x ω.2⟫_ℝ/(N:ℝ))^k

theorem compactPair_measurable (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (a b : ℝ≥0) :
    Measurable (Function.uncurry (compactPair (k:=k) β R hR J a b)) := by
  have h1 : Measurable (fun z : State N×(VectorBrownian.Space N×VectorBrownian.Space N) =>
      compactObservable (k:=k) R hR (endpoint β R hR J a z.1 z.2.1)) := (compactObservable_contDiff (N:=N) (k:=k) R hR).continuous.measurable.comp
    ((endpoint_measurable β R hR J a).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  have h2 : Measurable (fun z : State N×(VectorBrownian.Space N×VectorBrownian.Space N) =>
      compactObservable (k:=k) R hR (endpoint β R hR J b z.1 z.2.2)) := (compactObservable_contDiff (N:=N) (k:=k) R hR).continuous.measurable.comp
    ((endpoint_measurable β R hR J b).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  exact (continuous_fst.inner continuous_snd).measurable.comp (h1.prodMk h2)

theorem momentIntegrand_measurable (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (a b : ℝ≥0) :
    Measurable (Function.uncurry (momentIntegrand (k:=k) β R hR J a b)) := by
  have h1 : Measurable (fun z : State N×(VectorBrownian.Space N×VectorBrownian.Space N) =>
      endpoint β R hR J a z.1 z.2.1) := (endpoint_measurable β R hR J a).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h2 : Measurable (fun z : State N×(VectorBrownian.Space N×VectorBrownian.Space N) =>
      endpoint β R hR J b z.1 z.2.2) := (endpoint_measurable β R hR J b).comp
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact (((continuous_fst.inner continuous_snd).measurable.comp (h1.prodMk h2)).div_const _).pow_const k

/-- The waiting seed and the two independent actual future Wiener paths
live on their literal product probability space. -/
@[expose] def waitingForkMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω→State N) (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    (a b : ℝ≥0) : ℝ :=
  ∫z : Ω×(VectorBrownian.Space N×VectorBrownian.Space N),
    momentIntegrand (k:=k) β R hR J a b (X z.1) z.2
      ∂μ.prod ((VectorBrownian.law N).prod (VectorBrownian.law N))

theorem waiting_pair_ae_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω→State N} (hX : Measurable X)
    (hXs : ∀ᵐω ∂μ,OnSphere (X ω)) (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (a b : ℝ≥0) :
    (fun z : Ω×(VectorBrownian.Space N×VectorBrownian.Space N) =>
      compactPair (k:=k) β R hR J a b (X z.1) z.2) =ᵐ[
        μ.prod ((VectorBrownian.law N).prod (VectorBrownian.law N))]
    (fun z => momentIntegrand (k:=k) β R hR J a b (X z.1) z.2) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    ((compactPair_measurable β R hR J a b).comp ((hX.comp measurable_fst).prodMk measurable_snd))
    ((momentIntegrand_measurable β R hR J a b).comp ((hX.comp measurable_fst).prodMk measurable_snd)))).mpr
  filter_upwards [hXs] with ω hω
  exact compact_pair_ae_eq hN β R hR hNR J a b (X ω) hω

theorem waiting_compact_pair_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω→State N} (hX : Measurable X)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (a b : ℝ≥0) :
    Integrable (fun z : Ω×(VectorBrownian.Space N×VectorBrownian.Space N) =>
      compactPair (k:=k) β R hR J a b (X z.1) z.2)
      (μ.prod ((VectorBrownian.law N).prod (VectorBrownian.law N))) := by
  obtain ⟨C,hC⟩ := (compactObservable_hasCompactSupport (N:=N) (k:=k) R hR).exists_bound_of_continuous
    (compactObservable_contDiff R hR).continuous
  have hC0 : 0≤C := (norm_nonneg (compactObservable (k:=k) R hR (0 : State N))).trans (hC _)
  apply Integrable.of_bound
    ((compactPair_measurable β R hR J a b).comp
      ((hX.comp measurable_fst).prodMk measurable_snd)).aestronglyMeasurable (C^2)
  apply ae_of_all
  intro z
  dsimp only [compactPair,Function.comp_def]
  exact (norm_inner_le_norm _ _).trans (by
    simpa only [pow_two] using mul_le_mul
      (hC (endpoint β R hR J a (X z.1) z.2.1))
      (hC (endpoint β R hR J b (X z.1) z.2.2)) (norm_nonneg _) hC0)

/-- Full endpoint identity on the actual waiting × future × future law. -/
theorem waitingForkMoment_eq_tensorMean {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω→State N} (hX : Measurable X)
    (hXs : ∀ᵐω ∂μ,OnSphere (X ω)) (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (a b : ℝ≥0) :
    waitingForkMoment (k:=k) μ X β R hR J a b=
      ∫ω,⟪tensorMean (k:=k) β R hR J a (X ω),tensorMean (k:=k) β R hR J b (X ω)⟫_ℝ ∂μ := by
  rw [waitingForkMoment,←integral_congr_ae (waiting_pair_ae_eq hX hXs hN β R hR hNR J a b),
    integral_prod _ (waiting_compact_pair_integrable hX β R hR J a b)]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => integral_inner_product
    (compact_terminal_integrable β R hR J a (X ω))
    (compact_terminal_integrable β R hR J b (X ω))

theorem waiting_moment_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω→State N} (hX : Measurable X)
    (hXs : ∀ᵐω ∂μ,OnSphere (X ω)) (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (a b : ℝ≥0) :
    Integrable (fun z : Ω×(VectorBrownian.Space N×VectorBrownian.Space N) =>
      momentIntegrand (k:=k) β R hR J a b (X z.1) z.2)
      (μ.prod ((VectorBrownian.law N).prod (VectorBrownian.law N))) :=
  (waiting_compact_pair_integrable hX β R hR J a b).congr
    (waiting_pair_ae_eq hX hXs hN β R hR hNR J a b)

/-- A positive forward density identifying the genuine waiting-state law
gives the literal density/tensor product formula. The density law is the
preceding forward-realization input; the fork moment is proved from the
actual independent Wiener restart construction. -/
theorem waitingForkMoment_eq_density {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω→State N} (hX : Measurable X)
    (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (a b : ℝ≥0) {ρ : State N→ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀x,0≤ρ x)
    (hLaw : HasLaw X ((SphereInitialLaw.sphereLaw N).withDensity (fun x => ENNReal.ofReal (ρ x))) μ) :
    waitingForkMoment (k:=k) μ X β R hR J a b=
      ∫x : State N,ρ x*⟪tensorMean (k:=k) β R hR J a x,tensorMean (k:=k) β R hR J b x⟫_ℝ
        ∂SphereInitialLaw.sphereLaw N := by
  have hsphere : ∀ᵐx ∂SphereInitialLaw.sphereLaw N,OnSphere x := by
    simpa only [OnSphere,real_inner_self_eq_norm_sq] using
      SphereInitialLaw.sphereLaw_support (by omega : 1≤N)
  have hXs : ∀ᵐω ∂μ,OnSphere (X ω) :=
    (hLaw.ae_iff (by unfold OnSphere;fun_prop)).mpr
      ((withDensity_absolutelyContinuous _ _).ae_le hsphere)
  rw [waitingForkMoment_eq_tensorMean hX hXs hN β R hR hNR J a b]
  have hm : Continuous (fun x : State N =>
      ⟪tensorMean (k:=k) β R hR J a x,tensorMean (k:=k) β R hR J b x⟫_ℝ) :=
    (tensorMean_contDiff_two β R hR J a).continuous.inner
      (tensorMean_contDiff_two β R hR J b).continuous
  have he := hLaw.integral_comp hm.aestronglyMeasurable
  simp only [Function.comp_def] at he
  rw [he,
    integral_withDensity_eq_integral_toReal_smul (hρ.ennreal_ofReal)
      (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hρ0 x)]
    rfl

/-- The same formula in the literal real-age semigroup notation used by
the source10.3 product current. -/
theorem waitingForkMoment_eq_realTensorDensity {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω→State N} (hX : Measurable X)
    (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (a b : ℝ) {ρ : State N→ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀x,0≤ρ x)
    (hLaw : HasLaw X ((SphereInitialLaw.sphereLaw N).withDensity (fun x => ENNReal.ofReal (ρ x))) μ) :
    waitingForkMoment (k:=k) μ X β R hR J a.toNNReal b.toNNReal=
      ∫x : State N,ρ x*⟪realTensorMean (k:=k) β R hR J a x,realTensorMean (k:=k) β R hR J b x⟫_ℝ
        ∂SphereInitialLaw.sphereLaw N :=
  waitingForkMoment_eq_density hX hN β R hR hNR J a.toNNReal b.toNNReal hρ hρ0 hLaw

theorem waitingForkMoment_abs_le_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω→State N} (hX : Measurable X)
    (hXs : ∀ᵐω ∂μ,OnSphere (X ω)) (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (a b : ℝ≥0) :
    |waitingForkMoment (k:=k) μ X β R hR J a b|≤1 := by
  rw [waitingForkMoment_eq_tensorMean hX hXs hN β R hR hNR J a b,←Real.norm_eq_abs]
  have hb : ∀ᵐω ∂μ,‖⟪tensorMean (k:=k) β R hR J a (X ω),tensorMean (k:=k) β R hR J b (X ω)⟫_ℝ‖≤1 := by
    filter_upwards [hXs] with ω hω
    exact (norm_inner_le_norm _ _).trans (by
      simpa only [one_mul] using mul_le_mul
        (tensorMean_norm_le_one hN β R hR hNR J a (X ω) hω)
        (tensorMean_norm_le_one hN β R hR hNR J b (X ω) hω) (norm_nonneg _) (by norm_num : (0:ℝ)≤1))
  simpa only [probReal_univ,one_mul] using norm_integral_le_of_norm_le_const hb

theorem endpoint_joint_measurable (β R : ℝ≥0) (hR : 0<(R:ℝ)) (t : ℝ≥0) :
    Measurable (fun z : (Disorder N p×State N)×VectorBrownian.Space N =>
      endpoint β R hR z.1.1 t z.1.2 z.2) :=
  (jointProcess_measurable (NullAugmentation.driver (VectorBrownian.driver N)) β R hR).measurable.comp
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

theorem momentIntegrand_joint_measurable (β R : ℝ≥0) (hR : 0<(R:ℝ)) (a b : ℝ≥0) :
    Measurable (fun z : (Disorder N p×State N)×(VectorBrownian.Space N×VectorBrownian.Space N) =>
      momentIntegrand (k:=k) β R hR z.1.1 a b z.1.2 z.2) := by
  have h1 : Measurable (fun z : (Disorder N p×State N)×(VectorBrownian.Space N×VectorBrownian.Space N) =>
      endpoint β R hR z.1.1 a z.1.2 z.2.1) :=
    (endpoint_joint_measurable β R hR a).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h2 : Measurable (fun z : (Disorder N p×State N)×(VectorBrownian.Space N×VectorBrownian.Space N) =>
      endpoint β R hR z.1.1 b z.1.2 z.2.2) :=
    (endpoint_joint_measurable β R hR b).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact (((continuous_fst.inner continuous_snd).measurable.comp (h1.prodMk h2)).div_const _).pow_const k

set_option maxHeartbeats 50000 in
/-- Genuine disorder measurability is inherited from the actual SDE
family and Wiener integration; no joint forward-density measurability
assumption is needed. -/
theorem waitingForkMoment_measurable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {X : Disorder N p→Ω→State N}
    (hX : Measurable (Function.uncurry X)) (β R : ℝ≥0) (hR : 0<(R:ℝ)) (a b : ℝ≥0) :
    Measurable (fun J : Disorder N p => waitingForkMoment (k:=k) μ (X J) β R hR J a b) := by
  have hseed : Measurable (fun z : Disorder N p×(Ω×(VectorBrownian.Space N×VectorBrownian.Space N)) =>
      (z.1,z.2.1)) := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hstate : Measurable (fun z : Disorder N p×(Ω×(VectorBrownian.Space N×VectorBrownian.Space N)) =>
      X z.1 z.2.1) := hX.comp hseed
  have harg : Measurable (fun z : Disorder N p×(Ω×(VectorBrownian.Space N×VectorBrownian.Space N)) =>
      ((z.1,X z.1 z.2.1),z.2.2)) :=
    (measurable_fst.prodMk hstate).prodMk (measurable_snd.comp measurable_snd)
  have hF : Measurable (fun z : Disorder N p×(Ω×(VectorBrownian.Space N×VectorBrownian.Space N)) =>
      momentIntegrand (k:=k) β R hR z.1 a b (X z.1 z.2.1) z.2.2) :=
    by
      have hh := (momentIntegrand_joint_measurable (N:=N) (p:=p) (k:=k) β R hR a b).comp harg
      simpa only [Function.comp_def] using hh
  change Measurable (fun J : Disorder N p => ∫z : Ω×(VectorBrownian.Space N×VectorBrownian.Space N),
    momentIntegrand (k:=k) β R hR J a b (X J z.1) z.2
      ∂μ.prod ((VectorBrownian.law N).prod (VectorBrownian.law N)))
  exact (hF.stronglyMeasurable.integral_prod_right'
    (ν:=μ.prod ((VectorBrownian.law N).prod (VectorBrownian.law N)))).measurable

/-- The exact endpoint law transfers actual disorder measurability to
the printed density product, even if the density package has no joint
disorder measurability field. -/
theorem density_pairing_measurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Disorder N p→Ω→State N}
    (hX : Measurable (Function.uncurry X)) (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (a b : ℝ≥0)
    {ρ : Disorder N p→State N→ℝ} (hρ : ∀J,Measurable (ρ J)) (hρ0 : ∀J x,0≤ρ J x)
    (hLaw : ∀J,HasLaw (X J) ((SphereInitialLaw.sphereLaw N).withDensity
      (fun x => ENNReal.ofReal (ρ J x))) μ) :
    Measurable (fun J : Disorder N p => ∫x : State N,ρ J x*
      ⟪tensorMean (k:=k) β R hR J a x,tensorMean (k:=k) β R hR J b x⟫_ℝ
        ∂SphereInitialLaw.sphereLaw N) := by
  have he : (fun J : Disorder N p => waitingForkMoment (k:=k) μ (X J) β R hR J a b)=
      (fun J => ∫x : State N,ρ J x*⟪tensorMean (k:=k) β R hR J a x,tensorMean (k:=k) β R hR J b x⟫_ℝ
        ∂SphereInitialLaw.sphereLaw N) := by
    funext J
    exact waitingForkMoment_eq_density (hX.comp (measurable_const.prodMk measurable_id))
      hN β R hR hNR J a b (hρ J) (hρ0 J) (hLaw J)
  rw [←he]
  exact waitingForkMoment_measurable (N:=N) (p:=p) (k:=k) μ hX β R hR a b

end SphericalAging.ActualSphereForkMoment
