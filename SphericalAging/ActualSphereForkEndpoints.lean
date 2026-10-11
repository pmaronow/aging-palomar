module

public import SphericalAging.ActualSphereForkConditional
public import SphericalAging.ActualSphereMarkovRestart

public section

/-! The literal source10.3 fork endpoints, with a genuine independent
uniform sphere initial point. The same-path identity averages the
fixed-initial conditional transition theorem over the sphere law. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualSphereForkEndpoints
open FiniteModel HardSphereDynamics AnnealedSDECore ActualSphereTransition
  ActualSphereForkMoment ActualSphereForkConditional ActualSphereMarkovRestart
  ActualSphereTensorSemigroup ActualSphereTensorProductCurrent SphereTensorObservable
  SphereInitialLaw SphereFisherHelly
variable {N p k : ℕ}

@[expose] def initialLaw (N : ℕ) : Measure (State N×VectorBrownian.Space N) :=
  (sphereLaw N).prod (VectorBrownian.law N)

instance : IsProbabilityMeasure (initialLaw N) := by unfold initialLaw;infer_instance

@[expose] def initialWaiting (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (s : ℝ≥0)
    (eta : State N×VectorBrownian.Space N) : State N :=
  endpoint β R hR J s eta.1 eta.2

@[expose] def initialForkMoment (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (s a b : ℝ≥0) : ℝ :=
  waitingForkMoment (k:=k) (initialLaw N) (initialWaiting β R hR J s) β R hR J a b

@[expose] def samePathMoment (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (s b : ℝ≥0) : ℝ :=
  ∫eta : State N×VectorBrownian.Space N,
    (⟪initialWaiting β R hR J s eta,initialWaiting β R hR J (s+b) eta⟫_ℝ/(N:ℝ))^k
      ∂initialLaw N

theorem initialWaiting_measurable (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (s : ℝ≥0) :
    Measurable (initialWaiting β R hR J s) := endpoint_measurable β R hR J s

theorem initialWaiting_joint_measurable (β R : ℝ≥0) (hR : 0<(R:ℝ)) (s : ℝ≥0) :
    Measurable (fun z : Disorder N p×(State N×VectorBrownian.Space N) =>
      initialWaiting β R hR z.1 s z.2) := by
  have hh := (endpoint_joint_measurable (N:=N) (p:=p) β R hR s).comp
    ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  simpa only [Function.comp_def,initialWaiting] using hh

theorem initialWaiting_onSphere (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (s : ℝ≥0) :
    ∀ᵐeta ∂initialLaw N,OnSphere (initialWaiting β R hR J s eta) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_setOfPred.mpr
    (((continuous_fst.inner continuous_snd).measurable.comp
      ((initialWaiting_measurable β R hR J s).prodMk
        (initialWaiting_measurable β R hR J s))).eq measurable_const))).mpr
  filter_upwards [sphereLaw_support (by omega : 1≤N)] with x hx
  have hxS : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
  exact (jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N)
    β R hR hNR J x hxS).mono (fun _ h => h s)

theorem compact_norm_one (hN : 0<N) (R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) {x : State N} (hx : OnSphere x) :
    ‖compactObservable (k:=k) R hR x‖=1 := by
  rw [(compactObservable_eventuallyEq R hR hNR hx).eq_of_nhds]
  apply observable_norm_one hN
  exact (sq_eq_sq₀ (norm_nonneg x) (Real.sqrt_nonneg _)).mp
    ((onSphere_iff_norm_sq x).mp hx |>.trans (Real.sq_sqrt (Nat.cast_nonneg N)).symm)

theorem compact_samePath_integrable (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (s b : ℝ≥0) :
    Integrable (fun eta : State N×VectorBrownian.Space N =>
      ⟪compactObservable (k:=k) R hR (initialWaiting β R hR J s eta),
        compactObservable (k:=k) R hR (initialWaiting β R hR J (s+b) eta)⟫_ℝ) (initialLaw N) := by
  have h1 := (compactObservable_contDiff (N:=N) (k:=k) R hR).continuous.measurable.comp
    (initialWaiting_measurable β R hR J s)
  have h2 := (compactObservable_contDiff (N:=N) (k:=k) R hR).continuous.measurable.comp
    (initialWaiting_measurable β R hR J (s+b))
  apply Integrable.of_bound ((continuous_fst.inner continuous_snd).measurable.comp
    (h1.prodMk h2)).aestronglyMeasurable 1
  filter_upwards [initialWaiting_onSphere hN β R hR hNR J s,
    initialWaiting_onSphere hN β R hR hNR J (s+b)] with eta hs ht
  change ‖⟪compactObservable (k:=k) R hR (initialWaiting β R hR J s eta),
    compactObservable (k:=k) R hR (initialWaiting β R hR J (s+b) eta)⟫_ℝ‖≤1
  exact (norm_inner_le_norm _ _).trans (by rw [compact_norm_one hN R hR hNR hs,
    compact_norm_one hN R hR hNR ht,one_mul])

theorem compact_waiting_mean_integrable (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (s b : ℝ≥0) :
    Integrable (fun eta : State N×VectorBrownian.Space N =>
      ⟪compactObservable (k:=k) R hR (initialWaiting β R hR J s eta),
        tensorMean (k:=k) β R hR J b (initialWaiting β R hR J s eta)⟫_ℝ) (initialLaw N) := by
  have h1 := (compactObservable_contDiff (N:=N) (k:=k) R hR).continuous.measurable.comp
    (initialWaiting_measurable β R hR J s)
  have h2 := (tensorMean_contDiff_two (k:=k) β R hR J b).continuous.measurable.comp
    (initialWaiting_measurable β R hR J s)
  apply Integrable.of_bound ((continuous_fst.inner continuous_snd).measurable.comp
    (h1.prodMk h2)).aestronglyMeasurable 1
  filter_upwards [initialWaiting_onSphere hN β R hR hNR J s] with eta hs
  change ‖⟪compactObservable (k:=k) R hR (initialWaiting β R hR J s eta),
    tensorMean (k:=k) β R hR J b (initialWaiting β R hR J s eta)⟫_ℝ‖≤1
  apply (norm_inner_le_norm _ _).trans
  rw [compact_norm_one hN R hR hNR hs,one_mul]
  exact tensorMean_norm_le_one hN β R hR hNR J b _ hs

/-- Both independent-future and same-path endpoints use the genuine
uniform initial sphere point; no random initial point is placed in the
canonical Wiener time-zero sigma algebra. -/
theorem initial_zero_branch_eq_same_path (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (s b : ℝ≥0) :
    initialForkMoment (k:=k) β R hR J s 0 b=samePathMoment (k:=k) β R hR J s b := by
  rw [initialForkMoment,waitingForkMoment_eq_tensorMean (initialWaiting_measurable β R hR J s)
    (initialWaiting_onSphere hN β R hR hNR J s) hN β R hR hNR J 0 b]
  simp_rw [tensorMean_zero]
  rw [show initialLaw N=(sphereLaw N).prod (VectorBrownian.law N) from rfl,
    integral_prod _ (compact_waiting_mean_integrable hN β R hR hNR J s b)]
  have he : (∫x : State N,∫ω : VectorBrownian.Space N,
      ⟪compactObservable (k:=k) R hR (endpoint β R hR J s x ω),
        tensorMean (k:=k) β R hR J b (endpoint β R hR J s x ω)⟫_ℝ
        ∂VectorBrownian.law N ∂sphereLaw N)=
      ∫x : State N,∫ω : VectorBrownian.Space N,
      ⟪compactObservable (k:=k) R hR (endpoint β R hR J s x ω),
        compactObservable (k:=k) R hR (endpoint β R hR J (s+b) x ω)⟫_ℝ
        ∂VectorBrownian.law N ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [sphereLaw_support (by omega : 1≤N)] with x hx
    have hxS : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
    exact (compact_waiting_inner_identity (Nat.ne_of_gt hN) β R hR hNR J
      (fun t omega => endpoint β R hR J t x omega)
      (fun T => jointProcess_physical (Nat.ne_of_gt hN) (VectorBrownian.driver N)
        β R hR hNR J x hxS T)
      (jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J x hxS) s b).symm
  change (∫x : State N,∫ω : VectorBrownian.Space N,
    ⟪compactObservable (k:=k) R hR (endpoint β R hR J s x ω),
      tensorMean (k:=k) β R hR J b (endpoint β R hR J s x ω)⟫_ℝ
      ∂VectorBrownian.law N ∂sphereLaw N)=_
  rw [he]
  change (∫x : State N,∫omega : VectorBrownian.Space N,
    ⟪compactObservable (k:=k) R hR (initialWaiting β R hR J s (x,omega)),
      compactObservable (k:=k) R hR (initialWaiting β R hR J (s+b) (x,omega))⟫_ℝ
      ∂VectorBrownian.law N ∂sphereLaw N)=_
  rw [←integral_prod _ (compact_samePath_integrable hN β R hR hNR J s b)]
  change (∫eta : State N×VectorBrownian.Space N,
    ⟪compactObservable (k:=k) R hR (initialWaiting β R hR J s eta),
      compactObservable (k:=k) R hR (initialWaiting β R hR J (s+b) eta)⟫_ℝ ∂initialLaw N)=_
  unfold samePathMoment
  apply integral_congr_ae
  filter_upwards [initialWaiting_onSphere hN β R hR hNR J s,
    initialWaiting_onSphere hN β R hR hNR J (s+b)] with eta hs ht
  rw [(compactObservable_eventuallyEq R hR hNR hs).eq_of_nhds,
    (compactObservable_eventuallyEq R hR hNR ht).eq_of_nhds]
  exact observable_inner hN _ _

theorem initialForkMoment_measurable (β R : ℝ≥0) (hR : 0<(R:ℝ)) (s a b : ℝ≥0) :
    Measurable (fun J : Disorder N p => initialForkMoment (k:=k) β R hR J s a b) :=
  waitingForkMoment_measurable (initialLaw N) (initialWaiting_joint_measurable β R hR s)
    β R hR a b

theorem samePathMoment_measurable (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (s b : ℝ≥0) :
    Measurable (fun J : Disorder N p => samePathMoment (k:=k) β R hR J s b) := by
  have he : (fun J : Disorder N p => samePathMoment (k:=k) β R hR J s b)=
      (fun J => initialForkMoment (k:=k) β R hR J s 0 b) :=
    funext (fun J => (initial_zero_branch_eq_same_path hN β R hR hNR J s b).symm)
  rw [he]
  exact initialForkMoment_measurable β R hR s 0 b

/-- The preceding forward density realizes the literal sphere-initial
physical waiting law. This is a law input, and contains no fork identity
or disorder measurability of the target current. -/
@[expose] def WaitingDensityLaw (β R : ℝ≥0) (hR : 0<(R:ℝ)) (E : FisherDensity N p β) : Prop :=
  ∀(J : Disorder N p) (s : ℝ≥0),HasLaw (initialWaiting β R hR J s)
    ((sphereLaw N).withDensity (fun x => ENNReal.ofReal (E.ρ J s x))) (initialLaw N)

theorem density_slice_measurable (β : ℝ≥0) (E : FisherDensity N p β)
    (J : Disorder N p) (t : ℝ) : Measurable (E.ρ J t) := by
  have hh := (E.smooth J).continuous.measurable.comp
    ((measurable_const : Measurable (fun _ : State N => t)).prodMk measurable_id)
  simpa only [Function.comp_def,Function.uncurry_def,id_eq] using hh

/-- The printed left endpoint is a genuine two-independent-future
fork, averaged over the actual uniform sphere initial law. -/
theorem pairing_zero_eq_fork (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (E : FisherDensity N p β)
    (hLaw : WaitingDensityLaw β R hR E) (J : Disorder N p) (T a d : ℝ≥0) :
    actualTensorPairing (k:=k) β R hR E J T a d 0=
      initialForkMoment (k:=k) β R hR J T a d := by
  have he := waitingForkMoment_eq_density (k:=k) (initialWaiting_measurable β R hR J T)
    hN β R hR hNR J a d (density_slice_measurable β E J T)
    (fun x => (E.positive J T x).le) (hLaw J T)
  simpa only [actualTensorPairing,initialForkMoment,add_zero,sub_zero,realTensorMean,
    Real.toNNReal_coe] using he.symm

/-- The printed right endpoint is the literal same-path correlation
moment at times T+a and T+2a+d, for arbitrary k. -/
theorem pairing_age_eq_same_path (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (E : FisherDensity N p β)
    (hLaw : WaitingDensityLaw β R hR E) (J : Disorder N p) (T a d : ℝ≥0) :
    actualTensorPairing (k:=k) β R hR E J T a d a=
      samePathMoment (k:=k) β R hR J (T+a) (a+d) := by
  have he := waitingForkMoment_eq_density (k:=k)
    (initialWaiting_measurable β R hR J (T+a)) hN β R hR hNR J 0 (a+d)
    (density_slice_measurable β E J (T+a))
    (fun x => (E.positive J (T+a) x).le) (hLaw J (T+a))
  have hp : actualTensorPairing (k:=k) β R hR E J T a d a=
      initialForkMoment (k:=k) β R hR J (T+a) 0 (a+d) := by
    simpa only [actualTensorPairing,initialForkMoment,sub_self,realTensorMean,
      ←NNReal.coe_add,Real.toNNReal_coe,Real.toNNReal_zero,add_comm] using he.symm
  exact hp.trans (initial_zero_branch_eq_same_path hN β R hR hNR J (T+a) (a+d))

/-- Endpoint disorder measurability comes from the genuine joint SDE
family and independent Wiener integration, without a joint density
measurability premise. -/
theorem pairing_increment_measurable (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (E : FisherDensity N p β)
    (hLaw : WaitingDensityLaw β R hR E) (T a d : ℝ≥0) :
    Measurable (fun J : Disorder N p => actualTensorPairing (k:=k) β R hR E J T a d a-
      actualTensorPairing (k:=k) β R hR E J T a d 0) := by
  have he : (fun J : Disorder N p => actualTensorPairing (k:=k) β R hR E J T a d a-
      actualTensorPairing (k:=k) β R hR E J T a d 0)=
      (fun J => samePathMoment (k:=k) β R hR J (T+a) (a+d)-
        initialForkMoment (k:=k) β R hR J T a d) := by
    funext J
    rw [pairing_age_eq_same_path hN β R hR hNR E hLaw,
      pairing_zero_eq_fork hN β R hR hNR E hLaw]
  rw [he]
  exact (samePathMoment_measurable hN β R hR hNR (T+a) (a+d)).sub
    (initialForkMoment_measurable β R hR T a d)

end SphericalAging.ActualSphereForkEndpoints
