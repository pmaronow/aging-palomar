module

public import SphericalAging.ActualSphereForkEndpoints
public import SphericalAging.ActualOverlapConcentration
public import SphericalAging.TwoMomentL2Transfer

public section

/-! Literal two-independent-future overlap law and its full annealed
moments. The same-path law is identified with the actual global SDE. -/
noncomputable section
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualForkOverlapLaw
open Set Filter MeasureTheory ProbabilityTheory FiniteModel HardSphereDynamics
open ActualSphereForkMoment ActualSphereForkEndpoints ActualSphereTransition
open ActualModelOverlapVariance ActualSphereBackwardIto ActualBackgroundOverlapLaw
open scoped Topology NNReal ENNReal InnerProductSpace

@[expose] abbrev ForkSample (N p : ℕ) := Disorder N p×
  ((State N×VectorBrownian.Space N)×(VectorBrownian.Space N×VectorBrownian.Space N))

@[expose] def forkLaw (N p : ℕ) : Measure (ForkSample N p) :=
  (disorderLaw N p).prod ((initialLaw N).prod
    ((VectorBrownian.law N).prod (VectorBrownian.law N)))

instance {N p : ℕ} : IsProbabilityMeasure (forkLaw N p) := by unfold forkLaw;infer_instance

@[expose] def forkOverlap {N p : ℕ} (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (T a d : ℝ≥0) (z : ForkSample N p) : ℝ :=
  momentIntegrand (k:=1) β R hR z.1 a d
    (initialWaiting β R hR z.1 T z.2.1) z.2.2

set_option maxHeartbeats 200000 in
theorem forkOverlap_measurable {N p : ℕ} (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (T a d : ℝ≥0) : Measurable (forkOverlap (N:=N) (p:=p) β R hR T a d) := by
  have hx : Measurable (fun z : ForkSample N p => initialWaiting β R hR z.1 T z.2.1) :=
    (initialWaiting_joint_measurable (N:=N) (p:=p) β R hR T).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have harg : Measurable (fun z : ForkSample N p =>
      ((z.1,initialWaiting β R hR z.1 T z.2.1),z.2.2)) :=
    (measurable_fst.prodMk hx).prodMk (measurable_snd.comp measurable_snd)
  have hh := (momentIntegrand_joint_measurable (N:=N) (p:=p) (k:=1) β R hR a d).comp harg
  have hdef : forkOverlap (N:=N) (p:=p) β R hR T a d=
      (fun z => momentIntegrand (k:=1) β R hR z.1 a d
        (initialWaiting β R hR z.1 T z.2.1) z.2.2) := rfl
  rw [hdef]
  simpa only [Function.comp_def] using hh

theorem forkOverlap_abs_le_one {N p : ℕ} (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (T a d : ℝ≥0) :
    ∀ᵐz ∂forkLaw N p,|forkOverlap β R hR T a d z|≤1 := by
  have hm : MeasurableSet {z : ForkSample N p | |forkOverlap β R hR T a d z|≤1} :=
    measurableSet_le (continuous_abs.measurable.comp
      (forkOverlap_measurable (N:=N) (p:=p) β R hR T a d)) measurable_const
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  apply ae_of_all
  intro J
  have hf : Measurable (fun z : (State N×VectorBrownian.Space N)×
      (VectorBrownian.Space N×VectorBrownian.Space N) =>
      forkOverlap β R hR T a d (J,z)) :=
    (forkOverlap_measurable (N:=N) (p:=p) β R hR T a d).comp (measurable_const.prodMk measurable_id)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
    (continuous_abs.measurable.comp hf) measurable_const)).mpr
  filter_upwards [initialWaiting_onSphere hN β R hR hNR J T] with eta heta
  have hs := jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N)
    β R hR hNR J (initialWaiting β R hR J T eta) heta
  have h1 := (measurePreserving_fst (μ:=VectorBrownian.law N) (ν:=VectorBrownian.law N)).quasiMeasurePreserving.ae hs
  have h2 := (measurePreserving_snd (μ:=VectorBrownian.law N) (ν:=VectorBrownian.law N)).quasiMeasurePreserving.ae hs
  filter_upwards [h1,h2] with omega ho1 ho2
  simpa only [forkOverlap,momentIntegrand,pow_one,endpoint,FiniteCorrelationIto.overlap,
    Function.comp_def] using
    FiniteCorrelationIto.overlap_abs_le_one hN (ho1 a) (ho2 d)

theorem forkOverlap_memLp {N p : ℕ} (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (T a d : ℝ≥0) :
    MemLp (forkOverlap (p:=p) β R hR T a d) 2 (forkLaw N p) :=
  MemLp.of_bound (forkOverlap_measurable (N:=N) (p:=p) β R hR T a d).aestronglyMeasurable 1
    (by simpa only [Real.norm_eq_abs] using forkOverlap_abs_le_one hN β R hR hNR T a d)

theorem forkOverlap_moment {N p k : ℕ} (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (T a d : ℝ≥0) :
    (∫z,(forkOverlap (p:=p) β R hR T a d z)^k ∂forkLaw N p)=
      ∫J,initialForkMoment (k:=k) β R hR J T a d ∂disorderLaw N p := by
  have hi : Integrable (fun z => (forkOverlap (p:=p) β R hR T a d z)^k) (forkLaw N p) :=
    Integrable.of_bound ((forkOverlap_measurable (N:=N) (p:=p) β R hR T a d).pow_const k).aestronglyMeasurable 1
      ((forkOverlap_abs_le_one hN β R hR hNR T a d).mono (fun z hz => by
        rw [Real.norm_eq_abs,abs_pow]
        exact pow_le_one₀ (abs_nonneg _) hz))
  rw [forkLaw,integral_prod _ hi]
  simp only [forkOverlap,momentIntegrand,pow_one,initialForkMoment,waitingForkMoment]

@[expose] def sameOverlap {N p : ℕ} (β R : ℝ≥0) (hR : 0<(R:ℝ)) (s t : ℝ≥0)
    (z : Disorder N p×(State N×VectorBrownian.Space N)) : ℝ :=
  ⟪initialWaiting β R hR z.1 s z.2,initialWaiting β R hR z.1 t z.2⟫_ℝ/(N:ℝ)

theorem sameOverlap_measurable {N p : ℕ} (β R : ℝ≥0) (hR : 0<(R:ℝ)) (s t : ℝ≥0) :
    Measurable (sameOverlap (N:=N) (p:=p) β R hR s t) :=
  (((continuous_fst.inner continuous_snd).measurable.comp
    ((initialWaiting_joint_measurable (N:=N) (p:=p) β R hR s).prodMk
      (initialWaiting_joint_measurable (N:=N) (p:=p) β R hR t))).div_const _)

theorem sameOverlap_moment_actual {N p k : ℕ} (β R : ℝ≥0) (hR : 0<(R:ℝ)) (s t : ℝ≥0) :
    (∫z,(sameOverlap (p:=p) β R hR s t z)^k ∂(disorderLaw N p).prod (initialLaw N))=
      ∫z,(actualOverlap (p:=p) β R hR s t z)^k ∂AnnealedModelLaw.law N p := by
  have he := (measurePreserving_prodAssoc (disorderLaw N p) (SphereInitialLaw.sphereLaw N)
    (VectorBrownian.law N)).integral_comp'
    (fun z => (sameOverlap (p:=p) β R hR s t z)^k)
  have hae := (actualOverlap_ae_joint (N:=N) (p:=p) β R hR s t).pow_const k
  exact he.symm.trans (integral_congr_ae hae.symm)

theorem sameOverlap_abs_le_one {N p : ℕ} (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (s t : ℝ≥0) :
    ∀ᵐz ∂(disorderLaw N p).prod (initialLaw N),|sameOverlap β R hR s t z|≤1 := by
  have hm : MeasurableSet {z : Disorder N p×(State N×VectorBrownian.Space N) |
      |sameOverlap β R hR s t z|≤1} :=
    measurableSet_le (continuous_abs.measurable.comp
      (sameOverlap_measurable (N:=N) (p:=p) β R hR s t)) measurable_const
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  apply ae_of_all
  intro J
  filter_upwards [initialWaiting_onSphere hN β R hR hNR J s,
    initialWaiting_onSphere hN β R hR hNR J t] with eta hs ht
  simpa only [sameOverlap,FiniteCorrelationIto.overlap,Function.comp_def] using
    FiniteCorrelationIto.overlap_abs_le_one hN hs ht

theorem samePathMoment_annealed_actual {N p k : ℕ} (hN : 0<N)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (s b : ℝ≥0) :
    (∫J,samePathMoment (k:=k) β R hR J s b ∂disorderLaw N p)=
      ∫z,(actualOverlap (p:=p) β R hR s (s+b) z)^k ∂AnnealedModelLaw.law N p := by
  have hi : Integrable (fun z => (sameOverlap (p:=p) β R hR s (s+b) z)^k)
      ((disorderLaw N p).prod (initialLaw N)) := by
    apply Integrable.of_bound
      ((sameOverlap_measurable (N:=N) (p:=p) β R hR s (s+b)).pow_const k).aestronglyMeasurable 1
    filter_upwards [sameOverlap_abs_le_one (p:=p) hN β R hR hNR s (s+b)] with z hz
    rw [Real.norm_eq_abs,abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hz
  rw [←sameOverlap_moment_actual β R hR s (s+b),integral_prod _ hi]
  rfl

end SphericalAging.ActualForkOverlapLaw
