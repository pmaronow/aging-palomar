module

public import SphericalAging.ActualBackgroundOverlapVariance
public import SphericalAging.ActualSphereTransition

public section

/-! The constructed L² background overlap mean is exactly the Brownian
mean of the actual jointly measurable physical process. This identifies
the variance bound with the literal independent parameter/noise law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.ActualBackgroundOverlapLaw
open FiniteModel HardSphereDynamics HamiltonianPicardDependence
open ActualDisorderOverlapVariance ActualSphereOverlapDerivative ActualBackgroundOverlapVariance
open SphereInitialLaw
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def jointOverlap (D : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (s t : ℝ≥0) (q : (Disorder N p × State N) × Ω) : ℝ :=
  inner ℝ (ActualSphereTransition.jointProcess D β R hR q.1 s q.2)
    (ActualSphereTransition.jointProcess D β R hR q.1 t q.2)/(N : ℝ)

 lemma jointOverlap_stronglyMeasurable (D : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (s t : ℝ≥0) : StronglyMeasurable (jointOverlap (p := p) D β R hR s t) := by
  have hX (u : ℝ≥0) : StronglyMeasurable (fun q : (Disorder N p × State N) × Ω =>
      ActualSphereTransition.jointProcess D β R hR q.1 u q.2) :=
    (ActualSphereTransition.jointProcess_measurable D β R hR).comp_measurable
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hh : StronglyMeasurable (fun q : (Disorder N p × State N) × Ω =>
      inner ℝ (ActualSphereTransition.jointProcess D β R hR q.1 s q.2)
        (ActualSphereTransition.jointProcess D β R hR q.1 t q.2)) := (hX s).inner (hX t)
  exact (continuous_id.div_const (N : ℝ)).comp_stronglyMeasurable hh

 lemma terminalClass_ae_joint (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (J : Disorder N p) (x : State N) (T t : ℝ≥0) (ht : t≤T) :
    HamiltonianDisorderTerminalDerivative.stateClass (NullAugmentation.driver D₀) β R hR J x T t=ᵐ[P]
      ActualSphereTransition.jointProcess (NullAugmentation.driver D₀) β R hR (J,x) t := by
  have hg := GlobalSDE.process_eq_horizon (NullAugmentation.driver D₀)
    (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩) (noise_family_lipschitz N R hR) x T
  exact ((HamiltonianDisorderTerminalDerivative.stateClass_ae (NullAugmentation.driver D₀) β R hR J x T t).trans
    (hg.mono (fun _ h => (h t ht).symm))).trans
      ((ActualSphereTransition.jointProcess_ae (NullAugmentation.driver D₀) β R hR (J,x)).mono (fun _ h => (h t).symm))

 theorem backgroundMean_eq_joint_mean (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T) (q : Disorder N p × State N) :
    backgroundMean D₀ β R hR T s t q=
      ∫ ω,jointOverlap (NullAugmentation.driver D₀) β R hR s t (q,ω) ∂P := by
  unfold backgroundMean initialMean overlapMean
  rw [L2.inner_def,← integral_div]
  apply integral_congr_ae
  filter_upwards [terminalClass_ae_joint D₀ β R hR q.1 q.2 T s hs,
    terminalClass_ae_joint D₀ β R hR q.1 q.2 T t ht] with ω hωs hωt
  simp only [hωs,hωt,jointOverlap]

 theorem actual_joint_mean_background_variance (hN : 3≤N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T) (hT : 0<T) :
    variance (fun q : Disorder N p × State N =>
      ∫ ω,jointOverlap (NullAugmentation.driver D₀) β R hR s t (q,ω) ∂P)
      ((disorderLaw N p).prod (sphereLaw N))≤backgroundVarianceCeiling p β T/(N : ℝ) := by
  have he : (fun q : Disorder N p × State N =>
      ∫ ω,jointOverlap (NullAugmentation.driver D₀) β R hR s t (q,ω) ∂P)=
        backgroundMean D₀ β R hR T s t := funext (fun q => (backgroundMean_eq_joint_mean D₀ β R hR T s t hs ht q).symm)
  rw [he]
  exact actual_background_overlap_variance hN hp D₀ β R hR hNR T s t hs ht hT

end SphericalAging.ActualBackgroundOverlapLaw
