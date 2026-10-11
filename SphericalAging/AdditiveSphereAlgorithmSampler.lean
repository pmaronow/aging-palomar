module

public import SphericalAging.AdditiveSphereRandomInitialApproximation

public section

/-! Actual independent algorithm seeds. Any genuine seed map preserving
the initial-state / entire-driver law pulls back the constructed ball
approximation, with an everywhere samplewise Euclidean coefficient bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.AdditiveSphereAlgorithmSampler
open FiniteModel HardSphereDynamics LocalSDE LandscapeMetricProjection ActualSphereTransition
open AdditiveSphereGaussianApproximation AdditiveSphereRandomInitialApproximation
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω SeedSpace : Type*} [MeasurableSpace Ω] [MeasurableSpace SeedSpace]
  {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Regrouping the independent seed and disorder retains the literal
Gaussian / initial / entire-driver product law. -/
@[expose] def regroup : ((State N×Ω)×Disorder N p)≃ᵐ((Disorder N p×State N)×Ω) :=
  MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc.symm

theorem regroup_measurePreserving (ρ : Measure (State N)) [IsProbabilityMeasure ρ] :
    MeasurePreserving (regroup (N:=N) (p:=p) (Ω:=Ω))
      ((ρ.prod P).prod (disorderLaw N p)) (((disorderLaw N p).prod ρ).prod P) :=
  (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (disorderLaw N p) ρ P)).comp Measure.measurePreserving_swap

/-- The seed law is the exact law of an independent sphere initial state
and a whole actual Brownian driver path. No algorithm error is an input. -/
theorem exists_actual_seed_ball_algorithm (hN : 2≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (T t : ℝ≥0) (ht : t≤T)
    (ρ : Measure (State N)) [IsProbabilityMeasure ρ] (hρ : ∀ᵐx ∂ρ,OnSphere x)
    (μ : Measure SeedSpace) [IsProbabilityMeasure μ] (ψ : SeedSpace→State N×Ω)
    (hψ : MeasurePreserving ψ μ (ρ.prod P)) :
    ∃ A : SeedSpace×Disorder N p→State N,
      Measurable A ∧
      (∀ξ,LipschitzWith (AdditiveSphereJointParameter.jointRate p β (landscapeCutoff p) T)
        (fun J : CoefficientSpace N p => A (ξ,J.ofLp))) ∧
      (∀ξ J,‖A (ξ,J)‖≤Real.sqrt N) ∧
      (∫z : SeedSpace×Disorder N p,
        ‖jointProcess (NullAugmentation.driver D₀) β R hR (z.2,(ψ z.1).1) t (ψ z.1).2-
          A z‖^2/(N:ℝ) ∂μ.prod (disorderLaw N p))≤annealedErrorBound N p β T t := by
  obtain ⟨G,hG,hLip,hBall,hError⟩ :=
    exists_actual_random_initial_ball_approximation hN hp D₀ β R hR hNR T t ht ρ hρ
  let A : SeedSpace×Disorder N p→State N := fun z =>
    G ((ψ z.1).2,(WithLp.toLp 2 z.2,(ψ z.1).1))
  have hA : Measurable A := hG.comp
    (((measurable_snd.comp hψ.measurable).comp measurable_fst).prodMk
      (((PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp measurable_snd).prodMk
        ((measurable_fst.comp hψ.measurable).comp measurable_fst)))
  refine ⟨A,hA,?_,?_,?_⟩
  · intro ξ
    apply LipschitzWith.of_dist_le_mul
    intro J K
    simpa only [A,WithLp.toLp_ofLp,Prod.dist_eq,dist_self,max_eq_left dist_nonneg] using
      (hLip (ψ ξ).2).dist_le_mul (J,(ψ ξ).1) (K,(ψ ξ).1)
  · intro ξ J
    exact hBall _ _
  · let f : (Disorder N p×State N)×Ω→ℝ := fun q =>
      ‖jointProcess (NullAugmentation.driver D₀) β R hR q.1 t q.2-
        G (q.2,(WithLp.toLp 2 q.1.1,q.1.2))‖^2/(N:ℝ)
    have hfm : Measurable f := by
      have hX : Measurable (fun q : (Disorder N p×State N)×Ω =>
          jointProcess (NullAugmentation.driver D₀) β R hR q.1 t q.2) :=
        (jointProcess_measurable (NullAugmentation.driver D₀) β R hR).measurable.comp
          (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
      have hY : Measurable (fun q : (Disorder N p×State N)×Ω =>
          G (q.2,(WithLp.toLp 2 q.1.1,q.1.2))) := hG.comp
        (measurable_snd.prodMk
          ((((PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp measurable_fst).comp
            measurable_fst).prodMk (measurable_snd.comp measurable_fst)))
      exact ((hX.sub hY).norm.pow_const 2).div_const _
    have hΦ := (regroup_measurePreserving (p:=p) ρ).comp
      (hψ.prod (MeasurePreserving.id (disorderLaw N p)))
    have he := hΦ.hasLaw.integral_comp hfm.aestronglyMeasurable
    change (∫z,f (regroup (ψ z.1,z.2)) ∂μ.prod (disorderLaw N p))≤_
    change (∫z,f (regroup (ψ z.1,z.2)) ∂μ.prod (disorderLaw N p))=
      (∫q,f q ∂((disorderLaw N p).prod ρ).prod P) at he
    rw [he]
    exact hError

end SphericalAging.AdditiveSphereAlgorithmSampler
