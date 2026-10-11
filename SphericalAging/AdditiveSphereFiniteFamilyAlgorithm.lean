module

public import SphericalAging.AdditiveSphereAlgorithmSampler
public import SphericalAging.FiniteFamilyBallApproximation
public import SphericalAging.ActualSphereMarkovRestart

public section

/-! A genuine finite-family approximation of wholepath-driven physical
sphere endpoints. The coefficient Lipschitz constant is uniform in the
dimension, and the actual projected-mean error converges to zero. The
only seed input is its literal initial/entire-Wiener-path probability law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.AdditiveSphereFiniteFamilyAlgorithm
open FiniteModel HardSphereDynamics LocalSDE LandscapeMetricProjection ActualSphereTransition
open AdditiveSphereGaussianApproximation AdditiveSphereAlgorithmSampler
open FiniteFamilyBallApproximation AnnealedHamiltonianEnergyStein ActualSphereMarkovRestart
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

variable {N p : ℕ} {SeedSpace : Type*} [MeasurableSpace SeedSpace]
  {μ : Measure SeedSpace} [IsProbabilityMeasure μ]

/-- The literal physical endpoint driven by the full path selected by the seed. -/
@[expose] def endpoint (β : ℝ≥0) (t : ℝ≥0) (ψ : SeedSpace→State N×VectorBrownian.Space N)
    (z : SeedSpace×Disorder N p) : State N :=
  jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
    (modelRadius_pos N) (z.2,(ψ z.1).1) t (ψ z.1).2

theorem endpoint_memLp (β : ℝ≥0) (t : ℝ≥0) (ψ : SeedSpace→State N×VectorBrownian.Space N)
    (hψ : MeasurePreserving ψ μ ((SphereInitialLaw.sphereLaw N).prod (VectorBrownian.law N))) :
    MemLp (endpoint (p:=p) β t ψ) 2 (μ.prod (disorderLaw N p)) := by
  have he := annealedGlobal_eq_joint (ρ:=AnnealedModelLaw.parameterLaw N p)
    (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1) (modelRadius_pos N)
      (AnnealedModelLaw.parameter_disorder_memLp N p) t
  change modelProcess N p β t=ᵐ[AnnealedModelLaw.law N p]
    (fun q => jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
      β (N+1) (modelRadius_pos N) q.1 t q.2) at he
  have hm : MemLp (fun q : (Disorder N p×State N)×VectorBrownian.Space N =>
      jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
        (modelRadius_pos N) q.1 t q.2) 2 (AnnealedModelLaw.law N p) :=
    (ActualWeightedWiener.model_memLp N p β t).ae_eq he
  have hΦ := (regroup_measurePreserving (p:=p) (SphereInitialLaw.sphereLaw N)).comp
    (hψ.prod (MeasurePreserving.id (disorderLaw N p)))
  exact hm.comp_measurePreserving hΦ

/-- Every genuine finite family of independent-initial/wholepath seed
marginals admits a single globally coefficient-Lipschitz projected mean
algorithm. Correlation between the selected branch paths is permitted. -/
theorem exists_finite_family_algorithm {K : ℕ} (hK : 0<K) {p : ℕ} (hp : 2≤p)
    (dim : ℕ→ℕ) (hDim : ∀n,2≤dim n) (hDimTop : Tendsto dim atTop atTop)
    (Seed : ℕ→Type*) [∀n,MeasurableSpace (Seed n)]
    (μ : ∀n,Measure (Seed n)) [∀n,IsProbabilityMeasure (μ n)]
    (ψ : ∀n,Fin K→Seed n→State (dim n)×VectorBrownian.Space (dim n))
    (hψ : ∀n b,MeasurePreserving (ψ n b) (μ n)
      ((SphereInitialLaw.sphereLaw (dim n)).prod (VectorBrownian.law (dim n))))
    (β : ℝ≥0) (T t : ℝ≥0) (ht : t≤T) (Q : ℝ) (hQ : 0<Q) :
    ∃ A : ∀n,Seed n×Disorder (dim n) p→State (dim n),
      (∀n,Measurable (A n)) ∧
      (∀n ξ,LipschitzWith (normalizedRate (AdditiveSphereJointParameter.jointRate p β (landscapeCutoff p) T) Q)
        (fun J : CoefficientSpace (dim n) p => A n (ξ,J.ofLp))) ∧
      (∀n ξ J,‖A n (ξ,J)‖≤Real.sqrt (dim n)) ∧
      Tendsto (fun n => (∫z,‖A n z-output Q (fun b => endpoint β t (ψ n b) z)‖^2
        ∂(μ n).prod (disorderLaw (dim n) p))/(dim n:ℝ)) atTop (𝓝 0) := by
  have hρ n : ∀ᵐx ∂SphereInitialLaw.sphereLaw (dim n),OnSphere x :=
    (SphereInitialLaw.sphereLaw_support (by have := hDim n;omega : 1≤dim n)).mono
      (fun x hx => (onSphere_iff_norm_sq x).mpr hx)
  have hExists n b := exists_actual_seed_ball_algorithm (hDim n) hp (VectorBrownian.driver (dim n))
    β (dim n+1) (modelRadius_pos (dim n)) (modelRadius_sq (dim n)) T t ht
      (SphereInitialLaw.sphereLaw (dim n)) (hρ n) (μ n) (ψ n b) (hψ n b)
  choose B hBmeas hBLip hBBall hBError using hExists
  let A : ∀n,Seed n×Disorder (dim n) p→State (dim n) :=
    fun n z => output Q (fun b => B n b z)
  have hBmem n b : MemLp (B n b) 2 ((μ n).prod (disorderLaw (dim n) p)) :=
    MemLp.of_bound (hBmeas n b).aestronglyMeasurable (Real.sqrt (dim n))
      (.of_forall (fun z => hBBall n b z.1 z.2))
  have hEmem n b : MemLp (endpoint (p:=p) β t (ψ n b)) 2 ((μ n).prod (disorderLaw (dim n) p)) :=
    endpoint_memLp β t (ψ n b) (hψ n b)
  refine ⟨A,?_,?_,?_,?_⟩
  · intro n
    exact output_measurable (B n) (hBmeas n)
  · intro n ξ
    change LipschitzWith (normalizedRate (AdditiveSphereJointParameter.jointRate p β (landscapeCutoff p) T) Q)
      (fun J : CoefficientSpace (dim n) p => output Q (fun b => B n b (ξ,J.ofLp)))
    exact output_lipschitz (N:=dim n) (E:=CoefficientSpace (dim n) p) hK
      (AdditiveSphereJointParameter.jointRate p β (landscapeCutoff p) T) Q
        (fun b J => B n b (ξ,J.ofLp)) (fun b => hBLip n b ξ)
  · intro n ξ J
    exact output_norm_le Q _
  · have hBound n : (∫z,‖A n z-output Q (fun b => endpoint β t (ψ n b) z)‖^2
        ∂(μ n).prod (disorderLaw (dim n) p))/(dim n:ℝ)≤
          Q⁻¹*annealedErrorBound (dim n) p β T t := by
      exact output_normalized_error_le (by have := hDim n;omega : 0<dim n) hK hQ
        (B n) (fun b => endpoint β t (ψ n b)) (hBmem n) (hEmem n)
          (annealedErrorBound (dim n) p β T t) (fun b => by
            simpa only [endpoint,norm_sub_rev,integral_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using hBError n b)
    have hLimit := ((annealedErrorBound_tendsto_zero p β T t).comp hDimTop).const_mul Q⁻¹
    apply squeeze_zero' (.of_forall (fun n => div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (Nat.cast_nonneg _)))
      (.of_forall hBound)
    simpa only [mul_zero,Function.comp_def] using hLimit

end SphericalAging.AdditiveSphereFiniteFamilyAlgorithm
