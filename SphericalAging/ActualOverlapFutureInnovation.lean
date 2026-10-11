module

public import SphericalAging.ActualSphereLinearInnovation
public import SphericalAging.ActualOverlapBackwardTestDerivative
public import SphericalAging.ActualSphereMarkovRestart
public import SphericalAging.ActualSphereKernelSupport
public import SphericalAging.FiniteCorrelationIto
public import SphericalAging.ActualSphereLinearRegularity

public section

/-! Actual two-time future overlap innovation. The waiting observation
vector is random and correlated with the earlier path. Its true product
law with the independent future Wiener path is derived, then the actual
fixed-vector innovation estimate is integrated over that observed law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualOverlapFutureInnovation
open HardSphereDynamics ActualSphereTransition AnnealedSDECore ActualSphereBackwardIto
open ActualOverlapBackwardTestDerivative ActualSphereMarkovRestart
open BrownianFuturePath BrownianFutureFiltered ActualSphereLinearInnovation
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem future_innovation_variance_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    {Z0 : VectorBrownian.Space N → State N}
    (X : ℝ≥0 → VectorBrownian.Space N → State N)
    (hX : ∀ T,IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω))
    (s u : ℝ≥0) :
    (∫ ω,(⟪X s ω,X (s+u) ω⟫_ℝ/(N : ℝ)-
      overlapTest (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u (X s ω))^2
        ∂VectorBrownian.law N)≤
      (2*u/(N : ℝ))*Real.exp (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*u) := by
  let P := VectorBrownian.law N
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let F := NullAugmentation.augment (VectorBrownian.filtration N) P
  have hn : 0<N := by omega
  have hZa : Measurable[F s] (X s) := ((hX 0).2.1 s).measurable
  have hZm : Measurable (X s) := hZa.mono (F.le s) le_rfl
  let μ := P.map (X s)
  letI : IsProbabilityMeasure μ :=
    (hasLaw_map hZm.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hμs : ∀ᵐ z ∂μ,OnSphere z :=
    (ae_map_iff hZm.aemeasurable ActualSphereKernelSupport.measurableSet_onSphere).mpr
      (hSphere.mono (fun ω h => h s))
  let Y : State N × VectorBrownian.Space N → State N := fun q => jointProcess D β R hR (J,q.1) u q.2
  let g : State N → ℝ := overlapTest D β R hR J u
  let G : State N × VectorBrownian.Space N → ℝ := fun q => ⟪q.1,Y q⟫_ℝ/(N : ℝ)
  let E : State N × VectorBrownian.Space N → ℝ := fun q => (G q-g q.1)^2
  have hY : StronglyMeasurable Y := (jointProcess_measurable D β R hR).comp_measurable
    ((measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
  have hg : Continuous g := (overlapTest_differentiable (VectorBrownian.driver N) β R hR J u).continuous
  have hG : StronglyMeasurable G := (continuous_id.div_const (N : ℝ)).comp_stronglyMeasurable
    (measurable_fst.stronglyMeasurable.inner hY)
  have hE : StronglyMeasurable E := (hG.sub (hg.stronglyMeasurable.comp_measurable measurable_fst)).pow 2
  have hsp : ∀ᵐ q ∂μ.prod P,OnSphere q.1 ∧ OnSphere (Y q) := by
    have hm : MeasurableSet {q : State N × VectorBrownian.Space N | OnSphere q.1 ∧ OnSphere (Y q)} :=
      (ActualSphereKernelSupport.measurableSet_onSphere.preimage measurable_fst).inter
        (ActualSphereKernelSupport.measurableSet_onSphere.preimage hY.measurable)
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [hμs] with z hz
    exact (jointProcess_onSphere (Nat.ne_of_gt hn) (VectorBrownian.driver N) β R hR hNR J z hz).mono
      (fun ω h => ⟨hz,h u⟩)
  have hEi : Integrable E (μ.prod P) := by
    apply Integrable.of_bound hE.aestronglyMeasurable 4
    filter_upwards [hsp] with q hq
    have h1 : |G q|≤1 := FiniteCorrelationIto.overlap_abs_le_one hn hq.1 hq.2
    have h2 : |g q.1|≤1 := overlapTest_abs_le_one hn (VectorBrownian.driver N) β R hR hNR J u q.1 hq.1
    have hh : |G q-g q.1|≤2 := (abs_sub _ _).trans (by linarith)
    change ‖(G q-g q.1)^2‖≤4
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs,show (2 : ℝ)^2=4 by norm_num] using
      pow_le_pow_left₀ (abs_nonneg (G q-g q.1)) hh 2
  let φ : VectorBrownian.Space N → State N × VectorBrownian.Space N := fun ω => (X s ω,future s ω)
  have hφ : MeasurePreserving φ P (μ.prod P) := waiting_future_measurePreserving s (X s) hZa
  have hpull : (∫ ω,E (φ ω) ∂P)=∫ q,E q ∂μ.prod P := by
    rw [← hφ.map_eq]
    exact (integral_map hφ.measurable.aemeasurable hE.aestronglyMeasurable).symm
  have he : (fun ω => (⟪X s ω,X (s+u) ω⟫_ℝ/(N : ℝ)-g (X s ω))^2)=ᵐ[P]
      (fun ω => E (φ ω)) := by
    filter_upwards [actual_future_eq_joint (Nat.ne_of_gt hn) β R hR hNR J X hX hSphere s u] with ω hω
    change (⟪X s ω,X (s+u) ω⟫_ℝ/(N : ℝ)-g (X s ω))^2=
      (⟪X s ω,jointProcess D β R hR (J,X s ω) u (future s ω)⟫_ℝ/(N : ℝ)-g (X s ω))^2
    rw [hω]
  have hb : ∀ᵐ z ∂μ,(∫ ω,E (z,ω) ∂P)≤
      (2*u/(N : ℝ))*Real.exp (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*u) := by
    filter_upwards [hμs] with z hz
    have hh := normalized_linear_innovation_variance_le hN hp β R hR hNR J
      (jointProcess D β R hR (J,z)) u
      (jointProcess_physical (Nat.ne_of_gt hn) (VectorBrownian.driver N) β R hR hNR J z hz u)
      (jointProcess_onSphere (Nat.ne_of_gt hn) (VectorBrownian.driver N) β R hR hNR J z hz)
      z hz (ActualSphereLinearRegularity.linear_spatialC2Transition β R hR J ((N : ℝ)⁻¹ • z))
    convert hh using 1
    congr 1
    funext ω
    dsimp only [E,G,Y,g,overlapTest]
    rw [sub_div]
  change (∫ ω,(⟪X s ω,X (s+u) ω⟫_ℝ/(N : ℝ)-g (X s ω))^2 ∂P)≤_
  rw [integral_congr_ae he,hpull,integral_prod E hEi]
  have hh := integral_mono_of_nonneg
    (.of_forall (fun z => integral_nonneg (fun ω => sq_nonneg (G (z,ω)-g z))))
    (integrable_const ((2*u/(N : ℝ))*Real.exp
      (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*u))) hb
  simpa only [integral_const,probReal_univ,one_smul] using hh

end SphericalAging.ActualOverlapFutureInnovation
