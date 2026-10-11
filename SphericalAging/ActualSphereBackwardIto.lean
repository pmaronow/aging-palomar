module

public import SphericalAging.PhysicalSpaceTimeIto
public import SphericalAging.ActualSphereBackwardMartingale
public import SphericalAging.ActualC2BackwardGenerator

public section

/-! Actual backward transition stochastic-integral representation. The only
analytic boundary is spatial C² and joint continuity of its spatial derivatives;
the backward equation is derived from the constructed SDE and semigroup. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereBackwardIto
open HardSphereDynamics LocalSDE VectorIto AnnealedSDECore MultivariateTaylor
open ActualSphereTransition ActualC2BackwardGenerator PhysicalSpaceTimeIto
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Explicit regularity of the actual transition observable. These fields
assert no martingale, backward equation, bracket, or variance identity. -/
structure SpatialC2Transition (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) (f : State N → ℝ) : Prop where
  slices : ∀ t : ℝ≥0,ContDiff ℝ 2
    (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t f)
  value : Continuous (fun q : ℝ≥0 × State N =>
    transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J q.1 f q.2)
  first : Continuous (fun q : ℝ≥0 × State N => fderiv ℝ
    (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J q.1 f) q.2)
  second : Continuous (fun q : ℝ≥0 × State N => Hessian
    (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J q.1 f) q.2)

/-- Genuine time-dependent backward-mean Itô representation, with all
predictable stochastic rows identified with the true spatial derivative. -/
theorem backward_transition_ito (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    {Z0 : VectorBrownian.Space N → State N}
    (X : ℝ≥0 → VectorBrownian.Space N → State N) (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω))
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (hreg : SpatialC2Transition β R hR J f) :
    ∃ V : Fin N → Fin N → PredictableProcessL2
      (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)) (VectorBrownian.law N),
      (∀ i j,(V i j : TimeProcessL2 (VectorBrownian.law N))=ᵐ[
        nonnegativeLebesgueMeasure.prod (VectorBrownian.law N)]
        FourPapersCommon.continuousAdaptedTimeCut
          (fun s ω => fderiv ℝ
            (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (T-s) f)
              (X s ω) (basisVector i)*noiseColumn (X s ω) j i) T) ∧
      ∀ᵐ ω ∂VectorBrownian.law N,f (X T ω)=
        transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J T f (Z0 ω)+
          ∑ i : Fin N,(vectorIto (NullAugmentation.driver (VectorBrownian.driver N)) (V i) :
            VectorBrownian.Space N → ℝ) ω := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let u : ℝ → State N → ℝ := fun s => transition D β R hR J ((T : ℝ)-s).toNNReal f
  let udot : ℝ → State N → ℝ := fun s x => -SphereGenerator.coefficientGenerator β J (u s) x
  have ht (s : ℝ≥0) : ((T : ℝ)-(s : ℝ)).toNNReal=T-s := by
    rfl
  have huC2 (s : ℝ≥0) : ContDiff ℝ 2 (u s) := hreg.slices _
  have huc : Continuous (fun q : ℝ≥0 × State N => u q.1 q.2) :=
    hreg.value.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)
  have huD : Continuous (fun q : ℝ≥0 × State N => fderiv ℝ (u q.1) q.2) :=
    hreg.first.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)
  have huH : Continuous (fun q : ℝ≥0 × State N => Hessian (u q.1) q.2) :=
    hreg.second.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)
  have huG : Continuous (fun q : ℝ≥0 × State N => SphereGenerator.coefficientGenerator β J (u q.1) q.2) := by
    unfold SphereGenerator.coefficientGenerator
    exact (huD.clm_apply ((contDiff_hamiltonianDrift β J).continuous.comp continuous_snd)).add
      ((continuous_finsetSum Finset.univ (fun j _ =>
        (huH.clm_apply ((contDiff_noiseColumn j).continuous.comp continuous_snd)).clm_apply
          ((contDiff_noiseColumn j).continuous.comp continuous_snd))).const_mul _)
  have htime : ∀ᵐ ω ∂VectorBrownian.law N,
      (∀ r∈Icc (0 : ℝ) T,ContinuousOn (fun s => u s (X r.toNNReal ω)) (Icc 0 T)) ∧
      (∀ r∈Icc (0 : ℝ) T,∀ s∈Ioo (0 : ℝ) T,
        HasDerivAt (fun a => u a (X r.toNNReal ω)) (udot s (X r.toNNReal ω)) s) ∧
      ContinuousOn (fun q : ℝ × ℝ => udot q.1 (X q.2.toNNReal ω))
        (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T) := by
    filter_upwards [hSphere,hX.2.2.1] with ω hs hc
    refine ⟨?_,?_,?_⟩
    · intro r hr
      exact ((ActualSphereMeanTimeC2.transition_time_continuous_onSphere hN β R hR hNR J _
        (hs r.toNNReal) f hf.continuous).comp
          (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))).continuousOn
    · intro r hr s hsT
      have hpos : 0<(T : ℝ)-s := sub_pos.mpr hsT.2
      have hd := transition_backward_hasDerivAt_of_contDiff hN β R hR hNR J _ (hs r.toNNReal) hf
        ((T : ℝ)-s) hpos (hreg.slices _)
      have hline : HasDerivAt (fun a : ℝ => (T : ℝ)-a) (-1) s :=
        by convert (hasDerivAt_id s).const_sub (T : ℝ) using 1 <;> rfl
      simpa only [u,udot,Function.comp_def,mul_neg_one] using hd.comp s hline
    · have hmap : Continuous (fun q : ℝ × ℝ =>
          (q.1.toNNReal,X q.2.toNNReal ω)) :=
        (continuous_real_toNNReal.comp continuous_fst).prodMk
          (hc.comp (continuous_real_toNNReal.comp continuous_snd))
      apply ((huG.neg).comp hmap).continuousOn.congr
      intro q hq
      dsimp only [udot,Function.comp_def,Pi.neg_apply]
      rw [Real.coe_toNNReal _ hq.1.1]
  obtain ⟨V,hV,he⟩ := physical_spaceTime_ito_formula D β J T hX hSphere R hR hNR
    huC2 huc huD huH htime
  refine ⟨V,?_,?_⟩
  · intro i j
    simpa only [u,ht] using hV i j
  · filter_upwards [he,hX.2.2.1] with ω heω hc
    have hg : IntegrableOn (fun s : ℝ≥0 => SphereGenerator.coefficientGenerator β J (u s) (X s ω))
        (Ioc (0 : ℝ≥0) T) nonnegativeLebesgueMeasure :=
      (((huG.comp (continuous_id.prodMk hc)).continuousOn).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hcancel : (∫ s in Ioc (0 : ℝ≥0) T,udot s (X s ω) ∂nonnegativeLebesgueMeasure)+
        (∫ s in Ioc (0 : ℝ≥0) T,SphereGenerator.coefficientGenerator β J (u s) (X s ω) ∂nonnegativeLebesgueMeasure)=0 := by
      dsimp only [udot]
      rw [integral_neg]
      ring
    have h0 : u 0=transition D β R hR J T f := by
      dsimp only [u]
      simp only [sub_zero,Real.toNNReal_coe]
    have hT : u T=f := by
      funext x
      dsimp only [u]
      simp only [sub_self,Real.toNNReal_zero]
      exact ActualSphereTransition.transition_zero D β R hR J f x
    rw [h0,hT] at heω
    linarith

end SphericalAging.ActualSphereBackwardIto
