module

public import SphericalAging.ActualSphereBackwardIto

public section

/-! Genuine Brownian backward-martingale variance from the actual
space-time Itô formula and full-vector Itô isometry. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereBackwardVariance
open HardSphereDynamics LocalSDE VectorIto AnnealedSDECore MultivariateTaylor
open ActualSphereTransition ActualSphereBackwardIto PhysicalC2Ito
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

omit [IsProbabilityMeasure P] in
lemma integral_sq_lp (U : Lp ℝ 2 P) : (∫ ω,(U : Ω → ℝ) ω^2 ∂P)=‖U‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  exact integral_congr_ae (.of_forall (fun ω => by
    simp only [RCLike.inner_apply,conj_trivial,pow_two]))

lemma vectorIto_sum_rows (D : BrownianDriver N P F)
    (V : Fin N → Fin N → PredictableProcessL2 F P) :
    vectorIto D (fun j => ∑ i,V i j)=∑ i,vectorIto D (V i) := by
  unfold vectorIto
  simp only [map_sum]
  exact Finset.sum_comm

variable {p : ℕ}

/-- Exact true Brownian innovation variance for every spatially C² actual
transition test, with the actual backward gradient contracted against the
physical sphere noise. Random initial states retain their conditional mean. -/
theorem backward_transition_variance (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    {Z0 : VectorBrownian.Space N → State N}
    (X : ℝ≥0 → VectorBrownian.Space N → State N) (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω))
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (hreg : SpatialC2Transition β R hR J f) :
    (∫ ω,(f (X T ω)-transition (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J T f (Z0 ω))^2 ∂VectorBrownian.law N)=
    ∫ s in Ioc (0 : ℝ≥0) T,∫ ω,∑ j : Fin N,
      (fderiv ℝ (transition (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR J (T-s) f) (X s ω) (noiseColumn (X s ω) j))^2
          ∂VectorBrownian.law N ∂nonnegativeLebesgueMeasure := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let P₀ := VectorBrownian.law N
  let F₀ := NullAugmentation.augment (VectorBrownian.filtration N) P₀
  let g (j : Fin N) (s : ℝ≥0) (ω : VectorBrownian.Space N) :=
    fderiv ℝ (transition D β R hR J (T-s) f) (X s ω) (noiseColumn (X s ω) j)
  obtain ⟨V,hV,he⟩ := backward_transition_ito hN β R hR hNR J X T hX hSphere hf hreg
  let U (j : Fin N) : PredictableProcessL2 F₀ P₀ := ∑ i,V i j
  have hU (j : Fin N) : (U j : TimeProcessL2 P₀)=ᵐ[nonnegativeLebesgueMeasure.prod P₀]
      FourPapersCommon.continuousAdaptedTimeCut (g j) T := by
    have hcoe := Lp.coeFn_fun_finsetSum Finset.univ (fun i => (V i j : TimeProcessL2 P₀))
    have hrows := ae_all_iff.mpr (fun i : Fin N => hV i j)
    filter_upwards [hcoe,hrows] with q hq hv
    have hq' : (U j : TimeProcessL2 P₀) q=∑ i : Fin N,(V i j : TimeProcessL2 P₀) q := by
      simpa only [U,Submodule.coe_sum] using hq
    rw [hq']
    simp only [hv,FourPapersCommon.continuousAdaptedTimeCut]
    split_ifs with hs
    · exact (derivative_coordinates _ _ _).symm
    · simp
  have hsum : ∀ᵐ ω ∂P₀,(vectorIto D U : VectorBrownian.Space N → ℝ) ω=
      ∑ i : Fin N,(vectorIto D (V i) : VectorBrownian.Space N → ℝ) ω := by
    rw [show vectorIto D U=∑ i : Fin N,vectorIto D (V i) from vectorIto_sum_rows D V]
    exact Lp.coeFn_fun_finsetSum Finset.univ _
  have hinnov : (fun ω => f (X T ω)-transition D β R hR J T f (Z0 ω))=ᵐ[P₀]
      (vectorIto D U : VectorBrownian.Space N → ℝ) := by
    filter_upwards [he,hsum] with ω heω hsω
    linarith
  have hgint (j : Fin N) : Integrable
      (fun q => (FourPapersCommon.continuousAdaptedTimeCut (g j) T q)^2)
        (nonnegativeLebesgueMeasure.prod P₀) :=
    ((Lp.memLp (U j : TimeProcessL2 P₀)).integrable_sq).congr
      ((hU j).mono (fun _ h => congrArg (fun z : ℝ => z^2) h))
  have hnorm (j : Fin N) : ‖U j‖^2=
      ∫ q,(FourPapersCommon.continuousAdaptedTimeCut (g j) T q)^2
        ∂nonnegativeLebesgueMeasure.prod P₀ := by
    change ‖(U j : TimeProcessL2 P₀)‖^2=_
    rw [← integral_sq_lp (U j : TimeProcessL2 P₀)]
    exact integral_congr_ae ((hU j).mono (fun _ h => congrArg (fun z : ℝ => z^2) h))
  calc
    _ = ∫ ω,(vectorIto D U : VectorBrownian.Space N → ℝ) ω^2 ∂P₀ :=
      integral_congr_ae (hinnov.mono (fun _ h => congrArg (fun z : ℝ => z^2) h))
    _ = ∑ j : Fin N,‖U j‖^2 := by rw [integral_sq_lp, norm_sq_vectorIto]
    _ = ∫ q,∑ j : Fin N,(FourPapersCommon.continuousAdaptedTimeCut (g j) T q)^2
        ∂nonnegativeLebesgueMeasure.prod P₀ := by
      simp only [hnorm]
      exact (integral_finsetSum _ (fun j _ => hgint j)).symm
    _ = ∫ s in Ioc (0 : ℝ≥0) T,∫ ω,∑ j : Fin N,(g j s ω)^2 ∂P₀
        ∂nonnegativeLebesgueMeasure := by
      rw [integral_prod _ (integrable_finsetSum _ (fun j _ => hgint j)),
        ← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      exact .of_forall (fun s => by
        by_cases hs : s∈Ioc (0 : ℝ≥0) T
        · simp only [FourPapersCommon.continuousAdaptedTimeCut,if_pos hs,indicator_of_mem hs]
        · simp only [FourPapersCommon.continuousAdaptedTimeCut,if_neg hs,zero_pow (by decide : (2 : ℕ)≠0),
            Finset.sum_const_zero,integral_zero,indicator_of_notMem hs])

end SphericalAging.ActualSphereBackwardVariance
