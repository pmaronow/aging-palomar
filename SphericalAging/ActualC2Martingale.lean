module

public import SphericalAging.ActualC2Dynkin
public import SphericalAging.ActualCoordinateMartingale

public section

/-! The actual general C² generator compensator has a genuine continuous
martingale version. Coherent prefix stochastic integrands are derived from
actual time-cut identifications rather than assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.ActualC2Martingale
open HardSphereDynamics LocalSDE AnnealedSDECore VectorIto PredictableItoTime PredictableDriftTime
open PhysicalC2Ito ActualC2Dynkin SharpRadialMoment
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma identified_timeCut_restrict (U V : PredictableProcessL2 F P) (G : ℝ≥0 → Ω → ℝ)
    (T t : ℝ≥0) (ht : t≤T)
    (hU : (U : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P] FourPapersCommon.continuousAdaptedTimeCut G T)
    (hV : (V : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P] FourPapersCommon.continuousAdaptedTimeCut G t) :
    V=FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t U := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hU,hV,FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F t U]
    with q hu hv hr
  rw [hv,hr]
  change _=(FourPapersCommon.FilteredBrownian.predictableTimeFrame t).indicator (U : TimeProcessL2 P) q
  by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) t
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left hq,
      Set.indicator_of_mem (show q ∈ FourPapersCommon.FilteredBrownian.predictableTimeFrame t from ⟨hq,mem_univ _⟩),hu,
      ite_eq_left (show q.1 ∈ Ioc (0 : ℝ≥0) T from ⟨hq.1,hq.2.trans ht⟩)]
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_right hq,
      Set.indicator_of_notMem (show q ∉ FourPapersCommon.FilteredBrownian.predictableTimeFrame t from fun h => hq h.1)]

/-- Every C² observable of the actual sphere process has a true continuous
martingale compensator, identified on a common event at all horizon times. -/
theorem exists_physical_C2_generator_martingale (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn D
      (fun _ i x => hamiltonianDrift β J x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ ω ∂P,∀ s,OnSphere (X s ω)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (T : ℝ≥0) :
    ∃ M : ℝ≥0 → Ω → ℝ,Martingale M F P ∧
      (∀ᵐ ω ∂P,Continuous (fun t => M t ω)) ∧
      ∀ᵐ ω ∂P,∀ t,t≤T → M t ω=f (X t ω)-f (Z0 ω)-
        ∫ s in (0 : ℝ)..(t : ℝ),SphereGenerator.coefficientGenerator β J f (X s.toNNReal ω) := by
  obtain ⟨U,hU,hformula⟩ := physical_C2_ito_formula D β J T (hX T) hXs R hR hNR hf
  choose Mi hMi hmod using (fun i : Fin N => exists_continuous_martingale_vectorProcess D (U i))
  let M : ℝ≥0 → Ω → ℝ := fun t ω => ∑ i : Fin N,Mi i t ω
  have hM : Martingale M F P := by
    have hsum (S : Finset (Fin N)) : Martingale (fun t ω => ∑ i ∈ S,Mi i t ω) F P := by
      induction S using Finset.induction_on with
      | empty => simp only [Finset.sum_empty];exact martingale_zero ℝ F P
      | @insert i S hi ih => simp only [Finset.sum_insert hi];exact (hMi i).add ih
    exact hsum Finset.univ
  have hMc : ∀ᵐ ω ∂P,Continuous (fun t => M t ω) := by
    filter_upwards [ae_all_iff.mpr (fun i : Fin N => (hmod i).continuous_paths)] with ω hω
    exact continuous_finsetSum Finset.univ (fun i _ => hω i)
  let G : ℝ≥0 → Ω → ℝ := fun s ω => SphereGenerator.coefficientGenerator β J f (X s ω)
  let cutG : ℝ≥0 × Ω → ℝ := FourPapersCommon.continuousAdaptedTimeCut G T
  have hGa : StronglyAdapted F G := fun s => (generator_continuous β J hf).comp_stronglyMeasurable ((hX 0).2.1 s)
  have hGc : ∀ᵐ ω ∂P,Continuous (fun s => G s ω) := (hX 0).2.2.1.mono
    (fun _ hc => (generator_continuous β J hf).comp hc)
  obtain ⟨K,hK⟩ := sphere_observable_bound _ (generator_continuous β J hf) R hR hNR X hXs
  have hcutInt := (timeCut_integrable G hGa hGc K hK T).prod_left_ae
  let C : ℝ≥0 → Ω → ℝ := fun t ω => f (X t ω)-f (Z0 ω)-primitive cutG t ω
  have hCc : ∀ᵐ ω ∂P,Continuous (fun t => C t ω) := by
    filter_upwards [(hX 0).2.2.1,hcutInt] with ω hxc hi
    exact ((hf.continuous.comp hxc).sub continuous_const).sub (primitive_continuous cutG ω hi)
  have hprefixIntegral (t : ℝ≥0) (ht : t≤T) (ω : Ω) : primitive cutG t ω=
      ∫ s in Ioc (0 : ℝ≥0) t,G s ω ∂nonnegativeLebesgueMeasure := by
    unfold primitive cutG
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp only [FourPapersCommon.continuousAdaptedTimeCut,
      ite_eq_left (show s ∈ Ioc (0 : ℝ≥0) T from ⟨hs.1,hs.2.trans ht⟩)]
  have hfixed (t : ℝ≥0) (ht : t≤T) : C t=ᵐ[P] M t := by
    obtain ⟨V,hV,he⟩ := physical_C2_ito_formula D β J t (hX t) hXs R hR hNR hf
    have hclass (i : Fin N) : vectorIto D (V i)=vectorProcessLp D (U i) t := by
      unfold vectorProcessLp
      congr 1
      funext j
      exact identified_timeCut_restrict (U i j) (V i j) _ T t ht (hU i j) (hV i j)
    have hnoise (i : Fin N) : (vectorIto D (V i) : Ω → ℝ)=ᵐ[P] Mi i t := by
      rw [hclass i]
      exact (vectorProcessLp_ae_eq D (U i) t).trans ((hmod i).fixedTime_ae_eq t)
    filter_upwards [he,ae_all_iff.mpr hnoise] with ω heω hm
    dsimp only [C,M]
    rw [hprefixIntegral t ht ω]
    have hs := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hm i)
    rw [hs] at heω
    linarith
  have hcommon : ∀ᵐ ω ∂P,∀ t,t≤T → C t ω=M t ω := by
    have hcmin : ∀ᵐ ω ∂P,Continuous (fun t => C (min t T) ω) :=
      hCc.mono (fun ω hc => hc.comp (continuous_id.min continuous_const))
    have hmmin : ∀ᵐ ω ∂P,Continuous (fun t => M (min t T) ω) :=
      hMc.mono (fun ω hc => hc.comp (continuous_id.min continuous_const))
    have hall := continuous_processes_ae_eq_of_fixedTime hcmin hmmin
      (fun t => hfixed (min t T) (min_le_right _ _))
    filter_upwards [hall] with ω hω
    intro t ht
    simpa only [min_eq_left ht] using hω t
  refine ⟨M,hM,hMc,?_⟩
  filter_upwards [hcommon] with ω hω
  intro t ht
  rw [← hω t ht]
  dsimp only [C]
  rw [hprefixIntegral t ht ω]
  congr 1
  exact primitive_eq_real_intervalIntegral (fun q : ℝ≥0 × Ω => G q.1 q.2) t ω

/-- The constructed literal fixed-disorder sphere flow realizes the full
C² generator martingale problem in its true complete driving filtration. -/
theorem exists_transition_C2_generator_martingale (hN : N ≠ 0) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (T : ℝ≥0) :
    ∃ M : ℝ≥0 → VectorBrownian.Space N → ℝ,
      Martingale M (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N))
        (VectorBrownian.law N) ∧
      (∀ᵐ ω ∂VectorBrownian.law N,Continuous (fun t => M t ω)) ∧
      ∀ᵐ ω ∂VectorBrownian.law N,∀ t,t≤T → M t ω=
        f (ActualSphereTransition.jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
          β R hR (J,x) t ω)-f x-
          ∫ s in (0 : ℝ)..(t : ℝ),SphereGenerator.coefficientGenerator β J f
            (ActualSphereTransition.jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
              β R hR (J,x) s.toNNReal ω) := by
  exact exists_physical_C2_generator_martingale
    (NullAugmentation.driver (VectorBrownian.driver N)) β J
    (fun T => ActualSphereMarkovRestart.jointProcess_physical hN (VectorBrownian.driver N) β R hR hNR J x hx T)
    (ActualSphereTransition.jointProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR J x hx)
    R hR hNR hf T

end SphericalAging.ActualC2Martingale
