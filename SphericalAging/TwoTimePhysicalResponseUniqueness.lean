module

public import SphericalAging.TwoTimePhysicalResponse

public section

/-! Physical two-time responses are unique on the actual waiting-time
trajectory. The proof converts the uncut physical Jacobian equation back
to the constructed bounded predictable cutoff equation, then uses genuine
strong pathwise uniqueness with random initial data. In particular the
response is independent of the auxiliary cutoff. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.TwoTimePhysicalResponseUniqueness
open HardSphereDynamics LocalSDE PredictableLinearCoefficient VariationalCoefficients
open PredictableDriftTime PhysicalVariationalBounds TwoTimePhysicalResponse
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Every genuine physical response on a sphere base path satisfies the
bounded predictable cutoff equation. Neither its state class nor moments
are assumptions. -/
theorem cutoff_of_physical (D : BrownianDriver N P F)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) {Kb Ks : ℝ≥0}
    (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (s T : ℝ≥0) (v : State N)
    (hSphere : ∀ᵐ omega ∂P,∀ t,t ≤ s+T → OnSphere (X t omega))
    {Y : ℝ≥0 → Ω → State N} (hY : IsStrongResponseOn β J X D s v Y T) :
    RandomLinearVariationalSDE.IsStrongSolutionOn
      (driftRows X hXa hXc β J R hR hb s T) (noiseRows X hXa hXc R hR hs s T)
      (ShiftedBrownian.driver D s) (fun omega => projection (X s omega) v) Y T := by
  obtain ⟨hYa,hYc,A,U,hA,hU,hEq⟩ := hY
  have hXe := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hSphere
  have hdrift : ∀ i,(A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => (driftRows X hXa hXc β J R hR hb s T i).value (t,omega) (Y t omega)) T := by
    intro i
    filter_upwards [hA i,hXe] with q hA hX
    rw [hA]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hxR : ‖X (s+q.1) q.2‖ < R := by
        have hn := (onSphere_iff_norm_sq _).mp (hX (s+q.1) (add_le_add le_rfl ht.2))
        nlinarith [norm_nonneg (X (s+q.1) q.2)]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,driftRows,derivativeRow,shiftedState]
      exact (fderiv_cutoffDrift_apply β J R hR _ _ hxR i).symm
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false]
  have hnoise : ∀ i j,(U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => (noiseRows X hXa hXc R hR hs s T i j).value (t,omega) (Y t omega)) T := by
    intro i j
    filter_upwards [hU i j,hXe] with q hU hX
    rw [hU]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hxR : ‖X (s+q.1) q.2‖ < R := by
        have hn := (onSphere_iff_norm_sq _).mp (hX (s+q.1) (add_le_add le_rfl ht.2))
        nlinarith [norm_nonneg (X (s+q.1) q.2)]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,noiseRows,derivativeRow,shiftedState]
      exact (fderiv_cutoffNoise_apply R hR _ _ hxR i j).symm
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false]
  refine ⟨hYa,hYc,A,U,hdrift,hnoise,?_⟩
  intro t ht i
  have hd0 := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun r omega => (fderiv ℝ (hamiltonianDrift β J) (X (s+r) omega) (Y r omega)) i) T (A i) (hA i)
  have hd1 := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun r omega => (driftRows X hXa hXc β J R hR hb s T i).value (r,omega) (Y r omega)) T (A i) (hdrift i)
  filter_upwards [hEq t ht i,hd0,hd1] with omega hEq hd0 hd1
  rw [← hd0 t ht,hd1 t ht] at hEq
  exact hEq

/-- Actual two-time physical pathwise uniqueness. The null-set condition
is inherited automatically from the completed physical filtration. -/
theorem response_pathwise_uniqueness (D : BrownianDriver N P F)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) {Kb Ks : ℝ≥0}
    (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (s T : ℝ≥0) (v : State N)
    (hSphere : ∀ᵐ omega ∂P,∀ t,t ≤ s+T → OnSphere (X t omega))
    {Y Z : ℝ≥0 → Ω → State N}
    (hY : IsStrongResponseOn β J X D s v Y T)
    (hZ : IsStrongResponseOn β J X D s v Z T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    ∀ᵐ omega ∂P,∀ t,t ≤ T → Y t omega=Z t omega := by
  apply RandomLinearVariationalSDE.pathwise_uniqueness
    (cutoff_of_physical D X hXa hXc β J R hR hNR hb hs s T v hSphere hY)
    (cutoff_of_physical D X hXa hXc β J R hR hNR hb hs s T v hSphere hZ)
  intro A hA hzero
  rw [ShiftedBrownian.filtration_zero]
  exact (F.mono bot_le) A (hnull A hA hzero)

end SphericalAging.TwoTimePhysicalResponseUniqueness
