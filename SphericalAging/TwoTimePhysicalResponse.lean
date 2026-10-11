module

public import SphericalAging.RandomLinearVariationalSDE
public import SphericalAging.ShiftedBrownian
public import SphericalAging.PhysicalVariationalEquation

public section

/-! Actual two-time physical matrix response. At waiting time s, the
initial vector is the genuine tangent projection P_{X_s}v, known in F_s.
A true shifted Brownian driver and constructed random-initial Picard
solution give the physical Jacobian SDE along the same base trajectory.
Identification with an arbitrary time-dependent forcing derivative and
Duhamel reconstruction are separate obligations. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.TwoTimePhysicalResponse
open HardSphereDynamics LocalSDE PredictableLinearCoefficient VariationalCoefficients
open PredictableDriftTime PhysicalVariationalBounds
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def shiftedState (X : ℝ≥0 → Ω → State N) (s : ℝ≥0) (t : ℝ≥0) : Ω → State N := X (s+t)

lemma shiftedState_stronglyAdapted {X : ℝ≥0 → Ω → State N} (hX : StronglyAdapted F X) (s : ℝ≥0) :
    StronglyAdapted (ShiftedBrownian.filtration F s) (shiftedState X s) := fun t => hX (s+t)

omit [IsProbabilityMeasure P] in
lemma shiftedState_continuous {X : ℝ≥0 → Ω → State N}
    (hX : ∀ᵐ omega ∂P,Continuous (fun t => X t omega)) (s : ℝ≥0) :
    ∀ᵐ omega ∂P,Continuous (fun t => shiftedState X s t omega) :=
  hX.mono (fun _ h => h.comp (continuous_const.add continuous_id))

lemma projection_continuous (v : State N) : Continuous (fun x : State N => projection x v) :=
  continuous_const.sub (((continuous_id.inner continuous_const).div_const (N : ℝ)).smul continuous_id)

lemma projectedInitial_stronglyMeasurable {X : ℝ≥0 → Ω → State N}
    (hX : StronglyAdapted F X) (s : ℝ≥0) (v : State N) :
    StronglyMeasurable[ShiftedBrownian.filtration F s 0] (fun omega => projection (X s omega) v) := by
  rw [ShiftedBrownian.filtration_zero]
  exact (projection_continuous v).comp_stronglyMeasurable (hX s)

lemma projectedInitial_memLp (hN : N ≠ 0) {X : ℝ≥0 → Ω → State N}
    (hX : StronglyAdapted F X) (s : ℝ≥0) (v : State N)
    (hsphere : ∀ᵐ omega ∂P,OnSphere (X s omega)) :
    MemLp (fun omega => projection (X s omega) v) 2 P := by
  apply (memLp_const (‖v‖ : ℝ) : MemLp (fun _ : Ω => ‖v‖) 2 P).mono'
    (((projectedInitial_stronglyMeasurable hX s v).mono
      ((ShiftedBrownian.filtration F s).le 0)).aestronglyMeasurable)
  filter_upwards [hsphere] with omega h
  simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg v)] using
    projection_norm_le_onSphere hN (X s omega) v h

@[expose] def driftRows (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R)
    {Kb : ℝ≥0} (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (s T : ℝ≥0) (i : Fin N) : Coefficient (N := N) (F := ShiftedBrownian.filtration F s) (P := P) Kb :=
  derivativeRow (shiftedState X s) (shiftedState_stronglyAdapted hXa s) (shiftedState_continuous hXc s)
    (cutoffDrift_contDiff β J R hR i) (hb i) T

@[expose] def noiseRows (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (R : ℝ) (hR : 0 < R) {Ks : ℝ≥0}
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (s T : ℝ≥0) (i j : Fin N) : Coefficient (N := N) (F := ShiftedBrownian.filtration F s) (P := P) Ks :=
  derivativeRow (shiftedState X s) (shiftedState_stronglyAdapted hXa s) (shiftedState_continuous hXc s)
    (cutoffNoise_contDiff R hR i j) (hs i j) T

/-- Literal physical variational equation at waiting time s. The initial
projection, time-shifted state, physical derivative and genuine shifted
full-filtration Itô operator are all present in the equation. -/
@[expose] def IsStrongResponseOn (β : ℝ) (J : FiniteModel.Disorder N p) (X : ℝ≥0 → Ω → State N)
    (D : BrownianDriver N P F) (s : ℝ≥0) (v : State N) (Y : ℝ≥0 → Ω → State N) (T : ℝ≥0) : Prop :=
  StronglyAdapted (ShiftedBrownian.filtration F s) Y ∧
  (∀ᵐ omega ∂P,Continuous (fun t => Y t omega)) ∧
  ∃ A : Fin N → PredictableProcessL2 (ShiftedBrownian.filtration F s) P,
  ∃ U : Fin N → Fin N → PredictableProcessL2 (ShiftedBrownian.filtration F s) P,
    (∀ i,(A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => (fderiv ℝ (hamiltonianDrift β J) (X (s+t) omega) (Y t omega)) i) T) ∧
    (∀ i j,(U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => (fderiv ℝ (fun z : State N => noiseColumn z j) (X (s+t) omega) (Y t omega)) i) T) ∧
    (∀ t,t ≤ T → ∀ i,∀ᵐ omega ∂P,Y t omega i=(projection (X s omega) v) i+
      (∫ r in (0 : ℝ)..(t : ℝ),
        (fderiv ℝ (hamiltonianDrift β J) (X (s+r.toNNReal) omega) (Y r.toNNReal omega)) i)+
      driverItoMap (ShiftedBrownian.driver D s)
        (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict
          (ShiftedBrownian.filtration F s) t (U i j)) omega)

 theorem physical_of_cutoff (_hN : N ≠ 0) (D : BrownianDriver N P F)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) {Kb Ks : ℝ≥0}
    (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (s T : ℝ≥0) (v : State N)
    (hSphere : ∀ᵐ omega ∂P,∀ t,t ≤ s+T → OnSphere (X t omega))
    {Y : ℝ≥0 → Ω → State N}
    (hY : RandomLinearVariationalSDE.IsStrongSolutionOn
      (driftRows X hXa hXc β J R hR hb s T) (noiseRows X hXa hXc R hR hs s T)
      (ShiftedBrownian.driver D s) (fun omega => projection (X s omega) v) Y T) :
    IsStrongResponseOn β J X D s v Y T := by
  obtain ⟨hYa,hYc,A,U,hA,hU,hEq⟩ := hY
  have hXe := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hSphere
  have hdrift : ∀ i,(A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => (fderiv ℝ (hamiltonianDrift β J) (X (s+t) omega) (Y t omega)) i) T := by
    intro i
    filter_upwards [hA i,hXe] with q hA hX
    rw [hA]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hxR : ‖X (s+q.1) q.2‖ < R := by
        have hn := (onSphere_iff_norm_sq _).mp (hX (s+q.1) (add_le_add le_rfl ht.2))
        nlinarith [norm_nonneg (X (s+q.1) q.2)]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,driftRows,derivativeRow,shiftedState]
      exact fderiv_cutoffDrift_apply β J R hR _ _ hxR i
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false]
  have hnoise : ∀ i j,(U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => (fderiv ℝ (fun z : State N => noiseColumn z j) (X (s+t) omega) (Y t omega)) i) T := by
    intro i j
    filter_upwards [hU i j,hXe] with q hU hX
    rw [hU]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hxR : ‖X (s+q.1) q.2‖ < R := by
        have hn := (onSphere_iff_norm_sq _).mp (hX (s+q.1) (add_le_add le_rfl ht.2))
        nlinarith [norm_nonneg (X (s+q.1) q.2)]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,noiseRows,derivativeRow,shiftedState]
      exact fderiv_cutoffNoise_apply R hR _ _ hxR i j
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false]
  refine ⟨hYa,hYc,A,U,hdrift,hnoise,?_⟩
  intro t ht i
  have hd0 := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun r omega => (driftRows X hXa hXc β J R hR hb s T i).value (r,omega) (Y r omega)) T (A i) (hA i)
  have hd1 := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun r omega => (fderiv ℝ (hamiltonianDrift β J) (X (s+r) omega) (Y r omega)) i) T (A i) (hdrift i)
  filter_upwards [hEq t ht i,hd0,hd1] with omega hEq hd0 hd1
  rw [← hd0 t ht,hd1 t ht] at hEq
  exact hEq

/-- Actual response existence with projected random initial vector;
all sphere and driver regularity are genuine inputs to the base path. -/
 theorem exists_response_onSphere (hN : N ≠ 0) (D : BrownianDriver N P F)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) {Kb Ks : ℝ≥0}
    (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (s T : ℝ≥0) (v : State N)
    (hSphere : ∀ᵐ omega ∂P,∀ t,t ≤ s+T → OnSphere (X t omega)) :
    ∃ Y,IsStrongResponseOn β J X D s v Y T ∧ ∀ t,MemLp (Y t) 2 P := by
  let h0 := projectedInitial_stronglyMeasurable hXa s v
  let hmem := projectedInitial_memLp hN hXa s v (hSphere.mono (fun _ h => h s (le_add_right le_rfl)))
  let Y := RandomLinearVariationalSDE.process (ShiftedBrownian.driver D s)
    (driftRows X hXa hXc β J R hR hb s T) (noiseRows X hXa hXc R hR hs s T)
    (fun omega => projection (X s omega) v) h0 hmem T
  refine ⟨Y,physical_of_cutoff hN D X hXa hXc β J R hR hNR hb hs s T v hSphere
    (RandomLinearVariationalSDE.process_strongSolution _ _ _ _ h0 hmem T),?_⟩
  intro t
  exact RandomLinearVariationalSDE.process_memLp _ _ _ _ h0 hmem T t

 theorem exists_on_actual_base (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) {Kb Ks : ℝ≥0}
    (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (x : State N) (hx : OnSphere x) (s T : ℝ≥0) (v : State N) :
    ∃ Y,IsStrongResponseOn β J (GlobalSDE.horizonProcess (NullAugmentation.driver D₀) hb hs x (s+T))
      (NullAugmentation.driver D₀) s v Y T ∧ ∀ t,MemLp (Y t) 2 P := by
  exact exists_response_onSphere hN (NullAugmentation.driver D₀) _
    (GlobalSDE.horizonProcess_strongSolution _ hb hs x (s+T)).1
    (GlobalSDE.horizonProcess_strongSolution _ hb hs x (s+T)).2.1
    β J R hR hNR hb hs s T v (PhysicalVariationalEquation.base_onSphere hN D₀ β J R hR hNR hb hs x hx (s+T))


 theorem IsStrongResponseOn.initial
    {β : ℝ} {J : FiniteModel.Disorder N p} {X : ℝ≥0 → Ω → State N}
    {D : BrownianDriver N P F} {s T : ℝ≥0} {v : State N} {Y : ℝ≥0 → Ω → State N}
    (hY : IsStrongResponseOn β J X D s v Y T) :
    ∀ᵐ omega ∂P,Y 0 omega=projection (X s omega) v := by
  obtain ⟨_,_,A,U,_,_,heq⟩ := hY
  have hn (i : Fin N) : driverItoMap (ShiftedBrownian.driver D s)
      (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict
        (ShiftedBrownian.filtration F s) 0 (U i j))=0 := by
    rw [CutoffSphere.driverItoMap_eq_vectorIto]
    change VectorIto.vectorProcessLp (ShiftedBrownian.driver D s) (U i) 0 = 0
    exact LinearSDELocalization.vectorProcessLp_zero_time _ _
  have hcoord := ae_all_iff.mpr (fun i : Fin N => heq 0 bot_le i)
  filter_upwards [hcoord,Lp.coeFn_zero ℝ 2 P] with omega h hzero
  apply PiLp.ext
  intro i
  have hi := h i
  rw [hn i,hzero] at hi
  simpa only [NNReal.coe_zero,intervalIntegral.integral_same,Pi.zero_apply,add_zero] using hi

end SphericalAging.TwoTimePhysicalResponse
