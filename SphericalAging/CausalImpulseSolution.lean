module

public import SphericalAging.CausalSourceResolvent
public import SphericalAging.RandomLinearVariationalSDE
public import SphericalAging.ShiftedItoProcess

public section

/-! Physical interpretation of actual causal source resolvents. The
constructed source solution has a zero continuous prefix; the impulse
initial value is inserted only at its actual waiting time. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.CausalImpulseSolution
open HardSphereDynamics LocalSDE PredictableDriftTime PredictableItoTime
open PredictableLinearCoefficient LinearVariationalSDE VectorIto
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks : ℝ≥0}

/-- Actual deterministic-prefix drift identity, at all prefix times on
one common probability-one event. -/
lemma driftVersion_timeRestrict (A : PredictableProcessL2 F P) (s T : ℝ≥0) (hs : s≤T) :
    ∀ᵐ omega ∂P,∀ t,t≤s → driftVersion A T t omega=
      driftVersion (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s A) s t omega := by
  have he : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      q.1∈Ioc (0 : ℝ≥0) s → cutRepresentative A T q=
        cutRepresentative (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s A) s q := by
    filter_upwards [representative_ae A,representative_ae (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s A),
      FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F s A] with q hA hR hcut
    intro hq
    have ht : q.1∈Ioc (0 : ℝ≥0) T := ⟨hq.1,hq.2.trans hs⟩
    simp only [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,indicator_of_mem (show q∈Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩),
      indicator_of_mem (show q∈Ioc (0 : ℝ≥0) s ×ˢ (univ : Set Ω) from ⟨hq,mem_univ _⟩),hA,hR,hcut]
  have hp := Measure.measurePreserving_swap.quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with omega ho
  intro t ht
  unfold driftVersion primitive
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae ho,ae_restrict_mem measurableSet_Ioc] with r hr hrt
  exact hr ⟨hrt.1,hrt.2.trans ht⟩

section Impulse
variable (D : BrownianDriver N P F)
  (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
  (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
  (s T : ℝ≥0) (Z0 : Ω → State N) (S Q : PredictableStateL2 N F P)
  (hS : (S : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) =ᵐ[nonnegativeLebesgueMeasure.prod P]
    (fun q => if q.1∈Ioc s T then Z0 q.2 else 0))
  (hQ : Q=S+LinearVariationalSDE.finiteDriftPicardMap a T Q+LinearVariationalSDE.finiteNoisePicardMap D sigma T Q)

@[expose] def continuousPart : ℝ≥0 → Ω → State N := LinearVariationalSDE.version D a sigma 0 T Q

@[expose] def jumpVersion (t : ℝ≥0) (omega : Ω) : State N :=
  continuousPart D a sigma T Q t omega + if t∈Ioc s T then Z0 omega else 0

include hS hQ in
lemma impulse_fixedPoint_coe : (Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
    =ᵐ[nonnegativeLebesgueMeasure.prod P]
      ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => jumpVersion D a sigma s T Z0 Q q.1 q.2)) := by
  have hadd := Lp.coeFn_add ((S : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))+
    (LinearVariationalSDE.finiteDriftPicardMap a T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (LinearVariationalSDE.finiteNoisePicardMap D sigma T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
  have hadd' := Lp.coeFn_add (S : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
    (LinearVariationalSDE.finiteDriftPicardMap a T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
  filter_upwards [hS,hadd,hadd',LinearVariationalSDE.finiteDriftPicardMap_coeFn a T Q,LinearVariationalSDE.finiteNoisePicardMap_coeFn D sigma T Q]
    with q hS ha ha' hd hn
  conv_lhs => rw [hQ]
  change (((S : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))+
    (LinearVariationalSDE.finiteDriftPicardMap a T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))+
    (LinearVariationalSDE.finiteNoisePicardMap D sigma T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) q=_
  rw [ha,Pi.add_apply,ha',Pi.add_apply,hS,hd,hn]
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
  · rw [indicator_of_mem (show q∈Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩)]
    simp only [ht,ite_true,jumpVersion,continuousPart,LinearVariationalSDE.version,
      LinearVariationalSDE.coordinateVersion,PiLp.zero_apply,zero_add,add_smul,Finset.sum_add_distrib]
    abel
  · have hst : q.1∉Ioc s T := fun h => ht ⟨(zero_le : 0≤s).trans_lt h.1,h.2⟩
    simp [ht,hst]

include hS hQ in
lemma prefix_coefficient_coe (hs : s≤T) {K : ℝ≥0}
    (c : Coefficient (N := N) (F := F) (P := P) K) :
    (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s (PredictableLinearCoefficient.apply c Q) : TimeProcessL2 P)
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut
          (fun r omega => c.value (r,omega) (continuousPart D a sigma T Q r omega)) s := by
  filter_upwards [FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F s (PredictableLinearCoefficient.apply c Q),
    apply_coeFn c Q,impulse_fixedPoint_coe D a sigma s T Z0 S Q hS hQ] with q hcut ha hQ
  rw [hcut]
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) s
  · have htT : q.1∈Ioc (0 : ℝ≥0) T := ⟨ht.1,ht.2.trans hs⟩
    have hst : q.1∉Ioc s T := fun h => (not_lt_of_ge ht.2) h.1
    rw [FourPapersCommon.FilteredBrownian.predictableTimeFrame,indicator_of_mem (show q∈Ioc (0 : ℝ≥0) s ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩),ha,hQ,indicator_of_mem (show q∈Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨htT,mem_univ _⟩)]
    simp [FourPapersCommon.continuousAdaptedTimeCut,ht,jumpVersion,hst]
  · simp [FourPapersCommon.FilteredBrownian.predictableTimeFrame,FourPapersCommon.continuousAdaptedTimeCut,ht]

include hS hQ in
/-- The continuous part of a genuine impulse resolvent solves a true
zero-initial linear SDE before the impulse time. -/
theorem continuousPart_prefix_strongSolution (hs : s≤T) :
    LinearVariationalSDE.IsStrongSolutionOn a sigma D 0 (continuousPart D a sigma T Q) s := by
  let A := fun i => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s (PredictableLinearCoefficient.apply (a i) Q)
  let U := fun i j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s (PredictableLinearCoefficient.apply (sigma i j) Q)
  have hA := fun i => prefix_coefficient_coe D a sigma s T Z0 S Q hS hQ hs (a i)
  have hU := fun i j => prefix_coefficient_coe D a sigma s T Z0 S Q hS hQ hs (sigma i j)
  refine ⟨LinearVariationalSDE.version_stronglyAdapted D a sigma 0 T Q,LinearVariationalSDE.version_ae_continuous D a sigma 0 T Q,A,U,hA,hU,?_⟩
  intro t ht i
  have he : driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (U i j))=
      driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (PredictableLinearCoefficient.apply (sigma i j) Q)) := by
    congr 1
    funext j
    exact FourPapersCommon.FilteredBrownian.predictableTimeRestrict_restrict F ht _
  have hd := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun r omega => (a i).value (r,omega) (continuousPart D a sigma T Q r omega)) s (A i) (hA i)
  have hr := driftVersion_timeRestrict (PredictableLinearCoefficient.apply (a i) Q) s T hs
  have hn := TerminalStateRepresentation.driverIto_ae_eq_versions D
    (fun j => PredictableLinearCoefficient.apply (sigma i j) Q) t
  filter_upwards [hd,hr,hn] with omega hd hr hn
  rw [continuousPart,LinearVariationalSDE.version_apply]
  simp only [LinearVariationalSDE.coordinateVersion,PiLp.zero_apply,zero_add]
  rw [hr t ht,hd t ht,he,hn]
  rfl

include hS hQ in
/-- Strong uniqueness and the true zero moment force the impulse's
continuous part to vanish on its whole deterministic prefix. -/
theorem continuousPart_zero_prefix (hs : s≤T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    ∀ᵐ omega ∂P,∀ t,t≤s → continuousPart D a sigma T Q t omega=0 :=
  LinearStrongUniqueness.linear_zero_of_strongSolution
    (continuousPart_prefix_strongSolution D a sigma s T Z0 S Q hS hQ hs) hnull

end Impulse
end SphericalAging.CausalImpulseSolution
