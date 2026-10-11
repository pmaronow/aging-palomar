module

public import SphericalAging.RandomLinearVariationalSDE
public import SphericalAging.StaticSDEOperators

public section

/-! True linear operations on actual random-initial strong linear SDE
solutions. Bounded initial-filtration multipliers commute with the genuine
Itô operator, rather than being treated as deterministic directions. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.RandomLinearStrongOperations
open HardSphereDynamics LocalSDE PredictableLinearCoefficient PredictableDriftTime
open BoundedItoMultiplier VectorIto
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks : ℝ≥0}

/-- Actual random-initial strong semantics is unchanged by an AE-equal
initial representative. -/
theorem initial_congr
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {Z0 W0 : Ω → State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hX : RandomLinearVariationalSDE.IsStrongSolutionOn a sigma D Z0 X T) (hZW : Z0=ᵐ[P] W0) :
    RandomLinearVariationalSDE.IsStrongSolutionOn a sigma D W0 X T := by
  obtain ⟨hXa,hXc,A,U,hA,hU,hEq⟩ := hX
  refine ⟨hXa,hXc,A,U,hA,hU,?_⟩
  intro t ht i
  filter_upwards [hEq t ht i,hZW] with omega hEq hZW
  simpa only [hZW] using hEq

/-- Genuine multiplication of the same-driver strong linear solution by
a bounded random scalar known in the full initial filtration. -/
theorem bounded_initial_scalar_mul
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hX : RandomLinearVariationalSDE.IsStrongSolutionOn a sigma D Z0 X T)
    (C : Ω → ℝ) (hC : StronglyMeasurable[F 0] C) (K : ℝ≥0) (hK : ∀ omega,‖C omega‖≤K) :
    RandomLinearVariationalSDE.IsStrongSolutionOn a sigma D (fun omega => C omega • Z0 omega)
      (fun t omega => C omega • X t omega) T := by
  obtain ⟨hXa,hXc,A,U,hA,hU,hEq⟩ := hX
  let A' := fun i => predictableMulCLM T hC K hK (A i)
  let U' := fun i j => predictableMulCLM T hC K hK (U i j)
  have hA' : ∀ i,(A' i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun t omega => (a i).value (t,omega) (C omega • X t omega)) T := by
    intro i
    filter_upwards [predictableMulCLM_coe T hC K hK (A i),hA i] with q hc ha
    rw [hc,ha]
    by_cases ht : q.1∈Ioc (0 : ℝ≥0) T <;>
      simp [FourPapersCommon.continuousAdaptedTimeCut,elementaryRepresentative,ht,map_smul,smul_eq_mul]
  have hU' : ∀ i j,(U' i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun t omega => (sigma i j).value (t,omega) (C omega • X t omega)) T := by
    intro i j
    filter_upwards [predictableMulCLM_coe T hC K hK (U i j),hU i j] with q hc hu
    rw [hc,hu]
    by_cases ht : q.1∈Ioc (0 : ℝ≥0) T <;>
      simp [FourPapersCommon.continuousAdaptedTimeCut,elementaryRepresentative,ht,map_smul,smul_eq_mul]
  refine ⟨(fun t => (hC.mono (F.mono bot_le)).smul (hXa t)),?_,A',U',hA',hU',?_⟩
  · exact hXc.mono (fun omega h => (h.const_smul (C omega)))
  · intro t ht i
    have hn := StaticSDEOperators.vectorProcessLp_mul_coe D T t ht hC K hK (U i)
    have heold := hEq t ht i
    have hOld : driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (U i j))=
        vectorProcessLp D (U i) t := CutoffSphere.driverItoMap_eq_vectorIto D _
    have hNew : driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (U' i j))=
        vectorProcessLp D (U' i) t := CutoffSphere.driverItoMap_eq_vectorIto D _
    rw [hOld] at heold
    rw [hNew]
    change ∀ᵐ omega ∂P,(C omega • X t omega) i=(C omega • Z0 omega) i+
      (∫ r in (0 : ℝ)..(t : ℝ),(a i).value (r.toNNReal,omega) (C omega • X r.toNNReal omega))+
      (vectorProcessLp D (U' i) t : Ω → ℝ) omega
    filter_upwards [heold,hn] with omega he hn
    simp only [PiLp.smul_apply,smul_eq_mul]
    simp_rw [map_smul,smul_eq_mul,intervalIntegral.integral_const_mul]
    rw [hn,he]
    ring

end SphericalAging.RandomLinearStrongOperations
