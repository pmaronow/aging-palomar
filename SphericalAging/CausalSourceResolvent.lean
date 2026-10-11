module

public import SphericalAging.CausalVolterraDecomposition
public import SphericalAging.AffineVariationalSolution

public section

/-! The genuine constructed affine response class is the Bochner integral
of its actual causal source resolvents. This is derived from the proved
source decomposition and the real continuous linear Picard solution map. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.CausalSourceResolvent
open HardSphereDynamics LocalSDE PredictableDriftTime VolterraLinearity
open PredictableLinearCoefficient LinearResolvent StochasticLinearizationError
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Field
variable (f : Fin N → ℝ≥0 → Ω → ℝ) (hf : ∀ i,StronglyAdapted F (f i))
  (M : ℝ) (hM : 0≤M) (hb : ∀ i,∀ᵐ omega ∂P,∀ t,‖f i t omega‖≤M)
  (hc : ∀ i,∀ᵐ omega ∂P,Continuous (fun t => f i t omega)) (T : ℝ≥0)

/-- Literal coordinate assembly of the actual causal forcing impulse. -/
@[expose] def impulseSource (s : ℝ≥0) : PredictableStateL2 N F P :=
  ∑ i,stateInclusion i (CausalImpulseSource.impulse (f i) (hf i) M (hb i) T s)

include hM hc in
lemma impulseSource_continuous : Continuous (impulseSource f hf M hb T) :=
  continuous_finsetSum Finset.univ (fun i _ => (stateInclusion i).continuous.comp
    (CausalImpulseSource.impulse_continuous (f i) (hf i) M hM (hb i) (hc i) T))

include hM hc in
lemma impulseSource_integrable : Integrable (impulseSource f hf M hb T) (finiteTimeMeasure T) :=
  (impulseSource_continuous f hf M hM hb hc T).continuousOn.integrableOn_compact isCompact_Icc
    |>.mono_set Ioc_subset_Icc_self

/-- Exact vector-valued source identity for the actual bounded adapted
continuous forcing field. -/
theorem driftSource_eq_integral_impulse :
    driftSource T (fun i => CausalImpulseSource.fieldClass (f i) (hf i) M hM (hb i) (hc i) T)=
      ∫ s,impulseSource f hf M hb T s ∂finiteTimeMeasure T := by
  letI : Fact (F.predictable≤(inferInstance : MeasurableSpace (ℝ≥0 × Ω))) := ⟨predictable_le_prod F⟩
  have hi (i : Fin N) : Integrable (CausalImpulseSource.impulse (f i) (hf i) M (hb i) T)
      (finiteTimeMeasure T) :=
    (CausalImpulseSource.impulse_integrable (f i) (hf i) M hM (hb i) (hc i) T).mono_set Ioc_subset_Icc_self
  unfold driftSource impulseSource
  simp only [driftOperator_apply,CausalVolterraDecomposition.bounded_field_volterra]
  rw [integral_finset_sum _ (fun i _ => (stateInclusion i).integrable_comp (hi i))]
  exact Finset.sum_congr rfl (fun i _ => ((stateInclusion i).integral_comp_comm (hi i)).symm)

/-- True Bochner response-source decomposition of the constructed linear
SDE, with actual causal forcing impulses and genuine integrability. -/
theorem sourceClass_eq_integral_impulse_resolvent {Kb Ks : ℝ≥0}
    (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) :
    LinearVariationalSDE.sourceClass D a sigma T
      (driftSource T (fun i => CausalImpulseSource.fieldClass (f i) (hf i) M hM (hb i) (hc i) T))=
      ∫ s,LinearVariationalSDE.sourceClass D a sigma T (impulseSource f hf M hb T s) ∂finiteTimeMeasure T := by
  letI : Fact (F.predictable≤(inferInstance : MeasurableSpace (ℝ≥0 × Ω))) := ⟨predictable_le_prod F⟩
  rw [driftSource_eq_integral_impulse f hf M hM hb hc T]
  exact ((sourceLinearMap D a sigma T).integral_comp_comm
    (impulseSource_integrable f hf M hM hb hc T)).symm

end Field

/-- The source decomposition belongs to the same actual continuous affine
strong solution used by the physical forced-response construction. -/
theorem actual_affine_responseClass_eq_integral {Kb Ks B : ℝ≥0}
    (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (hf : ∀ i,StronglyAdapted F (fun s omega => (forcing i).value (s,omega)))
    (hb : ∀ i,∀ᵐ omega ∂P,∀ s,‖(forcing i).value (s,omega)‖≤B)
    (hc : ∀ i,∀ᵐ omega ∂P,Continuous (fun s => (forcing i).value (s,omega))) (T : ℝ≥0) :
    AffineVariationalSolution.responseClass D a sigma forcing T=
      ∫ s,LinearVariationalSDE.sourceClass D a sigma T
        (impulseSource (fun i s omega => (forcing i).value (s,omega)) hf B hb T s) ∂finiteTimeMeasure T := by
  have hclasses (i : Fin N) : AffineVariationalSolution.forcingClass (forcing i) T=
      CausalImpulseSource.fieldClass (fun s omega => (forcing i).value (s,omega)) (hf i) B B.coe_nonneg (hb i) (hc i) T := by
    apply Subtype.ext
    apply Lp.ext
    exact (AffineVariationalSolution.forcingClass_coe (forcing i) T).trans
      (CausalImpulseSource.fieldClass_coe _ (hf i) B B.coe_nonneg (hb i) (hc i) T).symm
  unfold AffineVariationalSolution.responseClass
  simp only [hclasses]
  exact sourceClass_eq_integral_impulse_resolvent _ hf B B.coe_nonneg hb hc T D a sigma

end SphericalAging.CausalSourceResolvent
