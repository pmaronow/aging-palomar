module

public import SphericalAging.SphereOnlyPhysicalForkOverlapLaw
public import SphericalAging.SphereOnlyPhysicalForkCenterConcentration
public import SphericalAging.SphereOnlyPhysicalForkNormalizationLimits
public import SphericalAging.SphereOnlyPhysicalForkNormTheorem
public import SphericalAging.SphereOnlyPhysicalForkOverlapAggregation
public import SphericalAging.SphereOnlyPhysicalForkLateOverlapLimit
public import SphericalAging.ActualForkLateEnergyReplacement
public import SphericalAging.ActualForkLateEnergyLimit
public import SphericalAging.ActualSphereOnlyForkUniformL2

public section

/-! Source10.4 Step4 for the literal actual driver response fields:
dimension first, then stationary time, with no energy or weighted
response convergence premise. -/

noncomputable section
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereOnlyActualForkLateEnergyLimit
open PhysicalForkOverlapLaw PhysicalForkCenterConcentration PhysicalForkNormalizationLimits PhysicalForkNormTheorem PhysicalForkOverlapAggregation PhysicalForkLateOverlapLimit ActualForkLateEnergyLimit
open ActualForkLateEnergyLimit
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel HardSphereDynamics
open PhysicalForkDrivers ActualForkTraceFormula ActualForkLateEnergyReplacement
open SphereOnlyPhysicalForkLateOverlapLimit SphereOnlyPhysicalForkOverlapAggregation SphereOnlyPhysicalForkCenterConcentration
open AnnealedHamiltonianEnergyStein EnergyCovarianceContraction CKSpecification StationaryClusterInputs
open ActualForkMeanBridge SphereFisherHelly ActualSphereForkEndpoints
open TwoTimeResponseTimeParameter
open AnnealedResponseMatrixContraction
open scoped NNReal ENNReal Topology

theorem actual_late_energy_ordered_uniform {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|ActualSphereRestrictedFisherBudget.full (N:=dim j) (p:=p) β (dim j+1) (modelRadius_pos (dim j)) w-f w|) atTop (𝓝 0))
    (hK : 0<K) (L : ℝ≥0)
    (U : ∀n j : ℕ,Fin K→WaitingTime ((T n).toNNReal+L)×
      ((Disorder (dim j) p×State (dim j))×PathSeed (dim j) K)→State (dim j)→L[ℝ]State (dim j))
    (hU : ∀n j b,StronglyMeasurable (U n j b))
    (hUs : ∀n j b,RepresentsPhysicalMatrix (by have hd:=hDim j;omega : 0<dim j)
      β ((T n).toNNReal+L) (T n).toNNReal b (U n j b))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠn in atTop,∀ᶠj in atTop,∀b : Fin K,
      (∫a,|lateReplacementField β (T n).toNNReal L b c (U n j b) a|
        ∂integratedLaw (dim j) p K ((T n).toNNReal+L))<ε := by
  have hp : 2≤p := by have hh:=h.spin_ge_three;omega
  let D := (L:ℝ)*2*((p-1:ℕ):ℝ)*Real.sqrt (1+annealedFourthConstant p β L)
  have hD : 0≤D := by dsimp [D];positivity
  have hDp : 0<D+1 := by linarith
  let δ := (ε/(D+1))^2
  have hδ : 0<δ := sq_pos_of_pos (div_pos hε hDp)
  have hu := SphereOnlyPhysicalForkOverlapAggregation.actual_late_overlap_ordered_uniform H hT dim hDim hTop hbridge hi hn hL1 hK L hδ
  filter_upwards [hu] with n hnu
  filter_upwards [hnu] with j hju
  intro b
  have hb : ∀v : ℝ≥0,∀hv : v≤L,
      lateOverlapError (N:=dim j) (p:=p) β (T n).toNNReal L c b v≤δ := by
    intro v hv
    exact (hju v ⟨v.coe_nonneg,hv⟩ b).le
  have he := (actual_late_integrated_replacement_bound (by have hd:=hDim j;omega : 0<dim j)
    hp hK β (T n).toNNReal L H.profile b (U n j b) (hU n j b) (hUs n j b) hb).2
  have hs : Real.sqrt δ=ε/(D+1) := Real.sqrt_sq (le_of_lt (div_pos hε hDp))
  have hsmall : D*(ε/(D+1))<ε := by
    have hx : 0<ε/(D+1) := div_pos hε hDp
    have heq : (D+1)*(ε/(D+1))=ε := by field_simp
    nlinarith only [heq,hx]
  apply he.trans_lt
  rw [hs]
  convert hsmall using 1 <;> dsimp [D] <;> ring

theorem actual_late_energy_replacement_tendsto {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|ActualSphereRestrictedFisherBudget.full (N:=dim j) (p:=p) β (dim j+1) (modelRadius_pos (dim j)) w-f w|) atTop (𝓝 0))
    (hK : 0<K) (L : ℝ≥0)
    (U : ∀n j : ℕ,Fin K→WaitingTime ((T n).toNNReal+L)×
      ((Disorder (dim j) p×State (dim j))×PathSeed (dim j) K)→State (dim j)→L[ℝ]State (dim j))
    (hU : ∀n j b,StronglyMeasurable (U n j b))
    (hUs : ∀n j b,RepresentsPhysicalMatrix (by have hd:=hDim j;omega : 0<dim j)
      β ((T n).toNNReal+L) (T n).toNNReal b (U n j b)) (b : Fin K) :
    Tendsto (fun z : ℕ×ℕ => ∫a,|lateReplacementField β (T z.1).toNNReal L b c (U z.1 z.2 b) a|
      ∂integratedLaw (dim z.2) p K ((T z.1).toNNReal+L))
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 0) ∧
    Tendsto (fun n => limsup (fun j => ∫a,|lateReplacementField β (T n).toNNReal L b c (U n j b) a|
      ∂integratedLaw (dim j) p K ((T n).toNNReal+L)) atTop) atTop (𝓝 0) := by
  have ht : Tendsto (fun z : ℕ×ℕ => ∫a,|lateReplacementField β (T z.1).toNNReal L b c (U z.1 z.2 b) a|
      ∂integratedLaw (dim z.2) p K ((T z.1).toNNReal+L))
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun _ => ha.trans_le (integral_nonneg fun _ => abs_nonneg _))
    · intro ε hε
      rw [eventually_curry_iff]
      have he := SphereOnlyActualForkLateEnergyLimit.actual_late_energy_ordered_uniform H hT dim hDim hTop hbridge hi hn hL1 hK L U hU hUs hε
      filter_upwards [he] with n hnε
      filter_upwards [hnε] with j hjε
      exact hjε b
  refine ⟨ht,?_⟩
  apply PhysicalForkCenterConcentration.ordered_limsup_tendsto (M:=(L:ℝ)*2*((p-1:ℕ):ℝ)*Real.sqrt 8*Real.sqrt (1+annealedFourthConstant p β L))
    (fun _ _ => integral_nonneg fun _ => abs_nonneg _) _ ht
  intro n j
  exact (actual_late_integrated_replacement_bound (by have hd:=hDim j;omega : 0<dim j)
    (by have hp:=h.spin_ge_three;omega) hK β (T n).toNNReal L H.profile b (U n j b) (hU n j b) (hUs n j b)
    (fun v hv => (lateOverlapError_bounds (by have hd:=hDim j;omega : 0<dim j) hK β
      (T n).toNNReal L H.profile b ⟨v.coe_nonneg,hv⟩).2)).2

end SphericalAging.SphereOnlyActualForkLateEnergyLimit
