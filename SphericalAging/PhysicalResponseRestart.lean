module

public import SphericalAging.RandomLinearSolutionRestart
public import SphericalAging.RandomLinearCoefficientCongruence
public import SphericalAging.ShiftedBrownianAssociativity
public import SphericalAging.TwoTimeResponseMoments

public section

/-! Restart of the genuine physical response along the same actual
trajectory. Both the nested filtration and centered driver are identified
with the original driver shifted to the later waiting time. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.PhysicalResponseRestart
open HardSphereDynamics LocalSDE PredictableLinearCoefficient RandomLinearVariationalSDE
  TwoTimePhysicalResponse CausalImpulseRestart TimeShiftMeasure
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Kb Ks : ℝ≥0}

lemma strongSolution_filtration_congr {G : Filtration ℝ≥0 mΩ} (hF : F=G)
    (a : Fin N→Coefficient (N:=N) (F:=F) (P:=P) Kb)
    (sigma : Fin N→Fin N→Coefficient (N:=N) (F:=F) (P:=P) Ks)
    (a' : Fin N→Coefficient (N:=N) (F:=G) (P:=P) Kb)
    (sigma' : Fin N→Fin N→Coefficient (N:=N) (F:=G) (P:=P) Ks)
    (ha : ∀ i,(a i).value=ᵐ[nonnegativeLebesgueMeasure.prod P] (a' i).value)
    (hs : ∀ i j,(sigma i j).value=ᵐ[nonnegativeLebesgueMeasure.prod P] (sigma' i j).value)
    (D : BrownianDriver N P F) (D' : BrownianDriver N P G) (hD : HEq D D')
    (Z0 : Ω→State N) (Y : ℝ≥0→Ω→State N) (T : ℝ≥0)
    (h : IsStrongSolutionOn a sigma D Z0 Y T) :
    IsStrongSolutionOn a' sigma' D' Z0 Y T := by
  subst G
  have hd : D=D' := eq_of_heq hD
  rw [←hd]
  exact RandomLinearCoefficientCongruence.strongSolution_congr_coefficients
    a sigma a' sigma' ha hs D Z0 Y T h

section Physical
variable (D : BrownianDriver N P F) (X : ℝ≥0→Ω→State N)
  (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P,Continuous (fun t => X t ω))
  (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R:ℝ))
  (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
  (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j)) (s δ T : ℝ≥0)

lemma driftRows_shift_add (i : Fin N) :
    (coefficientShift (driftRows X hXa hXc β J R hR hb s (δ+T) i) δ).value=ᵐ[nonnegativeLebesgueMeasure.prod P]
      (driftRows X hXa hXc β J R hR hb (s+δ) T i).value := by
  have hpos : ∀ᵐ q : ℝ≥0×Ω ∂nonnegativeLebesgueMeasure.prod P,0<q.1 :=
    (Measure.quasiMeasurePreserving_fst (μ:=nonnegativeLebesgueMeasure) (ν:=P)).ae
      (ae_iff.mpr (by simp))
  filter_upwards [hpos] with q hq
  have he : δ+q.1∈Ioc (0:ℝ≥0) (δ+T) ↔ q.1∈Ioc (0:ℝ≥0) T :=
    and_congr (iff_of_true ((zero_le : 0≤δ).trans_lt (lt_add_of_pos_right δ hq)) hq)
      (add_le_add_iff_left δ)
  simp only [coefficientShift,driftRows,VariationalCoefficients.derivativeRow,shift,shiftedState,he,add_assoc]

lemma noiseRows_shift_add (i j : Fin N) :
    (coefficientShift (noiseRows X hXa hXc R hR hs s (δ+T) i j) δ).value=ᵐ[nonnegativeLebesgueMeasure.prod P]
      (noiseRows X hXa hXc R hR hs (s+δ) T i j).value := by
  have hpos : ∀ᵐ q : ℝ≥0×Ω ∂nonnegativeLebesgueMeasure.prod P,0<q.1 :=
    (Measure.quasiMeasurePreserving_fst (μ:=nonnegativeLebesgueMeasure) (ν:=P)).ae
      (ae_iff.mpr (by simp))
  filter_upwards [hpos] with q hq
  have he : δ+q.1∈Ioc (0:ℝ≥0) (δ+T) ↔ q.1∈Ioc (0:ℝ≥0) T :=
    and_congr (iff_of_true ((zero_le : 0≤δ).trans_lt (lt_add_of_pos_right δ hq)) hq)
      (add_le_add_iff_left δ)
  simp only [coefficientShift,noiseRows,VariationalCoefficients.derivativeRow,shift,shiftedState,he,add_assoc]

/-- The observed response state is the exact random initial state for the
later response SDE on the same trajectory and actual future Brownian noise. -/
theorem strongSolution_restart {Z0 : Ω→State N} {Y : ℝ≥0→Ω→State N}
    (h : IsStrongSolutionOn (driftRows X hXa hXc β J R hR hb s (δ+T))
      (noiseRows X hXa hXc R hR hs s (δ+T)) (ShiftedBrownian.driver D s) Z0 Y (δ+T)) :
    IsStrongSolutionOn (driftRows X hXa hXc β J R hR hb (s+δ) T)
      (noiseRows X hXa hXc R hR hs (s+δ) T) (ShiftedBrownian.driver D (s+δ))
      (Y δ) (fun t ω => Y (δ+t) ω) T := by
  have hr := RandomLinearSolutionRestart.strongSolution_timeShift δ T h
  exact strongSolution_filtration_congr (ShiftedBrownianAssociativity.filtration_add s δ)
    _ _ _ _ (driftRows_shift_add X hXa hXc β J R hR hb s δ T)
    (noiseRows_shift_add X hXa hXc R hR hs s δ T) _ _
    (ShiftedBrownianAssociativity.driver_add D s δ) _ _ T hr

end Physical
end SphericalAging.PhysicalResponseRestart
