module

public import SphericalAging.LinearResponseCoefficientDifference

public section

/-! Exact change-of-coefficient and change-of-source resolvent identity
for the genuinely constructed linear variational solution. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.LinearResponseDifferentSourceDifference
open HardSphereDynamics LocalSDE PredictableLinearCoefficient LinearResolvent
open StochasticLinearizationError
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem different_source_difference {Kb Ks : ℝ≥0} (D : BrownianDriver N P F)
    (ax ay : Fin N→Coefficient (N:=N) (F:=F) (P:=P) Kb)
    (sx sy : Fin N→Fin N→Coefficient (N:=N) (F:=F) (P:=P) Ks)
    (T : ℝ≥0) (Ax Ay : PredictableStateL2 N F P) :
    LinearVariationalSDE.sourceClass D ay sy T Ay-LinearVariationalSDE.sourceClass D ax sx T Ax=
      sourceLinearMap D ax sx T
        (Ay-Ax+driftSource T (fun i =>
          apply (ay i) (LinearVariationalSDE.sourceClass D ay sy T Ay)-
            apply (ax i) (LinearVariationalSDE.sourceClass D ay sy T Ay))+
        noiseSource D T (fun i j =>
          apply (sy i j) (LinearVariationalSDE.sourceClass D ay sy T Ay)-
            apply (sx i j) (LinearVariationalSDE.sourceClass D ay sy T Ay))) := by
  let U := LinearVariationalSDE.sourceClass D ax sx T Ax
  let V := LinearVariationalSDE.sourceClass D ay sy T Ay
  apply (LinearVariationalSDE.exists_unique_picard_fixedPoint D ax sx T _).choose_spec.2
  have hu := LinearVariationalSDE.sourceClass_fixedPoint D ax sx T Ax
  have hv := LinearVariationalSDE.sourceClass_fixedPoint D ay sy T Ay
  change U=Ax+_+_ at hu
  change V=Ay+_+_ at hv
  have hd : LinearVariationalSDE.finiteDriftPicardMap ay T V-
      LinearVariationalSDE.finiteDriftPicardMap ax T V=
      driftSource T (fun i => apply (ay i) V-apply (ax i) V) := by
    simp only [LinearVariationalSDE.finiteDriftPicardMap,LinearVariationalSDE.driftCoefficientMap,
      driftSource,VolterraLinearity.driftOperator_apply,VolterraLinearity.stateInclusion_apply,
      map_sub,Finset.sum_sub_distrib]
  have hs : LinearVariationalSDE.finiteNoisePicardMap D sy T V-
      LinearVariationalSDE.finiteNoisePicardMap D sx T V=
      noiseSource D T (fun i j => apply (sy i j) V-apply (sx i j) V) := by
    simp only [LinearVariationalSDE.finiteNoisePicardMap,LinearVariationalSDE.stochasticCoefficientMap,
      noiseSource,VolterraLinearity.itoOperator_apply,VolterraLinearity.stateInclusion_apply,
      map_sub,Finset.sum_sub_distrib]
  rw [←hd,←hs,finiteDrift_sub,finiteNoise_sub]
  have he := congrArg₂ (fun v u : PredictableStateL2 N F P => v-u) hv hu
  exact he.trans (by abel)

end SphericalAging.LinearResponseDifferentSourceDifference
