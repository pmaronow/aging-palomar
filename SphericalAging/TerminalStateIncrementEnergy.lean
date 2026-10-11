module

public import SphericalAging.WholeVectorCoefficientEnergy
public import SphericalAging.ShiftedDrift
public import SphericalAging.ShiftedItoProcess

public section

/-! True whole-vector terminal increments. Time translation preserves
the complete drift energy and matrix noise trace, without dimension factors. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.TerminalStateIncrementEnergy
open HardSphereDynamics LocalSDE TerminalLinearity TerminalStateRepresentation
open PredictableDriftTime ShiftedDrift ShiftedPredictable ShiftedItoProcess
open WholeVectorTerminalEnergy WholeVectorCoefficientEnergy
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem driftTerminal_timeShift (A : PredictableProcessL2 F P) (s t : ℝ≥0) :
    driftTerminalOperator t t (predictableShift s A)=
      driftTerminalOperator (s+t) (s+t) A-driftTerminalOperator (s+t) s A := by
  apply Lp.ext
  filter_upwards [(driftVersion_memLp (predictableShift s A) t t).coeFn_toLp,
    (driftVersion_memLp A (s+t) (s+t)).coeFn_toLp,
    (driftVersion_memLp A (s+t) s).coeFn_toLp,
    Lp.coeFn_sub (driftTerminalOperator (s+t) (s+t) A)
      (driftTerminalOperator (s+t) s A),driftVersion_timeShift A s t]
      with omega hL hR hS hsub hshift
  change ((driftVersion_memLp (predictableShift s A) t t).toLp _) omega = _
  rw [hL,hsub,Pi.sub_apply]
  change _=((driftVersion_memLp A (s+t) (s+t)).toLp _) omega-
    ((driftVersion_memLp A (s+t) s).toLp _) omega
  rw [hR,hS]
  exact hshift t le_rfl

theorem terminalClass_timeShift (D : BrownianDriver N P F) (v : State N)
    (A : Fin N→PredictableProcessL2 F P)
    (S : Fin N→Fin N→PredictableProcessL2 F P) (s t : ℝ≥0) :
    terminalClass (ShiftedBrownian.driver D s) 0 (fun i => predictableShift s (A i))
      (fun i j => predictableShift s (S i j)) t t=
    terminalClass D v A S (s+t) (s+t)-terminalClass D v A S (s+t) s := by
  have hnoise (i : Fin N) :
      (∑ j,itoTerminalOperator (ShiftedBrownian.driver D s) j t (predictableShift s (S i j)))=
      (∑ j,itoTerminalOperator D j (s+t) (S i j))-
        (∑ j,itoTerminalOperator D j s (S i j)) := by
    simpa only [itoTerminalOperator_apply,VectorIto.vectorProcessLp,VectorIto.vectorIto,
      VectorIto.coordinateIto,FourPapersCommon.FilteredBrownian.naturalItoProcess]
      using vectorProcessLp_timeShift D s t (S i)
  simp only [terminalClass,map_zero,zero_add,driftTerminal_timeShift,hnoise,map_add,map_sub,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  abel

theorem terminalClass_increment_norm_sq_le (D : BrownianDriver N P F) (v : State N)
    (A : Fin N→PredictableProcessL2 F P)
    (S : Fin N→Fin N→PredictableProcessL2 F P) (s t : ℝ≥0) :
    ‖terminalClass D v A S (s+t) (s+t)-terminalClass D v A S (s+t) s‖^2≤
      2*(t:ℝ)*(∑ i,‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict
        (ShiftedBrownian.filtration F s) t (predictableShift s (A i))‖^2)+
      2*(∑ i,∑ j,‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict
        (ShiftedBrownian.filtration F s) t (predictableShift s (S i j))‖^2) := by
  rw [←terminalClass_timeShift]
  exact terminalClass_zero_norm_sq_le (ShiftedBrownian.driver D s)
    (fun i => predictableShift s (A i)) (fun i j => predictableShift s (S i j)) t t le_rfl

end SphericalAging.TerminalStateIncrementEnergy
