module

public import SphericalAging.ShiftedBrownian

public section
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ShiftedBrownianAssociativity
open HardSphereDynamics
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
lemma filtration_add (s d : ℝ≥0) :
    ShiftedBrownian.filtration (ShiftedBrownian.filtration F s) d=
      ShiftedBrownian.filtration F (s+d) := by
  apply Filtration.ext
  funext t
  change F (s+(d+t))=F ((s+d)+t)
  rw [add_assoc]
lemma driver_ext (D E : BrownianDriver N P F) (h : D.coordinate=E.coordinate) : D=E := by
  cases D
  cases E
  simp_all
lemma driver_heq {G : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (hf : F=G) (D : BrownianDriver N P F) (E : BrownianDriver N P G)
    (hc : D.coordinate=E.coordinate) : HEq D E := by
  subst G
  exact heq_of_eq (driver_ext D E hc)
lemma driver_add (D : BrownianDriver N P F) (s d : ℝ≥0) :
    HEq (ShiftedBrownian.driver (ShiftedBrownian.driver D s) d)
      (ShiftedBrownian.driver D (s+d)) := by
  have hf := filtration_add (F:=F) s d
  have hc : (ShiftedBrownian.driver (ShiftedBrownian.driver D s) d).coordinate=
      (ShiftedBrownian.driver D (s+d)).coordinate := by
    funext i t w
    simp only [ShiftedBrownian.driver_coordinate,add_assoc]
    ring
  exact driver_heq hf _ _ hc
end SphericalAging.ShiftedBrownianAssociativity
