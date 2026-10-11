module

public import SphericalAging.RandomHamiltonianFutureRestart
public import SphericalAging.ActualSphereMeanJointSpatialContinuity

public section

/-! Genuine expectation restart for every waiting-measurable L² initial
state. Product integrability is obtained from the actual terminal L²
class and the proved waiting/future measure-preserving map. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.RandomHamiltonianFutureExpectation
open HardSphereDynamics ActualSphereTransition RandomInitialDependence
open BrownianFuturePath BrownianFutureFiltered RandomHamiltonianFutureRestart
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem terminalClass_expectation_eq_mean (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) (s T t : ℝ≥0) (ht : t≤T)
    (Z : VectorBrownian.Space N → State N)
    (hZ : StronglyMeasurable[(NullAugmentation.augment (VectorBrownian.filtration N)
      (VectorBrownian.law N)) s] Z) (hm : MemLp Z 2 (VectorBrownian.law N)) :
    let hZ0 : StronglyMeasurable[ShiftedBrownian.filtration
      (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)) s 0] Z :=
        by rw [ShiftedBrownian.filtration_zero];exact hZ
    (∫ ω,RandomHamiltonianTerminal.terminalClass
      (ShiftedBrownian.driver (NullAugmentation.driver (VectorBrownian.driver N)) s)
      β R hR T t (J,initialStateClass Z hZ0 hm) ω ∂VectorBrownian.law N)=
        ∫ ω,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t (Z ω)
          ∂VectorBrownian.law N := by
  intro hZ0
  let P := VectorBrownian.law N
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  have hZm : Measurable Z := (hZ.mono ((NullAugmentation.augment (VectorBrownian.filtration N) P).le s)).measurable
  let μ := P.map Z
  letI : IsProbabilityMeasure μ := (hasLaw_map hZm.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  let G : State N×VectorBrownian.Space N → State N := fun q => jointProcess D β R hR (J,q.1) t q.2
  have hGm : StronglyMeasurable G := (terminal_measurable D β R hR J t).stronglyMeasurable
  let φ : VectorBrownian.Space N → State N×VectorBrownian.Space N := fun ω => (Z ω,future s ω)
  have hφ : MeasurePreserving φ P (μ.prod P) := waiting_future_measurePreserving s Z hZ.measurable
  have hae := terminalClass_ae_future β R hR J s T t ht Z hZ hm
  let U := RandomHamiltonianTerminal.terminalClass (ShiftedBrownian.driver D s) β R hR T t
    (J,initialStateClass Z hZ0 hm)
  have hGp : MemLp (G ∘ φ) 2 P := (Lp.memLp U).ae_eq hae
  have hG : MemLp G 2 (μ.prod P) := by
    rw [← hφ.map_eq]
    exact (memLp_map_measure_iff (by rw [hφ.map_eq];exact hGm.aestronglyMeasurable)
      hφ.measurable.aemeasurable).mpr hGp
  have hmmean : StronglyMeasurable (fun x : State N => mean D β R hR J t x) := by
    have hh := (ActualSphereMeanJointSpatialContinuity.mean_joint_continuous
      (VectorBrownian.driver N) β J R hR).comp
      (continuous_const.prodMk continuous_id : Continuous (fun x : State N => (t,x)))
    exact hh.stronglyMeasurable
  calc
    _=∫ ω,G (φ ω) ∂P := integral_congr_ae hae
    _=∫ q,G q ∂μ.prod P := by
      rw [← hφ.map_eq]
      exact (integral_map hφ.measurable.aemeasurable hGm.aestronglyMeasurable).symm
    _=∫ x,mean D β R hR J t x ∂μ := integral_prod G (hG.integrable (by norm_num))
    _=_ := integral_map hZm.aemeasurable hmmean.aestronglyMeasurable

end SphericalAging.RandomHamiltonianFutureExpectation
