module

public import SphericalAging.ActualGammaBackwardPredictor

public section

/-! Genuine fourth moments of arbitrary actual vector Wiener increments,
obtained from the constructed measure-preserving future path. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace SphericalAging.BrownianVectorIncrementFourthMoment
open HardSphereDynamics BrownianVectorMoments BrownianFuturePath ActualGammaBackwardPredictor
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

theorem increment_fourthMoment (r h : ℝ≥0) :
    MemLp (fun ω => brownianVector (N:=N) (r+h) ω-brownianVector r ω) 4 (VectorBrownian.law N) ∧
    (∫ ω,‖brownianVector (N:=N) (r+h) ω-brownianVector r ω‖^4 ∂VectorBrownian.law N)≤
      3*(N : ℝ)^2*(h : ℝ)^2 := by
  refine ⟨(brownianVector_memLp (r+h) (q:=4) (by norm_num)).sub (brownianVector_memLp r (q:=4) (by norm_num)),?_⟩
  have hMP := future_measurePreserving (N:=N) r
  have hBm : StronglyMeasurable (brownianVector (N:=N) h) :=
    (ActualGammaFutureInnovation.brownianVector_waiting_measurable h).stronglyMeasurable.mono
      ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le h)
  have hF : StronglyMeasurable (fun ω : VectorBrownian.Space N => ‖brownianVector h ω‖^4) := by
    exact (continuous_id.pow 4).comp_stronglyMeasurable hBm.norm
  have he : (∫ ω,‖brownianVector (N:=N) (r+h) ω-brownianVector r ω‖^4 ∂VectorBrownian.law N)=
      ∫ ω,‖brownianVector (N:=N) h ω‖^4 ∂VectorBrownian.law N := by
    conv_rhs => rw [←hMP.map_eq,integral_map hMP.measurable.aemeasurable
      hF.aestronglyMeasurable]
    apply integral_congr_ae
    exact .of_forall (fun ω => congrArg (fun z : State N => ‖z‖^4) (brownianVector_future r h ω).symm)
  rw [he]
  exact brownianVector_fourthMoment_le h

end SphericalAging.BrownianVectorIncrementFourthMoment
