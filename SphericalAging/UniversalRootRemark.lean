module

public import SphericalAging.UniversalRootBandUniqueness
public import SphericalAging.UniversalRootThresholdQuadratic

public section

/-! Exact mathematical assertions of Remark13.3. Coordinate interpretation
and the caution about trace convergence are explanatory prose; the literal
band law, uniqueness, finite coherent mass, and threshold quadratic form
are proved below. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace SphericalAging.UniversalRootRemark
open UniversalRootInterval UniversalRootKernel UniversalRootBandMeasure
open UniversalRootBandUniqueness UniversalRootThresholdQuadratic
open CausalTree TreeCeilings TreeCoherentRoot
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem source13_3 :
    bandLaw=unitMeasure.withDensity bandDensity ∧
    squaredBandMass weight=unitMeasure ∧
    (∀g : ℝ→ℝ,Measurable g→0≤ᵐ[unitMeasure] g→squaredBandMass g=unitMeasure→
      (fun z : ℝ×ℝ => g (max z.1 z.2))=ᵐ[unitMeasure.prod unitMeasure] kernel) ∧
    (∀v : Space 2,∀j : ℕ,‖coherentShell v j‖^2=heightMass v j) ∧
    inner ℝ one (universalOperator one)=cubicCeiling := by
  refine ⟨bandLaw_eq_density,weight_squaredBandMass,?_,?_,universalOperator_one_quadratic⟩
  · intro g hg hn hMass
    exact max_kernel_unique hg hn hMass
  · intro v j
    rw [coherentShell_norm]
    rfl

end SphericalAging.UniversalRootRemark
