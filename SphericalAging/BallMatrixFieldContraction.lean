module

public import SphericalAging.BallResponseEnergyContraction

public section

/-! Genuine ball-center rank-one estimates for jointly measurable
physical response matrix fields, obtained from their finite columns. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.BallMatrixFieldContraction
open MeasureTheory ProbabilityTheory FiniteModel HardSphereDynamics
  ResponseMatrixEnergyContraction BallResponseEnergyContraction EnergyCovarianceContraction
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem matrix_field_sample_representation (U : Ω→State N→L[ℝ] State N)
    (hm : ∀i : Fin N,MemLp (fun ω => U ω (basisVector i)) 4 P) :
    ∃M : State N→L[ℝ] Lp (State N) 2 P,
      U=ᵐ[P] sampleMatrix M ∧
      ∀i : Fin N,(M (basisVector i) : Ω→State N)=ᵐ[P] (fun ω => U ω (basisVector i)) := by
  let hm₂ (i : Fin N) := (hm i).mono_exponent (by norm_num : (2:ℝ≥0∞)≤4)
  let V (i : Fin N) : Lp (State N) 2 P := (hm₂ i).toLp (fun ω => U ω (basisVector i))
  let M : State N→L[ℝ] Lp (State N) 2 P :=
    ∑i : Fin N,(VariationalCoefficients.coordinate i).smulRight (V i)
  have hb (i : Fin N) : M (basisVector i)=V i := by
    simp [M,ContinuousLinearMap.smulRight_apply,basisVector,PiLp.single_apply]
  have hrep (i : Fin N) : (M (basisVector i) : Ω→State N)=ᵐ[P]
      (fun ω => U ω (basisVector i)) := by rw [hb];exact (hm₂ i).coeFn_toLp
  refine ⟨M,?_,hrep⟩
  filter_upwards [ae_all_iff.mpr hrep] with ω hω
  apply ContinuousLinearMap.ext
  intro v
  conv_lhs => rw [←LocalSDE.state_sum_basis v,map_sum]
  rw [sampleMatrix_apply]
  simp only [map_smul,hω]

theorem ball_field_energyCorrection_moments (hN : 0<N) (hp : 2≤p)
    (U : Ω→State N→L[ℝ] State N) (C : ℝ)
    (hm : ∀i : Fin N,MemLp (fun ω => U ω (basisVector i)) 4 P)
    (hb : ∀i : Fin N,(∫ω,‖U ω (basisVector i)‖^4 ∂P)≤C)
    {x y : Ω→State N} (hxm : AEStronglyMeasurable x P) (hym : AEStronglyMeasurable y P)
    (hx : ∀ᵐω ∂P,‖x ω‖≤Real.sqrt (N:ℝ)) (hy : ∀ᵐω ∂P,‖y ω‖≤Real.sqrt (N:ℝ)) :
    MemLp (fun ω => energyCorrection (p:=p) (x ω) (y ω) (U ω)) 2 P ∧
    (∫ω,(energyCorrection (p:=p) (x ω) (y ω) (U ω))^2 ∂P)≤
      ((p:ℝ)^2*((p:ℝ)-1)^2/(N:ℝ))*(1+C) ∧
    (∫ω,|energyCorrection (p:=p) (x ω) (y ω) (U ω)| ∂P)≤
      Real.sqrt (((p:ℝ)^2*((p:ℝ)-1)^2/(N:ℝ))*(1+C)) := by
  obtain ⟨M,hU,hcols⟩ := matrix_field_sample_representation U hm
  have hm' (i : Fin N) : MemLp (M (basisVector i) : Ω→State N) 4 P :=
    (memLp_congr_ae (hcols i)).mpr (hm i)
  have hb' (i : Fin N) : (∫ω,‖M (basisVector i) ω‖^4 ∂P)≤C := by
    rw [integral_congr_ae ((hcols i).mono fun ω hω => congrArg (fun z : State N => ‖z‖^4) hω)]
    exact hb i
  have h := ball_energyCorrection_secondMoment hN hp M C hm' hb' hxm hym hx hy
  have he : (fun ω => energyCorrection (p:=p) (x ω) (y ω) (U ω))=ᵐ[P]
      (fun ω => energyCorrection (p:=p) (x ω) (y ω) (sampleMatrix M ω)) :=
    hU.mono fun ω hω => congrArg (energyCorrection (p:=p) (x ω) (y ω)) hω
  refine ⟨(memLp_congr_ae he).mpr h.1,?_,?_⟩
  · rw [integral_congr_ae (he.mono fun ω hω => congrArg (fun z : ℝ => z^2) hω)]
    exact h.2
  · rw [integral_congr_ae (he.mono fun ω hω => congrArg abs hω)]
    exact (integral_abs_le_sqrt_secondMoment h.1).trans (Real.sqrt_le_sqrt h.2)

end SphericalAging.BallMatrixFieldContraction
