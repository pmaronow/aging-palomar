module

public import SphericalAging.ActualGammaConcentration
public import SphericalAging.WeightedBrownianRowVariance

public section

/-! The state-earlier Brownian-later Γ increment under the actual full law.
Its zero mean and dimension-sharp second moment follow from the genuine
independent-background Brownian driver and actual adapted sphere process. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualGammaFutureObservation
open FiniteModel HardSphereDynamics LocalSDE ActualStateIncrementMoments
open ActualBrownianPrimitiveTimeModulus WeightedBrownianNoiseRow WeightedBrownianRowVariance
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def futurePairing (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t s : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : ℝ :=
  ⟪actualState β R hR t ω,actualBrownian s ω-actualBrownian t ω⟫_ℝ/(Real.sqrt 2*(N : ℝ))

theorem gamma_eq_diagonal_add_future (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t s : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :
    actualGamma β R hR t s ω=actualGamma β R hR t t ω+futurePairing β R hR t s ω := by
  simp only [actualGamma,futurePairing,inner_sub_right]
  ring

theorem actual_futurePairing_secondMoment (hN : 1≤N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (t s : ℝ≥0) (hts : t≤s) :
    MemLp (futurePairing (p:=p) β R hR t s) 2 (AnnealedModelLaw.law N p) ∧
      (∫ω,futurePairing (p:=p) β R hR t s ω ∂AnnealedModelLaw.law N p)=0 ∧
      (∫ω,(futurePairing (p:=p) β R hR t s ω)^2 ∂AnnealedModelLaw.law N p)=
        ((s : ℝ)-(t : ℝ))/(2*(N : ℝ)) := by
  let P := AnnealedModelLaw.law N p
  let D := AnnealedModelLaw.driver N p
  let d := Real.sqrt 2*(N : ℝ)
  let Z : Fin N→AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N→ℝ :=
    fun j ω => (actualState β R hR t ω) j/d
  have hXm : StronglyMeasurable[AnnealedModelLaw.filtration N p t] (actualState (p:=p) β R hR t) :=
    AnnealedGlobalSDE.globalProcess_stronglyAdapted (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR (AnnealedModelLaw.parameter_disorder_memLp N p) t
  have hZ2 (j : Fin N) : MemLp (Z j) 2 P := by
    unfold Z
    simpa only [div_eq_mul_inv,VariationalCoefficients.coordinate_apply] using
      ((actualState_memLp (p:=p) hN β R hR hNR t).continuousLinearMap_comp (VariationalCoefficients.coordinate j)).mul_const d⁻¹
  have hZm (j : Fin N) : AEStronglyMeasurable[AnnealedModelLaw.filtration N p t] (Z j) P := by
    unfold Z
    simpa only [div_eq_mul_inv,VariationalCoefficients.coordinate_apply] using
      (((VariationalCoefficients.coordinate j).continuous.comp_stronglyMeasurable hXm).mul_const d⁻¹).aestronglyMeasurable
  have he (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :
      futurePairing β R hR t s ω=∑j : Fin N,Z j ω*VectorIto.increment D j t s ω := by
    let x := actualState (p:=p) β R hR t ω
    let w := actualBrownian (N:=N) (p:=p) s ω-actualBrownian t ω
    have hi : ⟪x,w⟫_ℝ=∑j : Fin N,x j*w j := by
      calc
        _=⟪∑j : Fin N,x j • basisVector j,w⟫_ℝ := congrArg (fun z : State N => ⟪z,w⟫_ℝ) (state_sum_basis x).symm
        _=_ := by
          rw [sum_inner]
          apply Finset.sum_congr rfl
          intro j _
          rw [real_inner_smul_left,real_inner_comm,basis_inner]
    change ⟪x,w⟫_ℝ/d=_
    rw [hi,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    change (x j*w j)/d=(x j/d)*w j
    ring
  have hfun : futurePairing (p:=p) β R hR t s=fun ω => ∑j : Fin N,Z j ω*VectorIto.increment D j t s ω := funext he
  have hh := row_secondMoment D hts Z hZ2 hZm
  have hzero := row_integral D hts Z hZ2 hZm
  rw [hfun]
  refine ⟨hh.1,hzero,?_⟩
  rw [hh.2]
  have hn : (N : ℝ)≠0 := (Nat.cast_pos.mpr (by omega : 0<N)).ne'
  have hd : d^2=2*(N : ℝ)^2 := by dsimp [d];rw [mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  have hrow : ∀ᵐ ω ∂P,(∑j : Fin N,(Z j ω)^2)=1/(2*(N : ℝ)) := by
    filter_upwards [actualState_onSphere (p:=p) hN β R hR hNR] with ω hω
    simp only [Z,div_pow,←Finset.sum_div,coordinate_square_sum,real_inner_self_eq_norm_sq]
    rw [(onSphere_iff_norm_sq _).mp (hω t),hd]
    field_simp
  rw [integral_congr_ae hrow]
  simp only [integral_const,probReal_univ,one_smul]
  ring

end SphericalAging.ActualGammaFutureObservation
