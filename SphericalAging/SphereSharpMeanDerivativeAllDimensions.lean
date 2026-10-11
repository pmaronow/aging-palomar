module

public import SphericalAging.SphereSharpMeanDerivative
public import SphericalAging.PhysicalVariationNormComparison

public section

/-! Actual sharp tangent mean derivative for every N≥2. The physical
response norm is treated by genuine smooth norm Itô, retaining the radial
noise cancellation in dimension two. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SphericalAging.SphereSharpMeanDerivativeAllDimensions
open HardSphereDynamics FiniteModel LocalSDE HamiltonianTerminalDerivative
open PhysicalVariationalBounds PhysicalVariationalMoments ActualSphereTransition ActualSphereMeanDerivative
open VariationalCoefficients
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem terminal_tangent_firstMoment (hN : 2≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (x v : State N) (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0)
    (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    (∫ ω,‖(stateResponse (NullAugmentation.driver D₀) β J R hR x T t v) ω‖ ∂P)≤
      ‖v‖*Real.exp (((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t:ℝ)) := by
  have hn : 0<N := by omega
  let D := NullAugmentation.driver D₀
  let hb := (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
  let hs := (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec
  let X := GlobalSDE.horizonProcess D hb hs x T
  obtain ⟨Y,hY,hEq,hTan⟩ := PhysicalTangentResponse.exists_tangent_response_solution
    hn D₀ β J R hR hNR x v hx hv T hT
  have hPhys := PhysicalVariationalEquation.physical_of_cutoff (Nat.ne_of_gt hn) D₀ β J R hR hNR
    hb hs x v hx T Y hY
  have hSphere := horizonProcess_onSphere (Nat.ne_of_gt hn) D₀ β J R hR hNR x hx T hb hs
  have hXc : ∀ᵐ ω ∂P,Continuous (fun s => X s ω) := GlobalSDE.horizonProcess_continuous D hb hs x T
  have hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 →
      MeasurableSet[NullAugmentation.augment F P 0] A := by
    intro A hA hzero
    exact NullAugmentation.augment_null_known_zero F hA hzero
  have hYfourth (s : ℝ≥0) (hss : s≤T) : Integrable (fun ω => ‖Y s ω‖^4) P := by
    have hh := (LinearSDELocalization.linear_solution_fourthMoment hY hnull s hss).1.integrable_norm_rpow'
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using hh
  have hYtime : Integrable (fun q => ‖LinearSDETimeFourthMoment.stateTimeCut Y T q‖^4)
      (nonnegativeLebesgueMeasure.prod P) := by
    have hh := (LinearSDETimeFourthMoment.linear_solution_time_fourthMoment hY hnull).1.integrable_norm_rpow (by norm_num) (by norm_num)
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using hh
  have hh := PhysicalVariationNormComparison.norm_firstMoment hN hp β J D X Y v T hPhys
    hXc hSphere hTan hYfourth hYtime t ht
  rw [integral_congr_ae ((hEq t).mono fun ω he => congrArg (fun z : State N => ‖z‖) he)]
  exact hh

theorem mean_derivative_norm_le_tangent (hN : 2≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (x v : State N) (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0)
    (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    ‖fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t) x v‖≤
      Real.exp (((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t:ℝ))*‖v‖ := by
  rw [(mean_hasFDerivAt D₀ β J R hR x T t ht hT).fderiv]
  change ‖expectationOperator (stateResponse (NullAugmentation.driver D₀) β J R hR x T t v)‖≤_
  rw [expectationOperator_apply]
  have hh := norm_integral_le_integral_norm (μ:=P)
    (stateResponse (NullAugmentation.driver D₀) β J R hR x T t v : Ω → State N)
  have hb := terminal_tangent_firstMoment hN hp D₀ β R hR hNR J x v hx hv T t ht hT
  exact hh.trans (by simpa only [mul_comm] using hb)

theorem mean_tangent_derivative_norm_le (hN : 2≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (x v : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    ‖fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t) x (projection x v)‖≤
      Real.exp (((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t:ℝ))*‖v‖ := by
  have hn : 0<N := by omega
  have hv : ⟪x,projection x v⟫_ℝ=0 := projection_tangent (Nat.ne_of_gt hn) x v hx
  exact (mean_derivative_norm_le_tangent hN hp D₀ β R hR hNR J x (projection x v) hx hv T t ht hT).trans
    (mul_le_mul_of_nonneg_left (projection_norm_le_onSphere (Nat.ne_of_gt hn) x v hx)
      (Real.exp_nonneg _))

theorem mean_tangent_derivative_norm_le_landscape_cutoff (hN : 2≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R Q : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (hJ : GaussianLandscape.landscapeNorm N p J≤Q)
    (x v : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    ‖fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t) x (projection x v)‖≤
      Real.exp (((β:ℝ)*(p:ℝ)^2*(Q:ℝ))*(t:ℝ))*‖v‖ := by
  apply (mean_tangent_derivative_norm_le hN hp D₀ β R hR hNR J x v hx T t ht hT).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hJ (mul_nonneg β.coe_nonneg (sq_nonneg _))) t.coe_nonneg

end SphericalAging.SphereSharpMeanDerivativeAllDimensions
