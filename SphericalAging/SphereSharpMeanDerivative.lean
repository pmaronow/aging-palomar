module

public import SphericalAging.ActualSphereMeanDerivative
public import SphericalAging.PhysicalTangentResponse
public import SphericalAging.SphereTangentVariationalGeometry
public import SphericalAging.VectorSDEQuadraticLocalization

public section

/-! Sharp actual tangent mean derivative for N≥3. The genuine response
is tangent by differentiating sphere-valued terminal classes. Its exact
quadratic Itô drift and stopping comparison give the rate β p² Q. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.SphereSharpMeanDerivative
open HardSphereDynamics FiniteModel LocalSDE HamiltonianTerminalDerivative
open PhysicalVariationalBounds PhysicalVariationalMoments SphereTangentVariationalGeometry
open ActualSphereTransition ActualSphereMeanDerivative
open VariationalCoefficients
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem terminal_tangent_secondMoment (hN : 3≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (x v : State N) (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0)
    (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    (∫ ω,‖(stateResponse (NullAugmentation.driver D₀) β J R hR x T t v) ω‖^2 ∂P)≤
      ‖v‖^2*Real.exp ((2*(β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t:ℝ)) := by
  have hn : 0<N := by omega
  let D := NullAugmentation.driver D₀
  let hb := (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
  let hs := (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec
  let X := GlobalSDE.horizonProcess D hb hs x T
  let a := StochasticFlowDerivative.driftRows D (cutoffDrift_contDiff β J R hR) hb hs x T
  let sigma := StochasticFlowDerivative.noiseRows D (cutoffNoise_contDiff R hR) hb hs x T
  let K : ℝ≥0 := ⟨2*(β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J,
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) β.coe_nonneg) (sq_nonneg _))
      (GaussianLandscape.landscapeNorm_nonnegative N p J)⟩
  obtain ⟨Y,hY,hEq,hTan⟩ := PhysicalTangentResponse.exists_tangent_response_solution
    hn D₀ β J R hR hNR x v hx hv T hT
  have hSphere := horizonProcess_onSphere (Nat.ne_of_gt hn) D₀ β J R hR hNR x hx T hb hs
  have hSp := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hSphere
  have hTp := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hTan
  have hquad : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      (∑ i : Fin N,2*(Y q.1 q.2) i*(a i).value q (Y q.1 q.2))+
        (∑ i : Fin N,∑ j : Fin N,((sigma i j).value q (Y q.1 q.2))^2)≤K*‖Y q.1 q.2‖^2 := by
    filter_upwards [hSp,hTp] with q hsp htp
    by_cases hq : q.1∈Ioc (0:ℝ≥0) T
    · have hxs : OnSphere (X q.1 q.2) := hsp q.1 hq.2
      have hxr : ‖X q.1 q.2‖<(R:ℝ) := by
        have hh := (onSphere_iff_norm_sq _).mp hxs
        nlinarith [norm_nonneg (X q.1 q.2),R.coe_nonneg]
      have heA i : (a i).value q (Y q.1 q.2)=
          (fderiv ℝ (hamiltonianDrift β J) (X q.1 q.2) (Y q.1 q.2)) i := by
        change (if q.1∈Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffDrift β J R hR i)
          (X q.1 q.2) else 0) (Y q.1 q.2)=_
        rw [ite_eq_left hq]
        exact fderiv_cutoffDrift_apply β J R hR _ _ hxr i
      have heU i j : (sigma i j).value q (Y q.1 q.2)=
          (fderiv ℝ (fun y : State N => noiseColumn y j) (X q.1 q.2) (Y q.1 q.2)) i := by
        change (if q.1∈Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j)
          (X q.1 q.2) else 0) (Y q.1 q.2)=_
        rw [ite_eq_left hq]
        exact fderiv_cutoffNoise_apply R hR _ _ hxr i j
      simp_rw [heA,heU]
      have hi : (∑ i : Fin N,2*(Y q.1 q.2) i*
          (fderiv ℝ (hamiltonianDrift β J) (X q.1 q.2) (Y q.1 q.2)) i)=
          2*⟪Y q.1 q.2,fderiv ℝ (hamiltonianDrift β J) (X q.1 q.2) (Y q.1 q.2)⟫_ℝ := by
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
        congr 1
        simpa only [mul_comm] using coordinate_inner_sum (Y q.1 q.2)
          (fderiv ℝ (hamiltonianDrift β J) (X q.1 q.2) (Y q.1 q.2))
      rw [hi,Finset.sum_comm]
      simp_rw [coordinate_square_sum,real_inner_self_eq_norm_sq]
      exact tangent_secondMoment_generator_le hN hp β.coe_nonneg J _ _ hxs (htp q.1 hq.2)
    · have heA i : (a i).value q (Y q.1 q.2)=0 := by
        change (if q.1∈Ioc 0 T then _ else (0:State N →L[ℝ] ℝ)) (Y q.1 q.2)=0
        rw [ite_eq_right hq];rfl
      have heU i j : (sigma i j).value q (Y q.1 q.2)=0 := by
        change (if q.1∈Ioc 0 T then _ else (0:State N →L[ℝ] ℝ)) (Y q.1 q.2)=0
        rw [ite_eq_right hq];rfl
      simp_rw [heA,heU,mul_zero,zero_pow (by norm_num : (2:ℕ)≠0),Finset.sum_const_zero,zero_add]
      positivity
  have hY' : RandomLinearVariationalSDE.IsStrongSolutionOn a sigma D (fun _ => v) Y T := hY
  have hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 →
      MeasurableSet[NullAugmentation.augment F P 0] A := by
    intro A hA hzero
    exact NullAugmentation.augment_null_known_zero F hA hzero
  have hh := VectorSDEQuadraticLocalization.solution_secondMoment hY'
    (memLp_const v) ‖v‖₊ (.of_forall fun _ => le_rfl) K hquad hnull t ht
  have hh' := hh.2
  have hk : (K:ℝ)=2*(β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J := rfl
  rw [hk] at hh'
  rw [integral_congr_ae ((hEq t).mono fun ω he => congrArg (fun z : State N => ‖z‖^2) he)]
  simpa only [integral_const,probReal_univ,one_smul,smul_eq_mul,one_mul] using hh'

theorem mean_derivative_norm_le_tangent (hN : 3≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (x v : State N) (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0)
    (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    ‖fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t) x v‖≤
      Real.exp (((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t:ℝ))*‖v‖ := by
  let U := stateResponse (NullAugmentation.driver D₀) β J R hR x T t v
  have hh : ‖expectationOperator U‖^2≤∫ ω,‖U ω‖^2 ∂P := by
    rw [PredictableFamilyLift.integral_norm_sq_Lp]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_integral_lp_two_le U) 2
  have hb := hh.trans (terminal_tangent_secondMoment hN hp D₀ β R hR hNR J x v hx hv T t ht hT)
  rw [(mean_hasFDerivAt D₀ β J R hR x T t ht hT).fderiv]
  change ‖expectationOperator U‖≤_
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.exp_nonneg _) (norm_nonneg v))).mp
  rw [mul_pow,← Real.exp_nat_mul]
  have he : (2:ℕ)*(((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t:ℝ))=
      (2*(β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t:ℝ) := by ring
  rw [he,mul_comm]
  exact hb

/-- Sharp actual projected mean derivative, with no regularity or moment
premise for the mean or response. N≥3 suffices for dimension limits. -/
theorem mean_tangent_derivative_norm_le (hN : 3≤N) (hp : 2≤p)
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

theorem mean_tangent_derivative_norm_le_landscape_cutoff (hN : 3≤N) (hp : 2≤p)
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

end SphericalAging.SphereSharpMeanDerivative
