module

public import SphericalAging.ActualGammaBackwardPredictor
public import SphericalAging.SphereNoiseGradient

public section

/-! Genuine dimension-sharp noise contraction of the actual backward Γ
predictor. The observed state and Brownian vector may be correlated. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualGammaPredictorNoiseBounds
open FiniteModel HardSphereDynamics LocalSDE ActualSphereTransition ActualSphereMeanDerivative
open ActualGammaBackwardPredictor ActualGammaFutureInnovation ActualSphereGammaVariance
open ActualDisorderGammaVariance ActualSphereLinearTransition SphereNoiseGradient BrownianVectorMoments
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def linearTest (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (t r : ℝ≥0) (b x : State N) : ℝ :=
  ⟪b,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-r) x⟫_ℝ/(Real.sqrt 2*(N : ℝ))

theorem linearTest_fderiv (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (t r : ℝ≥0) (b x v : State N) :
    fderiv ℝ (linearTest β R hR J t r b) x v=
      ⟪b,fderiv ℝ (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-r)) x v⟫_ℝ/
        (Real.sqrt 2*(N : ℝ)) := by
  have hm := (mean_hasFDerivAt (VectorBrownian.driver N) β J R hR x ((t-r)+1) (t-r) (by simp) (by positivity)).differentiableAt.hasFDerivAt
  have hh := (((innerSL ℝ b).hasFDerivAt.comp x hm).const_mul ((Real.sqrt 2*(N : ℝ))⁻¹)).fderiv
  unfold linearTest
  simpa only [div_eq_mul_inv,Function.comp_def,innerSL_apply_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,smul_eq_mul,mul_comm] using congrArg (fun L : State N→L[ℝ]ℝ => L v) hh

theorem linearTest_projected_derivative (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (T t r : ℝ≥0) (ht : t≤T) (x b v : State N) (hx : OnSphere x) :
    ‖fderiv ℝ (linearTest β R hR J t r b) x (projection x v)‖≤
      (‖b‖*Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T)/
        (Real.sqrt 2*(N : ℝ)))*‖v‖ := by
  rw [linearTest_fderiv,norm_div,Real.norm_of_nonneg (by positivity : (0 : ℝ)≤Real.sqrt 2*(N : ℝ))]
  have hh := SphereSharpMeanDerivative.mean_tangent_derivative_norm_le hN hp (VectorBrownian.driver N) β R hR hNR J x v hx
    ((t-r)+1) (t-r) (by simp) (by positivity)
  have he : Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*((t-r : ℝ≥0) : ℝ))≤
      Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left (show ((t-r : ℝ≥0) : ℝ)≤T from by exact_mod_cast tsub_le_self.trans ht)
    have := GaussianLandscape.landscapeNorm_nonnegative N p J
    positivity
  calc
    _≤(‖b‖*(Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T)*‖v‖))/(Real.sqrt 2*(N : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact (norm_inner_le_norm (𝕜:=ℝ) _ _).trans
        (mul_le_mul_of_nonneg_left (hh.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))) (norm_nonneg _))
    _=_ := by ring

@[expose] def noiseRow (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (T t s r : ℝ≥0) (x b : State N) (j : Fin N) : ℝ :=
  fderiv ℝ (linearTest β R hR J t r b) x (noiseColumn x j)+
    fderiv ℝ (initialMean β R hR J T (t-r) (s-r)) x (noiseColumn x j)+
      (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-r) x) j/(Real.sqrt 2*(N : ℝ))

/-- The displayed noise row is the genuine derivative of the joint
state/Brownian predictor in its actual diffusion direction. -/
theorem predictor_joint_fderiv (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (T t s r : ℝ≥0) (hT : 0<T) (x b v w : State N) :
    fderiv ℝ (fun q : State N×State N => predictor β R hR J T t s r q.1 q.2) (x,b) (v,w)=
      fderiv ℝ (linearTest β R hR J t r b) x v+
        fderiv ℝ (initialMean β R hR J T (t-r) (s-r)) x v+
          ⟪w,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-r) x⟫_ℝ/(Real.sqrt 2*(N : ℝ)) := by
  have hm := (ActualSphereMeanSpatialC2.mean_contDiff_two (VectorBrownian.driver N) β J R hR (t-r)).differentiable (by norm_num)
  have hg : Differentiable ℝ (initialMean β R hR J T (t-r) (s-r)) :=
    (gammaMean_initial_contDiff_two β R hR J T (t-r) (s-r) hT).differentiable (by norm_num)
  have hl := ((hasFDerivAt_snd (𝕜:=ℝ) (p:=(x,b))).inner ℝ
    ((hm x).hasFDerivAt.comp (x,b) (hasFDerivAt_fst (𝕜:=ℝ) (p:=(x,b))))).const_mul ((Real.sqrt 2*(N : ℝ))⁻¹)
  have hga := (hg x).hasFDerivAt.comp (x,b) (hasFDerivAt_fst (𝕜:=ℝ) (p:=(x,b)))
  have hh := (hl.add hga).fderiv
  have hf : (fun q : State N×State N => (Real.sqrt 2*(N : ℝ))⁻¹*⟪q.2,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-r) q.1⟫_ℝ+
    initialMean β R hR J T (t-r) (s-r) q.1)=
    fun q => predictor β R hR J T t s r q.1 q.2 := by
    funext q
    unfold predictor initialMean
    rw [div_eq_mul_inv,mul_comm]
  change fderiv ℝ (fun q : State N×State N => (Real.sqrt 2*(N : ℝ))⁻¹*⟪q.2,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-r) q.1⟫_ℝ+
    initialMean β R hR J T (t-r) (s-r) q.1) (x,b)=_ at hh
  rw [hf] at hh
  rw [hh,linearTest_fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    smul_apply,smul_eq_mul,fderivInnerCLM_apply]
  simp only [show (ContinuousLinearMap.fst ℝ (State N) (State N)) (v,w)=v from rfl,
    show (ContinuousLinearMap.snd ℝ (State N) (State N)) (v,w)=w from rfl,Function.comp_apply]
  ring

theorem noiseRow_eq_joint_fderiv (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (T t s r : ℝ≥0) (hT : 0<T) (x b : State N) (j : Fin N) :
    noiseRow β R hR J T t s r x b j=
      fderiv ℝ (fun q : State N×State N => predictor β R hR J T t s r q.1 q.2) (x,b)
        (noiseColumn x j,basisVector j) := by
  rw [predictor_joint_fderiv β R hR J T t s r hT]
  simp only [noiseRow]
  rw [real_inner_comm,basis_inner]

theorem noiseRow_square_sum_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (T t s r : ℝ≥0) (ht : t≤T) (hT : 0<T) (x b : State N) (hx : OnSphere x) :
    (∑ j : Fin N,(noiseRow β R hR J T t s r x b j)^2)≤
      (3*‖b‖^2/(N : ℝ)^2+3*((s-r : ℝ≥0) : ℝ)/(N : ℝ))*
        Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T)+3/(2*(N : ℝ)) := by
  let A : ℝ := ‖b‖*Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T)/(Real.sqrt 2*(N : ℝ))
  let B : ℝ := tangentBound N p β T (s-r) J
  let a : Fin N→ℝ := fun j => fderiv ℝ (linearTest β R hR J t r b) x (noiseColumn x j)
  let c : Fin N→ℝ := fun j => fderiv ℝ (initialMean β R hR J T (t-r) (s-r)) x (noiseColumn x j)
  let d : Fin N→ℝ := fun j => (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-r) x) j/(Real.sqrt 2*(N : ℝ))
  have ha : (∑ j : Fin N,(a j)^2)≤2*A^2 :=
    noise_gradient_square_sum_le (by omega : N≠0) _ x hx A (by dsimp [A];positivity)
      (fun v => linearTest_projected_derivative hN hp β R hR hNR J T t r ht x b v hx)
  have hc : (∑ j : Fin N,(c j)^2)≤2*B^2 :=
    noise_gradient_square_sum_le (by omega : N≠0) _ x hx B (by dsimp [B,tangentBound];positivity)
      (fun v => initialMean_projected_derivative_norm hN hp β R hR hNR J x v hx T (t-r) (s-r) (tsub_le_self.trans ht) hT)
  have hd : (∑ j : Fin N,(d j)^2)≤1/(2*(N : ℝ)) := by
    dsimp only [d]
    simp_rw [div_pow]
    rw [←Finset.sum_div,coordinate_square_sum,real_inner_self_eq_norm_sq,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
    have hh := mean_norm_sq_le (by omega : N≠0) (VectorBrownian.driver N) β R hR hNR J (t-r) x hx
    calc
      _≤(N : ℝ)/(2*(N : ℝ)^2) := div_le_div_of_nonneg_right hh (by positivity)
      _=_ := by field_simp
  have hsum : (∑ j : Fin N,(noiseRow β R hR J T t s r x b j)^2)≤
      3*(∑ j : Fin N,(a j)^2)+3*(∑ j : Fin N,(c j)^2)+3*(∑ j : Fin N,(d j)^2) := by
    simp_rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    change (a j+c j+d j)^2≤3*(a j)^2+3*(c j)^2+3*(d j)^2
    nlinarith [sq_nonneg (a j-c j),sq_nonneg (a j-d j),sq_nonneg (c j-d j)]
  refine hsum.trans ((add_le_add (add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
    (mul_le_mul_of_nonneg_left hc (by norm_num))) (mul_le_mul_of_nonneg_left hd (by norm_num))).trans_eq ?_)
  dsimp only [A,B,tangentBound]
  rw [Real.sq_sqrt (by positivity : (0 : ℝ)≤((s-r : ℝ≥0) : ℝ)/(2*(N : ℝ))*Real.exp _)]
  simp only [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2),←Real.exp_nat_mul,Nat.cast_ofNat]
  rw [show (2 : ℝ)*(((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ))=
    (2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ) by ring]
  ring

/-- The true noise contraction is integrable along the physical path and
has a dimension-sharp expectation; no independence of X_r and B_r is used. -/
theorem actual_noiseRow_secondMoment (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    {Z0 : VectorBrownian.Space N → State N}
    (X : ℝ≥0 → VectorBrownian.Space N → State N)
    (hX : ∀ T,AnnealedSDECore.IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ u,OnSphere (X u ω))
    (T t s r : ℝ≥0) (ht : t≤T) (hT : 0<T) (hrs : r≤s) :
    Integrable (fun ω => ∑ j : Fin N,(noiseRow β R hR J T t s r (X r ω) (brownianVector r ω) j)^2)
      (VectorBrownian.law N) ∧
    (∫ ω,∑ j : Fin N,(noiseRow β R hR J T t s r (X r ω) (brownianVector r ω) j)^2 ∂VectorBrownian.law N)≤
      ((3*(s : ℝ))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T)+3/2)/(N : ℝ) := by
  let P := VectorBrownian.law N
  let E : ℝ := Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T)
  let f : VectorBrownian.Space N→ℝ := fun ω => ∑ j : Fin N,(noiseRow β R hR J T t s r (X r ω) (brownianVector r ω) j)^2
  let g : VectorBrownian.Space N→ℝ := fun ω =>
    (3*‖brownianVector r ω‖^2/(N : ℝ)^2+3*((s-r : ℝ≥0) : ℝ)/(N : ℝ))*E+3/(2*(N : ℝ))
  have hXi : StronglyMeasurable (X r) := ((hX 0).2.1 r).mono ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le r)
  have hBm : StronglyMeasurable (brownianVector (N:=N) r) := by
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).symm.continuous.measurable.comp
      (measurable_pi_iff.mpr (fun i => VectorBrownian.coordinate_measurable i r))).stronglyMeasurable
  have hfm : StronglyMeasurable f := by
    apply Finset.stronglyMeasurable_fun_sum
    intro j _
    unfold noiseRow
    have hl : Continuous (fun q : State N×State N => fderiv ℝ (linearTest β R hR J t r q.2) q.1 (noiseColumn q.1 j)) := by
      have he : (fun q : State N×State N => fderiv ℝ (linearTest β R hR J t r q.2) q.1 (noiseColumn q.1 j))=
        fun q => ⟪q.2,fderiv ℝ (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-r)) q.1 (noiseColumn q.1 j)⟫_ℝ/(Real.sqrt 2*(N : ℝ)) := by
          funext q;exact linearTest_fderiv β R hR J t r _ _ _
      rw [he]
      exact (continuous_snd.inner
        ((((ActualSphereMeanSpatialC2.mean_contDiff_two (VectorBrownian.driver N) β J R hR (t-r)).continuous_fderiv (by norm_num)).comp continuous_fst).clm_apply
          ((contDiff_noiseColumn j).continuous.comp continuous_fst))).div_const _
    have hg : Continuous (fun x : State N => fderiv ℝ (initialMean β R hR J T (t-r) (s-r)) x (noiseColumn x j)) :=
      ((gammaMean_initial_contDiff_two β R hR J T (t-r) (s-r) hT).continuous_fderiv (by norm_num)).clm_apply (contDiff_noiseColumn j).continuous
    have hm : Continuous (fun x : State N => (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-r) x) j/(Real.sqrt 2*(N : ℝ))) :=
      ((VariationalCoefficients.coordinate j).continuous.comp
        (ActualSphereMeanSpatialC2.mean_contDiff_two (VectorBrownian.driver N) β J R hR (t-r)).continuous).div_const _
    exact ((hl.comp_stronglyMeasurable (hXi.prodMk hBm)).add (hg.comp_stronglyMeasurable hXi) |>.add
      (hm.comp_stronglyMeasurable hXi)).pow 2
  have hgi : Integrable g P :=
    ((((brownianVector_memLp (N:=N) r (q:=2) (by norm_num)).integrable_norm_pow'.const_mul 3).div_const ((N : ℝ)^2)).add
      (integrable_const (3*((s-r : ℝ≥0) : ℝ)/(N : ℝ))) |>.mul_const E |>.add (integrable_const (3/(2*(N : ℝ)))))
  have hbound : ∀ᵐ ω ∂P,f ω≤g ω := hSphere.mono
    (fun ω h => noiseRow_square_sum_le hN hp β R hR hNR J T t s r ht hT (X r ω) (brownianVector r ω) (h r))
  have hfi : Integrable f P := hgi.mono' hfm.aestronglyMeasurable (hbound.mono (fun ω h => by
    change ‖f ω‖≤g ω
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact h))
  refine ⟨hfi,(integral_mono_ae hfi hgi hbound).trans_eq ?_⟩
  dsimp only [g]
  have hAi : Integrable (fun ω => 3*‖brownianVector r ω‖^2/(N : ℝ)^2) P :=
    ((brownianVector_memLp (N:=N) r (q:=2) (by norm_num)).integrable_norm_pow'.const_mul 3).div_const _
  have hbase : Integrable (fun ω => (3*‖brownianVector r ω‖^2/(N : ℝ)^2+3*((s-r : ℝ≥0) : ℝ)/(N : ℝ))*E) P :=
    (hAi.add (integrable_const _)).mul_const E
  rw [integral_add hbase (integrable_const _),integral_mul_const,
    integral_add hAi (integrable_const _),
    integral_div,integral_const_mul,brownianVector_secondMoment]
  simp only [integral_const,probReal_univ,one_smul]
  have hn : (N : ℝ)≠0 := (Nat.cast_pos.mpr (by omega : 0<N)).ne'
  have hs : ((s-r : ℝ≥0) : ℝ)=(s : ℝ)-r := NNReal.coe_sub hrs
  rw [hs]
  dsimp only [E]
  field_simp
  <;> ring

end SphericalAging.ActualGammaPredictorNoiseBounds
