module

public import SphericalAging.EnergyCovarianceContraction
public import SphericalAging.TwoTimeResponseMoments
public import Mathlib.Algebra.Order.Chebyshev

public section

/-! Finite-N energy contraction of a genuine L² terminal response matrix.
The sample matrix is assembled from its actual finite basis columns. The
normalized trace has a dimension-free fourth moment, while the rank-one
correction vanishes by column moments alone. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators InnerProductSpace NNReal ENNReal
namespace SphericalAging.ResponseMatrixEnergyContraction
open HardSphereDynamics FiniteModel EnergyCovarianceContraction
open FiniteCorrelationIto
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- The actual finite matrix of representatives of the terminal response. -/
@[expose] def sampleMatrix (M : State N →L[ℝ] Lp (State N) 2 P) (ω : Ω) :
    State N →L[ℝ] State N :=
  ∑ i : Fin N,(VariationalCoefficients.coordinate i).smulRight ((M (basisVector i)) ω)

lemma sampleMatrix_apply (M : State N →L[ℝ] Lp (State N) 2 P) (ω : Ω) (v : State N) :
    sampleMatrix M ω v = ∑ i : Fin N,v i • ((M (basisVector i)) ω) := by
  simp [sampleMatrix,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply]

lemma sampleMatrix_basis (M : State N →L[ℝ] Lp (State N) 2 P) (ω : Ω) (i : Fin N) :
    sampleMatrix M ω (basisVector i) = (M (basisVector i)) ω := by
  rw [sampleMatrix_apply]
  simp [basisVector,PiLp.single_apply]

/-- Every fixed direction of the finite sample matrix represents the
original continuous linear response operator. -/
lemma sampleMatrix_ae (M : State N →L[ℝ] Lp (State N) 2 P) (v : State N) :
    (fun ω => sampleMatrix M ω v) =ᵐ[P] (M v : Ω → State N) := by
  have he : M v = ∑ i : Fin N,v i • M (basisVector i) := by
    conv_lhs => rw [← LocalSDE.state_sum_basis v]
    rw [map_sum]
    simp only [map_smul]
  rw [he]
  have hs := Lp.coeFn_finsetSum Finset.univ (fun i : Fin N => v i • M (basisVector i))
  have hm := ae_all_iff.mpr (fun i : Fin N => Lp.coeFn_smul (v i) (M (basisVector i)))
  filter_upwards [hs,hm] with ω hsum hsmul
  rw [sampleMatrix_apply,hsum]
  simp only [Finset.sum_apply,Pi.smul_apply]
  exact Finset.sum_congr rfl (fun i _ => (hsmul i).symm)

@[expose] def sampleTrace (M : State N →L[ℝ] Lp (State N) 2 P) (ω : Ω) : ℝ :=
  (∑ i : Fin N,inner ℝ (basisVector i) ((M (basisVector i)) ω))/(N : ℝ)

lemma sampleTrace_eq (M : State N →L[ℝ] Lp (State N) 2 P) (ω : Ω) :
    sampleTrace M ω = EnergyCovarianceContraction.normalizedTrace (sampleMatrix M ω) := by
  unfold sampleTrace EnergyCovarianceContraction.normalizedTrace
  rw [HamiltonianDerivativeCovariance.operatorTrace,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin N) ℝ)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hb : EuclideanSpace.basisFun (Fin N) ℝ i = basisVector i :=
    EuclideanSpace.basisFun_apply (Fin N) ℝ i
  rw [hb]
  exact congrArg (inner ℝ (basisVector i)) (sampleMatrix_basis M ω i).symm

lemma normalizedTrace_fourth_le_columns (hN : 0 < N)
    (U : State N →L[ℝ] State N) :
    |EnergyCovarianceContraction.normalizedTrace U|^4 ≤
      (∑ i : Fin N,‖U (basisVector i)‖^4)/(N : ℝ) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have htrace : |HamiltonianDerivativeCovariance.operatorTrace U| ≤
      ∑ i : Fin N,‖U (basisVector i)‖ := by
    rw [HamiltonianDerivativeCovariance.operatorTrace,
      LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin N) ℝ)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    have hb : EuclideanSpace.basisFun (Fin N) ℝ i = basisVector i :=
      EuclideanSpace.basisFun_apply (Fin N) ℝ i
    rw [hb]
    simpa [basisVector] using norm_inner_le_norm (𝕜 := ℝ) (basisVector i) (U (basisVector i))
  have hpow := pow_sum_le_card_mul_sum_pow (s := Finset.univ)
    (f := fun i : Fin N => ‖U (basisVector i)‖) (fun i _ => norm_nonneg _) 3
  simp only [Finset.sum_const_zero,Finset.card_univ,Fintype.card_fin] at hpow
  rw [EnergyCovarianceContraction.normalizedTrace,abs_div,abs_of_pos hn,div_pow]
  apply (div_le_div_iff₀ (pow_pos hn 4) hn).mpr
  have hh := pow_le_pow_left₀ (abs_nonneg _) htrace 4
  calc
    |HamiltonianDerivativeCovariance.operatorTrace U|^4*(N : ℝ) ≤
        (∑ i : Fin N,‖U (basisVector i)‖)^4*(N : ℝ) := mul_le_mul_of_nonneg_right hh hn.le
    _ ≤ ((N : ℝ)^3*(∑ i : Fin N,‖U (basisVector i)‖^4))*(N : ℝ) :=
      mul_le_mul_of_nonneg_right hpow hn.le
    _ = _ := by ring

/-- Exact ordered coupling-gradient contraction with the actual sample
matrix, including the trace and overlap correction. -/
theorem actual_normalized_contraction (hN : 0 < N) (hp : 2 ≤ p)
    (M : State N →L[ℝ] Lp (State N) 2 P) (x y : State N) (ω : Ω) :
    (∑ I : TensorIndex N p,inner ℝ (gradient
      (GaussianIntegrationByParts.hamiltonianCoefficient I) x)
      (sampleMatrix M ω (gradient
        (GaussianIntegrationByParts.hamiltonianCoefficient I) y)))/(N : ℝ) =
      (p : ℝ)*(FiniteCorrelationIto.overlap x y)^(p-1)*sampleTrace M ω+
        energyCorrection (p := p) x y (sampleMatrix M ω) := by
  rw [normalized_contraction_eq hN hp,sampleTrace_eq]

theorem sampleTrace_fourthMoment (hN : 0 < N)
    (M : State N →L[ℝ] Lp (State N) 2 P) (B : ℝ)
    (hM : ∀ i : Fin N,MemLp (M (basisVector i) : Ω → State N) 4 P)
    (hB : ∀ i : Fin N,(∫ ω,‖(M (basisVector i)) ω‖^4 ∂P) ≤ B) :
    Integrable (fun ω => |sampleTrace M ω|^4) P ∧
      (∫ ω,|sampleTrace M ω|^4 ∂P) ≤ B := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmaj : Integrable (fun ω => (∑ i : Fin N,‖(M (basisVector i)) ω‖^4)/(N : ℝ)) P :=
    (integrable_finsetSum Finset.univ (fun i _ => (hM i).integrable_norm_pow')).div_const _
  have hs : AEStronglyMeasurable (fun ω => ∑ i : Fin N,inner ℝ (basisVector i) ((M (basisVector i)) ω)) P := by
    have h := Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => (innerSL ℝ (basisVector i)).continuous.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable (M (basisVector i))))
    convert h using 1
    funext ω
    simp only [Finset.sum_apply,innerSL_apply_apply]
  have hsm : AEStronglyMeasurable (sampleTrace M) P := by
    change AEStronglyMeasurable (fun ω => (∑ i : Fin N,inner ℝ (basisVector i) ((M (basisVector i)) ω))/(N : ℝ)) P
    simpa only [div_eq_mul_inv] using hs.mul_const (N : ℝ)⁻¹
  have hle : ∀ ω,|sampleTrace M ω|^4 ≤ (∑ i : Fin N,‖(M (basisVector i)) ω‖^4)/(N : ℝ) := by
    intro ω
    rw [sampleTrace_eq]
    simpa only [sampleMatrix_basis] using normalizedTrace_fourth_le_columns hN (sampleMatrix M ω)
  have hi : Integrable (fun ω => |sampleTrace M ω|^4) P :=
    hmaj.mono' (hsm.norm.pow 4) (ae_of_all _ (fun ω => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ |sampleTrace M ω|^4)] using hle ω))
  refine ⟨hi,(integral_mono_ae hi hmaj (ae_of_all _ hle)).trans ?_⟩
  rw [integral_div,integral_finsetSum _ (fun i _ => (hM i).integrable_norm_pow')]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ _i : Fin N,B := Finset.sum_le_sum (fun i _ => hB i)
    _ = _ := by simp;ring

/-- The sample operator satisfies the finite-column Hilbert--Schmidt
bound, proved directly from its basis expansion. -/
lemma sampleMatrix_apply_norm_sq_le (M : State N →L[ℝ] Lp (State N) 2 P) (ω : Ω) (v : State N) :
    ‖sampleMatrix M ω v‖^2 ≤ ‖v‖^2*(∑ i : Fin N,‖(M (basisVector i)) ω‖^2) := by
  rw [sampleMatrix_apply]
  have hn := norm_sum_le Finset.univ (fun i : Fin N => v i • ((M (basisVector i)) ω))
  simp only [norm_smul,Real.norm_eq_abs] at hn
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin N => |v i|) (fun i : Fin N => ‖(M (basisVector i)) ω‖)
  simp only [sq_abs,coordinate_square_sum,real_inner_self_eq_norm_sq] at hc
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc

lemma sphere_sample_pairing_sq_le (M : State N →L[ℝ] Lp (State N) 2 P) (ω : Ω)
    {x y : State N} (hx : OnSphere x) (hy : OnSphere y) :
    (inner ℝ y (sampleMatrix M ω x))^2 ≤
      (N : ℝ)^2*(∑ i : Fin N,‖(M (basisVector i)) ω‖^2) := by
  have hinner := pow_le_pow_left₀ (abs_nonneg _) (norm_inner_le_norm (𝕜 := ℝ) y (sampleMatrix M ω x)) 2
  simp only [Real.norm_eq_abs,sq_abs,mul_pow] at hinner
  have hu := mul_le_mul_of_nonneg_left (sampleMatrix_apply_norm_sq_le M ω x) (sq_nonneg ‖y‖)
  rw [(onSphere_iff_norm_sq x).mp hx,(onSphere_iff_norm_sq y).mp hy] at hu
  calc
    _ ≤ ‖y‖^2*‖sampleMatrix M ω x‖^2 := hinner
    _ ≤ (N : ℝ)*((N : ℝ)*(∑ i : Fin N,‖(M (basisVector i)) ω‖^2)) := by
      simpa only [(onSphere_iff_norm_sq y).mp hy] using hu
    _ = _ := by ring

/-- The rank-one correction is controlled by the actual columns. This
yields a vanishing error without assuming a sample operator-norm bound. -/
lemma energyCorrection_sq_le_columns (hN : 0<N) (hp : 2≤p)
    (M : State N →L[ℝ] Lp (State N) 2 P) (ω : Ω)
    {x y : State N} (hx : OnSphere x) (hy : OnSphere y) :
    (energyCorrection (p := p) x y (sampleMatrix M ω))^2 ≤
      ((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ)^2)*
        (∑ i : Fin N,‖(M (basisVector i)) ω‖^2) := by
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hp1 : (1 : ℝ)≤p := by exact_mod_cast (show 1≤p from by omega)
  have hpm : 0≤(p : ℝ)-1 := by linarith
  have hK : 0≤(p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2 := by positivity
  have hc : |overlap x y|^(p-2)≤1 := pow_le_one₀ (abs_nonneg _) (overlap_abs_le_one hN hx hy)
  have ha : |energyCorrection (p := p) x y (sampleMatrix M ω)| ≤
      ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)*|inner ℝ y (sampleMatrix M ω x)| := by
    rw [energyCorrection,abs_mul,abs_mul,abs_of_nonneg hK,abs_pow]
    simpa only [mul_one] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc hK) (abs_nonneg _)
  have hs := pow_le_pow_left₀ (abs_nonneg _) ha 2
  simp only [sq_abs,mul_pow] at hs
  calc
    _ ≤ ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)^2*(inner ℝ y (sampleMatrix M ω x))^2 := hs
    _ ≤ ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)^2*
        ((N : ℝ)^2*(∑ i : Fin N,‖(M (basisVector i)) ω‖^2)) :=
      mul_le_mul_of_nonneg_left (sphere_sample_pairing_sq_le M ω hx hy) (sq_nonneg _)
    _ = _ := by field_simp <;> ring

lemma sampleMatrix_aestronglyMeasurable (M : State N →L[ℝ] Lp (State N) 2 P) :
    AEStronglyMeasurable (sampleMatrix M) P := by
  have h := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
    (ContinuousLinearMap.smulRightL ℝ (State N) (State N) (VariationalCoefficients.coordinate i)).continuous.comp_aestronglyMeasurable
      (Lp.memLp (M (basisVector i))).aestronglyMeasurable)
  convert h using 1
  funext ω
  ext v
  simp only [sampleMatrix,Finset.sum_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.smulRightL_apply_apply]

lemma energyCorrection_aestronglyMeasurable (M : State N →L[ℝ] Lp (State N) 2 P)
    {x y : Ω → State N} (hx : AEStronglyMeasurable x P) (hy : AEStronglyMeasurable y P) :
    AEStronglyMeasurable (fun ω => energyCorrection (p := p) (x ω) (y ω) (sampleMatrix M ω)) P := by
  have hu : AEStronglyMeasurable (fun ω => sampleMatrix M ω (x ω)) P :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((sampleMatrix_aestronglyMeasurable M).prodMk hx)
  have hov : AEStronglyMeasurable (fun ω => overlap (x ω) (y ω)) P := by
    simpa only [overlap,div_eq_mul_inv] using (hx.inner hy).mul_const (N : ℝ)⁻¹
  have h := ((hov.pow (p-2)).mul (hy.inner hu)).const_mul
    ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)
  simpa only [energyCorrection,mul_assoc,Pi.mul_apply,Pi.pow_apply] using h

lemma column_secondMoment_le (M : State N →L[ℝ] Lp (State N) 2 P) (C : ℝ)
    (hm : ∀ i : Fin N,MemLp (M (basisVector i) : Ω → State N) 4 P)
    (hb : ∀ i : Fin N,(∫ ω,‖(M (basisVector i)) ω‖^4 ∂P)≤C) (i : Fin N) :
    (∫ ω,‖(M (basisVector i)) ω‖^2 ∂P)≤1+C := by
  calc
    _ ≤ ∫ ω,1+‖(M (basisVector i)) ω‖^4 ∂P := integral_mono_ae
      (Lp.memLp (M (basisVector i))).integrable_norm_pow'
      ((integrable_const 1).add (hm i).integrable_norm_pow')
      (ae_of_all P (fun ω => by nlinarith [sq_nonneg (‖(M (basisVector i)) ω‖^2-1)]))
    _ = 1+(∫ ω,‖(M (basisVector i)) ω‖^4 ∂P) := by
      rw [integral_add (integrable_const 1) (hm i).integrable_norm_pow'];simp
    _ ≤ 1+C := add_le_add_right (hb i) 1

theorem energyCorrection_secondMoment (hN : 0<N) (hp : 2≤p)
    (M : State N →L[ℝ] Lp (State N) 2 P) (C : ℝ)
    (hm : ∀ i : Fin N,MemLp (M (basisVector i) : Ω → State N) 4 P)
    (hb : ∀ i : Fin N,(∫ ω,‖(M (basisVector i)) ω‖^4 ∂P)≤C)
    {x y : Ω → State N} (hxm : AEStronglyMeasurable x P) (hym : AEStronglyMeasurable y P)
    (hx : ∀ᵐ ω ∂P,OnSphere (x ω)) (hy : ∀ᵐ ω ∂P,OnSphere (y ω)) :
    MemLp (fun ω => energyCorrection (p := p) (x ω) (y ω) (sampleMatrix M ω)) 2 P ∧
    (∫ ω,(energyCorrection (p := p) (x ω) (y ω) (sampleMatrix M ω))^2 ∂P)≤
      ((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+C) := by
  let K : ℝ := (p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ)^2
  have hK : 0≤K := by dsimp [K];positivity
  have hbound : ∀ᵐ ω ∂P,(energyCorrection (p := p) (x ω) (y ω) (sampleMatrix M ω))^2≤
      K*(∑ i : Fin N,‖(M (basisVector i)) ω‖^2) := by
    filter_upwards [hx,hy] with ω hxx hyy
    exact energyCorrection_sq_le_columns hN hp M ω hxx hyy
  have hi : Integrable (fun ω => K*(∑ i : Fin N,‖(M (basisVector i)) ω‖^2)) P := (integrable_finsetSum Finset.univ
    (fun i _ => (Lp.memLp (M (basisVector i))).integrable_norm_pow')).const_mul K
  have hmeas := energyCorrection_aestronglyMeasurable (p := p) M hxm hym
  have hisq : Integrable (fun ω => (energyCorrection (p := p) (x ω) (y ω) (sampleMatrix M ω))^2) P :=
    hi.mono' (hmeas.pow 2) (hbound.mono (fun ω hw => by simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using hw))
  refine ⟨(memLp_two_iff_integrable_sq hmeas).mpr hisq,?_⟩
  calc
    _ ≤ ∫ ω,K*(∑ i : Fin N,‖(M (basisVector i)) ω‖^2) ∂P := integral_mono_ae hisq hi hbound
    _ = K*(∑ i : Fin N,∫ ω,‖(M (basisVector i)) ω‖^2 ∂P) := by
      rw [integral_const_mul,integral_finsetSum Finset.univ
        (fun i _ => (Lp.memLp (M (basisVector i))).integrable_norm_pow')]
    _ ≤ K*(∑ _i : Fin N,(1+C)) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => column_secondMoment_le M C hm hb i)) hK
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      dsimp [K]
      field_simp [ne_of_gt (Nat.cast_pos.mpr hN : (0 : ℝ)<N)] <;> ring


lemma sampleTrace_memLp_fourth (M : State N →L[ℝ] Lp (State N) 2 P)
    (hm : ∀ i : Fin N,MemLp (M (basisVector i) : Ω → State N) 4 P) :
    MemLp (sampleTrace M) 4 P := by
  have hs := memLp_finsetSum Finset.univ (fun i _ =>
    (hm i).continuousLinearMap_comp (innerSL ℝ (basisVector i)))
  change MemLp (fun ω => (∑ i : Fin N,inner ℝ (basisVector i) ((M (basisVector i)) ω))/(N : ℝ)) 4 P
  simpa only [div_eq_mul_inv,innerSL_apply_apply] using hs.mul_const (N : ℝ)⁻¹

lemma integral_abs_le_sqrt_secondMoment {f : Ω → ℝ} (hf : MemLp f 2 P) :
    (∫ ω,|f ω| ∂P)≤Real.sqrt (∫ ω,(f ω)^2 ∂P) := by
  have hc : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have h := integral_mul_norm_le_Lp_mul_Lq hc (by simpa using hf)
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 P))
  simpa [Real.norm_eq_abs,Real.rpow_two,sq_abs,Real.sqrt_eq_rpow,one_div] using h

/-- The dimension-uniform physical fourth-moment constant has only a
linear dependence on the actual Gaussian landscape norm in its exponent. -/
@[expose] def uniformFourthConstant (p : ℕ) (β : ℝ≥0) (J : Disorder N p) (t : ℝ≥0) : ℝ :=
  Real.exp (54*(t : ℝ)+(4*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(t : ℝ))*GaussianLandscape.landscapeNorm N p J)

lemma physicalFourthConstant_le (hN : 0<N) (β : ℝ≥0) (J : Disorder N p) (t : ℝ≥0) :
    Real.exp (((4*PhysicalVariationalMoments.physicalDriftBound p β J+2+
      6*PhysicalVariationalMoments.physicalNoiseTraceBound N : ℝ≥0) : ℝ)*(t : ℝ))≤
      uniformFourthConstant p β J t := by
  apply Real.exp_le_exp.mpr
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have h1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hdiv : 8/(N : ℝ)≤8 := (div_le_iff₀ hn).mpr (by linarith)
  change (4*(1+(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*GaussianLandscape.landscapeNorm N p J)+2+
    6*(8/(N : ℝ)))*(t : ℝ)≤_
  nlinarith [mul_le_mul_of_nonneg_right hdiv t.coe_nonneg]

variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
open StochasticCalculus TwoTimeResponseMatrix

/-- Actual two-time response receipt for the finite-N energy bridge.
All column moments are derived from the genuine physical variational
SDE; there is no response moment or Duhamel identity among the premises. -/
theorem actual_response_contraction_moments (hN : 0<N) (hp : 2≤p)
    (D : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun t => X t ω))
    {Kb Ks : ℝ≥0} (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (s T : ℝ≥0) (hSphere : ∀ᵐ ω ∂P,OnSphere (X s ω))
    (hSpherePath : ∀ᵐ ω ∂P,∀ t,t≤s+T → OnSphere (X t ω))
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t≤T) :
    let M := terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s T hSphere t
    let C := uniformFourthConstant p β J t
    MemLp (sampleTrace M) 4 P ∧ (∫ ω,|sampleTrace M ω|^4 ∂P)≤C ∧
    MemLp (fun ω => energyCorrection (p := p) (X (s+t) ω) (X s ω) (sampleMatrix M ω)) 2 P ∧
    (∫ ω,(energyCorrection (p := p) (X (s+t) ω) (X s ω) (sampleMatrix M ω))^2 ∂P)≤
      ((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+C) ∧
    (∫ ω,|energyCorrection (p := p) (X (s+t) ω) (X s ω) (sampleMatrix M ω)| ∂P)≤
      Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+C)) := by
  dsimp only
  let M := terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s T hSphere t
  let C := uniformFourthConstant p β J t
  have hh (i : Fin N) := TwoTimeResponseMoments.terminal_direction_fourthMoment hN hp D β R hR hNR J
    X hXa hXc hb hs s T hSphere hSpherePath hnull t ht (basisVector i)
  have hm (i : Fin N) : MemLp (M (basisVector i) : Ω → State N) 4 P := (hh i).1
  have hbound (i : Fin N) : (∫ ω,‖(M (basisVector i)) ω‖^4 ∂P)≤C := by
    exact (hh i).2.trans (by simpa [basisVector] using physicalFourthConstant_le hN β J t)
  have htrace := sampleTrace_fourthMoment hN M C hm hbound
  have hx : ∀ᵐ ω ∂P,OnSphere (X (s+t) ω) := hSpherePath.mono
    (fun ω hw => hw (s+t) (add_le_add le_rfl ht))
  have hxm : AEStronglyMeasurable (X (s+t)) P :=
    ((hXa (s+t)).mono (F.le _)).aestronglyMeasurable
  have hym : AEStronglyMeasurable (X s) P := ((hXa s).mono (F.le _)).aestronglyMeasurable
  have he := energyCorrection_secondMoment hN hp M C hm hbound hxm hym hx hSphere
  refine ⟨sampleTrace_memLp_fourth M hm,htrace.2,he.1,he.2,?_⟩
  exact (integral_abs_le_sqrt_secondMoment he.1).trans (Real.sqrt_le_sqrt he.2)

end SphericalAging.ResponseMatrixEnergyContraction
