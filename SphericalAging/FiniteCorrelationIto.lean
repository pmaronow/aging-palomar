module

public import SphericalAging.HamiltonianDerivativeCovariance
public import SphericalAging.RadialUniqueness
public import SphericalAging.BoundedItoMultiplier

public section

/-! Actual finite-N empirical correlation coefficients and full-filtration
martingale. The noise is constructed from the projected Brownian integrands,
and its dimension-dependent variance bound is proved by genuine Itô isometry.
These are prerequisites of the finite-N CK bridge, not a convergence theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.FiniteCorrelationIto
open HardSphereDynamics FiniteModel LandscapeDerivatives VectorIto
open FourPapersCommon.FilteredBrownian
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The actual empirical overlap. -/
@[expose] def overlap {N : ℕ} (x y : State N) : ℝ := inner ℝ x y / N

/-- The actual coefficient of coordinate Brownian noise in an overlap row. -/
@[expose] def correlationNoise {N : ℕ} (x y : State N) (j : Fin N) : ℝ :=
  Real.sqrt 2 / N * (projection x y) j

lemma sphere_norm {N : ℕ} {x : State N} (hx : OnSphere x) : ‖x‖ = Real.sqrt N := by
  have hs := (onSphere_iff_norm_sq x).mp hx
  rw [← hs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

lemma overlap_diag {N : ℕ} (hN : 0 < N) {x : State N} (hx : OnSphere x) :
    overlap x x = 1 := by
  rw [overlap,hx,div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))]

lemma overlap_abs_le_one {N : ℕ} (hN : 0 < N) {x y : State N}
    (hx : OnSphere x) (hy : OnSphere y) : |overlap x y| ≤ 1 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [overlap,abs_div,abs_of_pos hn,div_le_one hn]
  calc
    |inner ℝ x y| ≤ ‖x‖*‖y‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
    _ = N := by rw [sphere_norm hx,sphere_norm hy,← pow_two,Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Euler identity for the genuine Euclidean gradient of the ordered Hamiltonian. -/
theorem hamiltonianGradient_euler {N p : ℕ} (J : Disorder N p) (x : State N) :
    inner ℝ (hamiltonianGradient J x) x = (p : ℝ)*Hamiltonian N p J x := by
  rw [hamiltonianGradient,inner_gradient_left,(Hamiltonian_hasFDerivAt J x).fderiv]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,diagonalDerivative_apply]
  have hu (i : Fin p) : Function.update (fun _ => x) i x = fun _ => x := by
    ext j
    simp [Function.update_apply]
  simp_rw [hu]
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Hamiltonian_eq_diagonal]
  ring

/-- Exact overlap drift in the manuscript normalization, with the actual
Hamiltonian multiplier rather than a stipulated mean-field quantity. -/
theorem correlation_drift {N p : ℕ} (β : ℝ) (J : Disorder N p) (x y : State N) :
    inner ℝ (hamiltonianDrift β J x) y / N =
      β / N * inner ℝ (hamiltonianGradient J x) y -
        (kappa N + β*(p : ℝ)*Hamiltonian N p J x/N)*overlap x y := by
  unfold hamiltonianDrift drift projection overlap
  simp only [inner_sub_left,real_inner_smul_left]
  rw [real_inner_comm (hamiltonianGradient J x) x,hamiltonianGradient_euler]
  ring

/-- Exact coordinate contraction of the true projected diffusion matrix. -/
lemma correlationNoise_eq_inner {N : ℕ} (x y : State N) (j : Fin N) :
    correlationNoise x y j = inner ℝ (noiseColumn x j) y / N := by
  rw [correlationNoise,noiseColumn,real_inner_smul_left,projection_self_adjoint]
  rw [real_inner_comm (projection x y) (basisVector j),basis_inner]
  ring

lemma correlationNoise_continuous {N : ℕ} (j : Fin N) :
    Continuous (fun q : State N × State N => correlationNoise q.1 q.2 j) := by
  unfold correlationNoise projection
  fun_prop

lemma correlationNoise_sum_sq {N : ℕ} (x y : State N) :
    ∑ j : Fin N, correlationNoise x y j ^ 2 =
      2/(N : ℝ)^2*‖projection x y‖^2 := by
  simp only [correlationNoise,mul_pow,div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Finset.mul_sum,coordinate_square_sum,real_inner_self_eq_norm_sq]

/-- This `2/N` joint-coordinate bound is the source of the actual
finite-N correlation martingale estimate; no independence bound is assumed. -/
lemma correlationNoise_sum_sq_le {N : ℕ} (hN : 0 < N) {x y : State N}
    (hx : OnSphere x) (hy : OnSphere y) :
    ∑ j : Fin N, correlationNoise x y j ^ 2 ≤ 2/(N : ℝ) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [correlationNoise_sum_sq]
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (projection_norm_le_onSphere (Nat.ne_of_gt hN) x y hx)
  have hny := (onSphere_iff_norm_sq y).mp hy
  rw [hny] at hs
  calc
    _ ≤ 2/(N : ℝ)^2*N := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by field_simp

lemma correlationNoise_norm_le {N : ℕ} (hN : 0 < N) {x y : State N}
    (hx : OnSphere x) (hy : OnSphere y) (j : Fin N) :
    ‖correlationNoise x y j‖ ≤ Real.sqrt 2*Real.sqrt N/N := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [correlationNoise,norm_mul,Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hn.le)]
  have hb := (PiLp.norm_apply_le (projection x y) j).trans
    (projection_norm_le_onSphere (Nat.ne_of_gt hN) x y hx)
  rw [sphere_norm hy] at hb
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring)

section Process
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {X : ℝ≥0 → Ω → State N}

/-- The past sample is delayed until it is known; on the causal slice it
is exactly `X s`. This supplies genuine predictability. -/
@[expose] def noiseProcess (s : ℝ≥0) (j : Fin N) (t : ℝ≥0) (ω : Ω) : ℝ :=
  correlationNoise (X t ω) (X (min t s) ω) j

lemma noiseProcess_adapted (hXa : StronglyAdapted F X) (s : ℝ≥0) (j : Fin N) :
    StronglyAdapted F (noiseProcess (X := X) s j) := by
  intro t
  exact (correlationNoise_continuous j).comp_stronglyMeasurable
    ((hXa t).prodMk ((hXa (min t s)).mono (F.mono (min_le_left _ _))))

lemma noiseProcess_continuous
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω)) (s : ℝ≥0) (j : Fin N) :
    ∀ᵐ ω ∂P, Continuous (fun t => noiseProcess (X := X) s j t ω) := by
  filter_upwards [hXc] with ω hω
  exact (correlationNoise_continuous j).comp
    (hω.prodMk (hω.comp (continuous_id.min continuous_const)))

lemma noiseProcess_bound (hN : 0 < N)
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) (s : ℝ≥0) (j : Fin N) :
    ∀ᵐ ω ∂P, ∀ t, ‖noiseProcess (X := X) s j t ω‖ ≤ Real.sqrt 2*Real.sqrt N/N := by
  filter_upwards [hSphere] with ω hω
  intro t
  exact correlationNoise_norm_le hN (hω t) (hω (min t s)) j

@[expose] def noiseBound (N : ℕ) : ℝ≥0 := ⟨Real.sqrt 2*Real.sqrt N/N,by positivity⟩

/-- The constructed predictable class of the actual projected coefficient. -/
@[expose] def noiseClass (hN : 0 < N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) (s T : ℝ≥0) (j : Fin N) :
    PredictableProcessL2 F P := by
  let hm := RadialUniqueness.timeCut_memLp (noiseProcess (X := X) s j)
    (noiseProcess_adapted hXa s j) (noiseProcess_continuous hXc s j)
    (noiseBound N) (noiseProcess_bound hN hSphere s j) T
  exact ⟨hm.toLp _, (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F
    (noiseProcess (X := X) s j) (noiseProcess_adapted hXa s j)
    (noiseProcess_continuous hXc s j) T).congr hm.coeFn_toLp.symm⟩

lemma noiseClass_coeFn (hN : 0 < N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) (s T : ℝ≥0) (j : Fin N) :
    (noiseClass hN hXa hXc hSphere s T j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (noiseProcess (X := X) s j) T :=
  (RadialUniqueness.timeCut_memLp (noiseProcess (X := X) s j)
    (noiseProcess_adapted hXa s j) (noiseProcess_continuous hXc s j)
    (noiseBound N) (noiseProcess_bound hN hSphere s j) T).coeFn_toLp

/-- Actual noise integrands on the causal interval `(s,T]`. -/
@[expose] def rowNoise (hN : 0 < N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) (s T : ℝ≥0) (j : Fin N) :
    PredictableProcessL2 F P :=
  FourPapersCommon.FilteredBrownian.predictableTimeSlice F s T (noiseClass hN hXa hXc hSphere s T j)

lemma rowNoise_coeFn (hN : 0 < N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) {s T : ℝ≥0} (hsT : s ≤ T) (j : Fin N) :
    (rowNoise hN hXa hXc hSphere s T j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => if q.1 ∈ Ioc s T then correlationNoise (X q.1 q.2) (X s q.2) j else 0 := by
  let U := noiseClass hN hXa hXc hSphere s T j
  have hsub := Lp.coeFn_sub
    (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F T U : TimeProcessL2 P)
    (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s U : TimeProcessL2 P)
  filter_upwards [hsub,FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F T U,
    FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F s U,noiseClass_coeFn hN hXa hXc hSphere s T j]
    with q hsub hT hs hU
  change ((FourPapersCommon.FilteredBrownian.predictableTimeRestrict F T U : TimeProcessL2 P)-
    (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s U : TimeProcessL2 P)) q = _
  rw [hsub,Pi.sub_apply,hT,hs]
  change (U : TimeProcessL2 P) q = FourPapersCommon.continuousAdaptedTimeCut (noiseProcess (X := X) s j) T q at hU
  by_cases hqs : s < q.1
  · have hq0 : 0 < q.1 := (zero_le : 0 ≤ s).trans_lt hqs
    by_cases hqT : q.1 ≤ T
    · simp [FourPapersCommon.FilteredBrownian.predictableTimeFrame,hq0,hqT,
        not_le_of_gt hqs,hU,FourPapersCommon.continuousAdaptedTimeCut,noiseProcess,
        min_eq_right hqs.le,hqs]
    · simp [FourPapersCommon.FilteredBrownian.predictableTimeFrame,hq0,hqT,not_le_of_gt hqs]
  · have hqs' : q.1 ≤ s := le_of_not_gt hqs
    by_cases hq0 : 0 < q.1
    · simp [FourPapersCommon.FilteredBrownian.predictableTimeFrame,hq0,hqs',hqs'.trans hsT,hqs]
    · simp [FourPapersCommon.FilteredBrownian.predictableTimeFrame,hq0,hqs]

/-- The genuine scalar Itô integral of the overlap row coefficients. -/
@[expose] def rowMartingaleValue (D : BrownianDriver N P F) (hN : 0 < N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) (s T : ℝ≥0) : RandomL2 P :=
  vectorIto D (rowNoise hN hXa hXc hSphere s T)

/-- Zero mean is derived from the full-filtration constructed integral. -/
theorem rowMartingaleValue_mean_zero (D : BrownianDriver N P F) (hN : 0 < N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) (s T : ℝ≥0) :
    ∫ ω, (rowMartingaleValue D hN hXa hXc hSphere s T : Ω → ℝ) ω ∂P = 0 := by
  unfold rowMartingaleValue vectorIto
  rw [← generalExpectationMap_apply,map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [generalExpectationMap_apply]
  exact integral_naturalItoIntegral (D.filtered j).toIsPreBrownianReal
    (D.coordinateStronglyMeasurable j) (D.filtered j) _

/-- Exact finite-dimensional Itô isometry produces the sharp dimension
factor for the actual overlap noise, with no variance hypothesis. -/
theorem rowMartingaleValue_norm_sq_le (D : BrownianDriver N P F) (hN : 0 < N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) {s T : ℝ≥0} (hsT : s ≤ T) :
    ‖rowMartingaleValue D hN hXa hXc hSphere s T‖^2 ≤ 2*((T : ℝ)-s)/N := by
  let U := rowNoise hN hXa hXc hSphere s T
  let μ := nonnegativeLebesgueMeasure.prod P
  have hint (j : Fin N) : Integrable (fun q => (U j : TimeProcessL2 P) q ^ 2) μ :=
    (Lp.memLp (U j : TimeProcessL2 P)).integrable_sq
  have hall := ae_all_iff.mpr (fun j : Fin N => rowNoise_coeFn hN hXa hXc hSphere hsT j)
  have hpath := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hSphere
  let B : ℝ≥0 × Ω → ℝ := (Ioc s T ×ˢ (univ : Set Ω)).indicator (fun _ => 2/(N : ℝ))
  have hB : Integrable B μ := by
    apply memLp_one_iff_integrable.mp
    apply memLp_indicator_const 1 (measurableSet_Ioc.prod MeasurableSet.univ) (2/(N : ℝ))
    apply Or.inr
    change (nonnegativeLebesgueMeasure.prod P) (Ioc s T ×ˢ univ) ≠ ∞
    rw [Measure.prod_prod,measure_univ,mul_one]
    exact nonnegativeLebesgueMeasure_Ioc_ne_top s T
  have hBint : (∫ q, B q ∂μ) = 2*((T : ℝ)-s)/N := by
    change (∫ q, (Ioc s T ×ˢ (univ : Set Ω)).indicator (fun _ => 2/(N : ℝ)) q ∂nonnegativeLebesgueMeasure.prod P) = _
    rw [integral_indicator_const _ (measurableSet_Ioc.prod MeasurableSet.univ)]
    simp only [Measure.real_def,Measure.prod_prod,measure_univ,mul_one,
      nonnegativeLebesgueMeasure_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr (show (s : ℝ) ≤ T from hsT)),smul_eq_mul]
    ring
  change ‖vectorIto D U‖^2 ≤ _
  rw [norm_sq_vectorIto]
  simp_rw [RadialUniqueness.predictable_norm_sq]
  rw [← integral_finsetSum Finset.univ (fun j _ => hint j)]
  calc
    _ ≤ ∫ q, B q ∂μ := by
      apply integral_mono_ae (integrable_finsetSum Finset.univ (fun j _ => hint j)) hB
      filter_upwards [hall,hpath] with q hq hpath
      by_cases ht : q.1 ∈ Ioc s T
      · simp only [U,hq,ht,ite_true,B,indicator_of_mem (show q ∈ Ioc s T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩)]
        exact correlationNoise_sum_sq_le hN (hpath q.1) (hpath s)
      · simp only [U,hq,ht,ite_false,B,indicator_of_notMem (show q ∉ Ioc s T ×ˢ (univ : Set Ω) from fun h => ht h.1),zero_pow (by norm_num : 2≠0),Finset.sum_const_zero,le_refl]
    _ = _ := hBint

/-- Equivalent true second-moment estimate for the actual random variable. -/
theorem rowMartingaleValue_second_moment_le (D : BrownianDriver N P F) (hN : 0 < N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) {s T : ℝ≥0} (hsT : s ≤ T) :
    ∫ ω, (rowMartingaleValue D hN hXa hXc hSphere s T : Ω → ℝ) ω ^ 2 ∂P ≤
      2*((T : ℝ)-s)/N := by
  rw [PredictableItoTime.integral_sq_toLp _ (Lp.memLp _),Lp.toLp_coeFn]
  exact rowMartingaleValue_norm_sq_le D hN hXa hXc hSphere hsT

/-- Exact quantitative Chebyshev bound for the actual correlation noise. -/
theorem rowMartingaleValue_chebyshev (D : BrownianDriver N P F) (hN : 0 < N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) {s T : ℝ≥0} (hsT : s ≤ T)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(rowMartingaleValue D hN hXa hXc hSphere s T : Ω → ℝ) ω|} ≤
      ENNReal.ofReal (2*((T : ℝ)-s)/(N*ε^2)) := by
  let M := rowMartingaleValue D hN hXa hXc hSphere s T
  have hm : MemLp (M : Ω → ℝ) 2 P := Lp.memLp M
  have hzero : ∫ ω, (M : Ω → ℝ) ω ∂P = 0 := rowMartingaleValue_mean_zero D hN hXa hXc hSphere s T
  have hv : variance (M : Ω → ℝ) P ≤ 2*((T : ℝ)-s)/N := by
    rw [variance_eq_integral hm.aemeasurable,hzero]
    simp only [sub_zero]
    exact rowMartingaleValue_second_moment_le D hN hXa hXc hSphere hsT
  have hc := meas_ge_le_variance_div_sq hm hε
  simp only [hzero,sub_zero] at hc
  refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ (2*((T : ℝ)-s)/N)/ε^2 := div_le_div_of_nonneg_right hv (sq_nonneg ε)
    _ = _ := by ring

/-- The coefficients supply an actual martingale with a continuous version. -/
theorem exists_continuous_rowMartingale (D : BrownianDriver N P F) (hN : 0 < N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) (s T : ℝ≥0) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M F P ∧
      IsContinuousProcessModification (vectorProcess D (rowNoise hN hXa hXc hSphere s T)) M P :=
  exists_continuous_martingale_vectorProcess D _

end Process
end SphericalAging.FiniteCorrelationIto
