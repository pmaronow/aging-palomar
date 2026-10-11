module

public import SphericalAging.FiniteCorrelationIto
public import SphericalAging.RandomInitialSDE
public import SphericalAging.CutoffSphere

public section

/-! Derivation of the actual empirical correlation integral equation from
the genuine finite-dimensional strong SDE, including its constructed
full-filtration matrix Itô integrals. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.FiniteCorrelationEquation
open HardSphereDynamics FiniteModel FiniteCorrelationIto LocalSDE VectorIto
open FourPapersCommon.FilteredBrownian
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {X : ℝ≥0 → Ω → State N}

lemma matrixNoise_memLp (hN : 0 < N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) (T : ℝ≥0) (i j : Fin N) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun t ω => noiseColumn (X t ω) j i) T)
      2 (nonnegativeLebesgueMeasure.prod P) := by
  apply RadialUniqueness.timeCut_memLp
    (fun t ω => noiseColumn (X t ω) j i)
    (fun t => (continuous_noiseCoordinate i j).comp_stronglyMeasurable (hXa t))
    (hXc.mono (fun ω hω => (continuous_noiseCoordinate i j).comp hω))
    ⟨Real.sqrt 2,Real.sqrt_nonneg _⟩
  filter_upwards [hSphere] with ω hω
  intro t
  exact noiseCoordinate_norm_le_onSphere (Nat.ne_of_gt hN) _ (hω t) i j

/-- Canonical actual projected matrix coefficient; proof arguments only
certify genuine predictability and integrability of the displayed function. -/
@[expose] def matrixNoiseClass (hN : 0 < N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) (T : ℝ≥0) (i j : Fin N) :
    PredictableProcessL2 F P :=
  coefficientPredictableActual hXa hXc (continuous_noiseCoordinate i j) T
    (matrixNoise_memLp hN hXa hXc hSphere T i j)

lemma matrixNoiseClass_coeFn (hN : 0 < N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) (T : ℝ≥0) (i j : Fin N) :
    (matrixNoiseClass hN hXa hXc hSphere T i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun t ω => noiseColumn (X t ω) j i) T :=
  (matrixNoise_memLp hN hXa hXc hSphere T i j).coeFn_toLp

@[expose] def coordinateNoiseValue (D : BrownianDriver N P F) (hN : 0 < N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) (T : ℝ≥0) (i : Fin N) : RandomL2 P :=
  driverItoMap D (matrixNoiseClass hN hXa hXc hSphere T i)

/-- The faithful random-initial SDE equation uses exactly the canonical
actual matrix integrals, irrespective of the certificates in its definition. -/
lemma physical_coordinate_equation (D : BrownianDriver N P F) (hN : 0 < N)
    (β : ℝ) (J : Disorder N p) (Z0 : Ω → State N) (T : ℝ≥0)
    (hsol : RandomInitialSDE.IsStrongSolutionOn (fun i x => hamiltonianDrift β J x i)
      (fun i j x => noiseColumn x j i) continuous_noiseCoordinate D Z0 X T)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) {t : ℝ≥0} (ht : t ≤ T) (i : Fin N) :
    ∀ᵐ ω ∂P, X t ω i = Z0 ω i+
      (∫ u in (0 : ℝ)..(t : ℝ), hamiltonianDrift β J (X u.toNNReal ω) i)+
        (coordinateNoiseValue D hN hXa hXc hSphere t i : Ω → ℝ) ω := by
  obtain ⟨hXa',hXc',hbm,hsm,heq⟩ := hsol
  exact heq t ht i

/-- Coordinate form of the genuine finite-dimensional inner product. -/
lemma overlap_eq_sum (x y : State N) : overlap x y=∑ i : Fin N, y i/N*x i := by
  simp only [overlap,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,
    Finset.sum_div,mul_div_assoc]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The coordinate noise expression obtained directly from the strong SDE. -/
@[expose] def coordinateCorrelationNoise (D : BrownianDriver N P F) (hN : 0 < N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) (s t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin N, (X s ω i/N)*
    ((coordinateNoiseValue D hN hXa hXc hSphere t i : Ω → ℝ) ω-
      (coordinateNoiseValue D hN hXa hXc hSphere s i : Ω → ℝ) ω)

/-- Exact empirical correlation equation before pulling the past sample
through the stochastic integral. Every noise term is an actual Itô operator. -/
theorem correlation_equation_coordinates (D : BrownianDriver N P F) (hN : 0 < N)
    (β : ℝ) (J : Disorder N p) (Z0 : Ω → State N) (T : ℝ≥0)
    (hsol : RandomInitialSDE.IsStrongSolutionOn (fun i x => hamiltonianDrift β J x i)
      (fun i j x => noiseColumn x j i) continuous_noiseCoordinate D Z0 X T)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) :
    ∀ᵐ ω ∂P, overlap (X t ω) (X s ω) = 1+
      (∫ u in (s : ℝ)..(t : ℝ), inner ℝ (hamiltonianDrift β J (X u.toNNReal ω)) (X s ω)/N)+
      coordinateCorrelationNoise D hN hXa hXc hSphere s t ω := by
  have het := ae_all_iff.mpr (fun i => physical_coordinate_equation D hN β J Z0 T hsol hXa hXc hSphere ht i)
  have hes := ae_all_iff.mpr (fun i => physical_coordinate_equation D hN β J Z0 T hsol hXa hXc hSphere (hst.trans ht) i)
  filter_upwards [het,hes,hXc,hSphere] with ω het hes hc hsp
  have hfc (i : Fin N) : Continuous (fun u : ℝ => hamiltonianDrift β J (X u.toNNReal ω) i) := by
    exact ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp
      (contDiff_hamiltonianDrift β J).continuous).comp (hc.comp continuous_real_toNNReal)
  have he (i : Fin N) : X t ω i=X s ω i+
      (∫ u in (s : ℝ)..(t : ℝ), hamiltonianDrift β J (X u.toNNReal ω) i)+
      ((coordinateNoiseValue D hN hXa hXc hSphere t i : Ω → ℝ) ω-
        (coordinateNoiseValue D hN hXa hXc hSphere s i : Ω → ℝ) ω) := by
    have hi := intervalIntegral.integral_interval_sub_left
      ((hfc i).intervalIntegrable (μ := volume) (0 : ℝ) (t : ℝ)) ((hfc i).intervalIntegrable (μ := volume) (0 : ℝ) (s : ℝ))
    linarith [het i,hes i]
  have hd : (∫ u in (s : ℝ)..(t : ℝ), inner ℝ (hamiltonianDrift β J (X u.toNNReal ω)) (X s ω)/N) =
      ∑ i : Fin N, (X s ω i/N)*(∫ u in (s : ℝ)..(t : ℝ), hamiltonianDrift β J (X u.toNNReal ω) i) := by
    change (∫ u in (s : ℝ)..(t : ℝ), overlap (hamiltonianDrift β J (X u.toNNReal ω)) (X s ω)) = _
    simp_rw [overlap_eq_sum]
    rw [intervalIntegral.integral_finsetSum (fun i _ => ((hfc i).intervalIntegrable (μ := volume) (s : ℝ) (t : ℝ)).const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  rw [hd,overlap_eq_sum]
  simp_rw [he,mul_add]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  have hdiag : (∑ i : Fin N, X s ω i/N*X s ω i)=1 :=
    (overlap_eq_sum _ _).symm.trans (overlap_diag hN (hsp s))
  rw [hdiag]
  rfl

/-- An everywhere bounded representative of the actual past coordinate.
It agrees with `X_s/N` on the proved sphere path event. -/
@[expose] def pastCoordinate (s : ℝ≥0) (i : Fin N) (ω : Ω) : ℝ :=
  max (-Real.sqrt N) (min (Real.sqrt N) (X s ω i))/N

lemma pastCoordinate_measurable (hXa : StronglyAdapted F X) (s : ℝ≥0) (i : Fin N) :
    StronglyMeasurable[F s] (pastCoordinate (X := X) s i) := by
  have hc : Continuous (fun z : ℝ => max (-Real.sqrt N) (min (Real.sqrt N) z)/N) := by fun_prop
  exact hc.comp_stronglyMeasurable ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp_stronglyMeasurable (hXa s))

lemma pastCoordinate_bound (hN : 0 < N) (s : ℝ≥0) (i : Fin N) (ω : Ω) :
    ‖pastCoordinate (X := X) s i ω‖ ≤ Real.sqrt N/N := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [pastCoordinate,Real.norm_eq_abs,abs_div,abs_of_pos hn]
  apply div_le_div_of_nonneg_right _ hn.le
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith [Real.sqrt_nonneg (N : ℝ)]) (min_le_left _ _)

lemma pastCoordinate_eq (hN : 0 < N) (s : ℝ≥0) (i : Fin N) {ω : Ω}
    (hSphere : OnSphere (X s ω)) : pastCoordinate (X := X) s i ω=X s ω i/N := by
  have hb : ‖X s ω i‖ ≤ Real.sqrt N := (PiLp.norm_apply_le _ i).trans_eq (sphere_norm hSphere)
  rw [Real.norm_eq_abs] at hb
  have ha := abs_le.mp hb
  rw [pastCoordinate,min_eq_right ha.2,max_eq_right ha.1]

@[expose] def pastBound (N : ℕ) : ℝ≥0 := ⟨Real.sqrt N/N,by positivity⟩

lemma matrixNoiseClass_restrict (hN : 0 < N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) {s t : ℝ≥0} (hst : s ≤ t) (i j : Fin N) :
    FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s (matrixNoiseClass hN hXa hXc hSphere t i j)=
      matrixNoiseClass hN hXa hXc hSphere s i j := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F s
      (matrixNoiseClass hN hXa hXc hSphere t i j),matrixNoiseClass_coeFn hN hXa hXc hSphere t i j,
      matrixNoiseClass_coeFn hN hXa hXc hSphere s i j] with q hcut ht hs
  rw [hcut,hs]
  by_cases hqs : q.1 ∈ Ioc 0 s
  · rw [indicator_of_mem (show q ∈ FourPapersCommon.FilteredBrownian.predictableTimeFrame s from ⟨hqs,mem_univ _⟩),ht]
    simp only [FourPapersCommon.continuousAdaptedTimeCut,hqs,show q.1 ∈ Ioc 0 t from ⟨hqs.1,hqs.2.trans hst⟩,ite_true]
  · simp only [indicator_of_notMem (show q ∉ FourPapersCommon.FilteredBrownian.predictableTimeFrame s from fun h => hqs h.1),
      FourPapersCommon.continuousAdaptedTimeCut,hqs,ite_false]

lemma matrixNoiseClass_slice (hN : 0 < N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) {s t : ℝ≥0} (hst : s ≤ t) (i j : Fin N) :
    FourPapersCommon.FilteredBrownian.predictableTimeSlice F s t (matrixNoiseClass hN hXa hXc hSphere t i j)=
      matrixNoiseClass hN hXa hXc hSphere t i j-matrixNoiseClass hN hXa hXc hSphere s i j := by
  rw [FourPapersCommon.FilteredBrownian.predictableTimeSlice,
    matrixNoiseClass_restrict hN hXa hXc hSphere le_rfl,
    matrixNoiseClass_restrict hN hXa hXc hSphere hst]

lemma coordinateNoiseValue_sub (D : BrownianDriver N P F) (hN : 0 < N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) {s t : ℝ≥0} (hst : s ≤ t) (i : Fin N) :
    coordinateNoiseValue D hN hXa hXc hSphere t i-coordinateNoiseValue D hN hXa hXc hSphere s i=
      vectorIto D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeSlice F s t
        (matrixNoiseClass hN hXa hXc hSphere t i j)) := by
  simp only [coordinateNoiseValue,driverItoMap_apply,vectorIto,coordinateIto,
    matrixNoiseClass_slice hN hXa hXc hSphere hst,map_sub,Finset.sum_sub_distrib]

/-- Exact deterministic contraction of a column with the frozen past point. -/
lemma noise_contraction_sum (x y : State N) (j : Fin N) :
    ∑ i : Fin N, y i/N*noiseColumn x j i=correlationNoise x y j := by
  rw [← overlap_eq_sum,overlap,← correlationNoise_eq_inner]

/-- Actual predictable equality: the overlap coefficient is the sum of the
bounded past-coordinate multipliers of the physical matrix coefficients. -/
lemma rowNoise_eq_past_matrix (hN : 0 < N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) {s t : ℝ≥0} (hst : s ≤ t) (j : Fin N) :
    rowNoise hN hXa hXc hSphere s t j=
      ∑ i : Fin N, BoundedItoMultiplier.predictableMulCLM t (pastCoordinate_measurable hXa s i)
        (pastBound N) (pastCoordinate_bound hN s i) (matrixNoiseClass hN hXa hXc hSphere t i j) := by
  let V (i : Fin N) := BoundedItoMultiplier.predictableMulCLM t (pastCoordinate_measurable hXa s i)
    (pastBound N) (pastCoordinate_bound hN s i) (matrixNoiseClass hN hXa hXc hSphere t i j)
  apply Subtype.ext
  apply Lp.ext
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun i => (V i : TimeProcessL2 P))
  have hprod := ae_all_iff.mpr (fun i : Fin N => BoundedItoMultiplier.predictableMulCLM_coe t
    (pastCoordinate_measurable hXa s i) (pastBound N) (pastCoordinate_bound hN s i)
    (matrixNoiseClass hN hXa hXc hSphere t i j))
  have hmat := ae_all_iff.mpr (fun i : Fin N => matrixNoiseClass_coeFn hN hXa hXc hSphere t i j)
  have hpath := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hSphere
  filter_upwards [rowNoise_coeFn hN hXa hXc hSphere hst j,hsum,hprod,hmat,hpath] with q hrow hsum hp hm hsp
  rw [hrow]
  change _=((∑ i : Fin N, V i : PredictableProcessL2 F P) : TimeProcessL2 P) q
  rw [Submodule.coe_sum,hsum]
  by_cases hqt : q.1 ∈ Ioc s t
  · have hq0t : q.1 ∈ Ioc 0 t := ⟨(zero_le : 0≤s).trans_lt hqt.1,hqt.2⟩
    simp only [hqt,ite_true,V,hp,elementaryRepresentative,hqt,FourPapersCommon.continuousAdaptedTimeCut,hm,hq0t]
    simp_rw [pastCoordinate_eq hN s _ (hsp s)]
    exact (noise_contraction_sum _ _ j).symm
  · simp only [hqt,ite_false,V,hp,elementaryRepresentative,hqt,zero_mul,Finset.sum_const_zero]

/-- The actual overlap-row stochastic integral is the bounded past sample
contracted with the physical coordinate noise increments. -/
lemma rowMartingaleValue_eq_bounded_sum (D : BrownianDriver N P F) (hN : 0 < N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) {s t : ℝ≥0} (hst : s ≤ t) :
    rowMartingaleValue D hN hXa hXc hSphere s t=
      ∑ i : Fin N, BoundedItoMultiplier.boundedMulCLM
        ((pastCoordinate_measurable hXa s i).mono (F.le s)).aestronglyMeasurable
        (pastBound N) (.of_forall (pastCoordinate_bound hN s i))
        (coordinateNoiseValue D hN hXa hXc hSphere t i-coordinateNoiseValue D hN hXa hXc hSphere s i) := by
  unfold rowMartingaleValue vectorIto
  simp_rw [rowNoise_eq_past_matrix hN hXa hXc hSphere hst,map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  change vectorIto D (fun j => BoundedItoMultiplier.predictableMulCLM t
    (pastCoordinate_measurable hXa s i) (pastBound N) (pastCoordinate_bound hN s i)
    (matrixNoiseClass hN hXa hXc hSphere t i j)) = _
  rw [BoundedItoMultiplier.vectorIto_mul D hst (pastCoordinate_measurable hXa s i)
    (pastBound N) (pastCoordinate_bound hN s i),← coordinateNoiseValue_sub D hN hXa hXc hSphere hst]

lemma rowMartingaleValue_ae_coordinateNoise (D : BrownianDriver N P F) (hN : 0 < N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) {s t : ℝ≥0} (hst : s ≤ t) :
    (rowMartingaleValue D hN hXa hXc hSphere s t : Ω → ℝ) =ᵐ[P]
      coordinateCorrelationNoise D hN hXa hXc hSphere s t := by
  let L (i : Fin N) := BoundedItoMultiplier.boundedMulCLM
    ((pastCoordinate_measurable hXa s i).mono (F.le s)).aestronglyMeasurable
    (pastBound N) (.of_forall (pastCoordinate_bound hN s i))
    (coordinateNoiseValue D hN hXa hXc hSphere t i-coordinateNoiseValue D hN hXa hXc hSphere s i)
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ L
  have hmul := ae_all_iff.mpr (fun i : Fin N => BoundedItoMultiplier.boundedMulCLM_coe
    ((pastCoordinate_measurable hXa s i).mono (F.le s)).aestronglyMeasurable
    (pastBound N) (.of_forall (pastCoordinate_bound hN s i))
    (coordinateNoiseValue D hN hXa hXc hSphere t i-coordinateNoiseValue D hN hXa hXc hSphere s i))
  have hsub := ae_all_iff.mpr (fun i : Fin N => Lp.coeFn_sub
    (coordinateNoiseValue D hN hXa hXc hSphere t i) (coordinateNoiseValue D hN hXa hXc hSphere s i))
  filter_upwards [hsum,hmul,hsub,hSphere] with ω hsum hmul hsub hsp
  rw [rowMartingaleValue_eq_bounded_sum D hN hXa hXc hSphere hst]
  change ((∑ i : Fin N, L i : RandomL2 P) : Ω → ℝ) ω= _
  rw [hsum]
  unfold coordinateCorrelationNoise
  apply Finset.sum_congr rfl
  intro i _
  change (L i : Ω → ℝ) ω= _
  rw [hmul i,hsub i,Pi.sub_apply,pastCoordinate_eq hN s i (hsp s)]

/-- The empirical physical multiplier, before any thermodynamic limit. -/
@[expose] def physicalMultiplier (β : ℝ) (J : Disorder N p) (x : State N) : ℝ :=
  kappa N+β*(p : ℝ)*Hamiltonian N p J x/N

/-- The actual finite-N correlation row equation, with its genuinely
constructed mean-zero martingale. This holds for random initial states
and every full-filtration physical strong solution. -/
theorem correlation_equation (D : BrownianDriver N P F) (hN : 0 < N)
    (β : ℝ) (J : Disorder N p) (Z0 : Ω → State N) (T : ℝ≥0)
    (hsol : RandomInitialSDE.IsStrongSolutionOn (fun i x => hamiltonianDrift β J x i)
      (fun i j x => noiseColumn x j i) continuous_noiseCoordinate D Z0 X T)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) :
    ∀ᵐ ω ∂P, overlap (X t ω) (X s ω) = 1+
      (∫ u in (s : ℝ)..(t : ℝ),
        β/N*inner ℝ (hamiltonianGradient J (X u.toNNReal ω)) (X s ω)-
          physicalMultiplier β J (X u.toNNReal ω)*overlap (X u.toNNReal ω) (X s ω))+
      (rowMartingaleValue D hN hXa hXc hSphere s t : Ω → ℝ) ω := by
  filter_upwards [correlation_equation_coordinates D hN β J Z0 T hsol hXa hXc hSphere hst ht,
    rowMartingaleValue_ae_coordinateNoise D hN hXa hXc hSphere hst] with ω heq hnoise
  rw [hnoise]
  convert heq using 1
  congr 2
  apply intervalIntegral.integral_congr
  intro u _
  exact (correlation_drift β J _ _).symm

/-- The residual defined from the genuine overlap and actual Hamiltonian
force is exactly the actual stochastic integral. -/
@[expose] def correlationResidual (β : ℝ) (J : Disorder N p) (s t : ℝ≥0) (ω : Ω) : ℝ :=
  overlap (X t ω) (X s ω)-1-
    (∫ u in (s : ℝ)..(t : ℝ),
      β/N*inner ℝ (hamiltonianGradient J (X u.toNNReal ω)) (X s ω)-
        physicalMultiplier β J (X u.toNNReal ω)*overlap (X u.toNNReal ω) (X s ω))

/-- Quantitative stochastic residual bound for the actual integral
correlation equation. The `O(1/N)` estimate is a conclusion. -/
theorem correlationResidual_second_moment_le (D : BrownianDriver N P F) (hN : 0 < N)
    (β : ℝ) (J : Disorder N p) (Z0 : Ω → State N) (T : ℝ≥0)
    (hsol : RandomInitialSDE.IsStrongSolutionOn (fun i x => hamiltonianDrift β J x i)
      (fun i j x => noiseColumn x j i) continuous_noiseCoordinate D Z0 X T)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω)) {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) :
    ∫ ω, correlationResidual (X := X) β J s t ω ^ 2 ∂P ≤ 2*((t : ℝ)-s)/N := by
  have heq : correlationResidual (X := X) β J s t =ᵐ[P]
      (rowMartingaleValue D hN hXa hXc hSphere s t : Ω → ℝ) := by
    filter_upwards [correlation_equation D hN β J Z0 T hsol hXa hXc hSphere hst ht] with ω hω
    unfold correlationResidual
    linarith
  calc
    _ = ∫ ω, (rowMartingaleValue D hN hXa hXc hSphere s t : Ω → ℝ) ω ^ 2 ∂P :=
      integral_congr_ae (heq.fun_comp (fun z => z^2))
    _ ≤ _ := rowMartingaleValue_second_moment_le D hN hXa hXc hSphere hst

end SphericalAging.FiniteCorrelationEquation
