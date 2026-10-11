module

public import SphericalAging.ActualBrownianCompactSupSecondMoment
public import SphericalAging.ActualStateDyadicTightness
public import SphericalAging.BrownianVectorIncrementFourthMoment

public section

/-! Dimension-uniform dyadic approximation of the literal normalized Wiener path. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.BrownianNormalizedDyadicTightness
open HardSphereDynamics BrownianVectorMoments ActualBrownianPrimitiveTimeModulus
open ActualStateDyadicTightness DyadicProcessGoodEvent DyadicContinuousChaining
variable {N p : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

@[expose] def normalizedBrownian (t : ℝ≥0) (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : State N :=
  (Real.sqrt N)⁻¹ • actualBrownian t ω

theorem normalizedBrownian_stronglyMeasurable (t : ℝ≥0) :
    StronglyMeasurable (normalizedBrownian (N:=N) (p:=p) t) := by
  change StronglyMeasurable ((Real.sqrt N)⁻¹ • actualBrownian (N:=N) (p:=p) t)
  apply StronglyMeasurable.const_smul
  exact ((PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.comp
    ((VectorBrownian.process_measurable N t).comp measurable_snd)).stronglyMeasurable

theorem normalizedBrownian_continuous (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :
    Continuous (fun t => normalizedBrownian t ω) := by
  change Continuous ((Real.sqrt N)⁻¹ • (fun t => actualBrownian t ω))
  apply Continuous.const_smul
  exact (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp (continuous_pi fun i => (ω.2 i).continuous)

theorem normalizedBrownian_increment_memLp_four (r h : ℝ≥0) :
    MemLp (fun ω => normalizedBrownian (N:=N) (p:=p) (r+h) ω-normalizedBrownian r ω) 4 (AnnealedModelLaw.law N p) := by
  change MemLp (fun ω => (Real.sqrt N)⁻¹ • actualBrownian (r+h) ω-(Real.sqrt N)⁻¹ • actualBrownian r ω) 4 (AnnealedModelLaw.law N p)
  have hm := ((actualBrownian_memLp (N:=N) (p:=p) (r+h) (q:=4) (by norm_num)).sub
    (actualBrownian_memLp r (q:=4) (by norm_num))).const_smul ((Real.sqrt N)⁻¹)
  apply MemLp.ae_eq (hf_Lp:=hm)
  filter_upwards with ω
  change (Real.sqrt N)⁻¹ • (actualBrownian (r+h) ω-actualBrownian r ω)=_
  exact smul_sub _ _ _

theorem actualBrownian_increment_fourthMoment (r h : ℝ≥0) :
    (∫ω,‖actualBrownian (N:=N) (p:=p) (r+h) ω-actualBrownian r ω‖^4 ∂AnnealedModelLaw.law N p)
      ≤3*(N:ℝ)^2*(h:ℝ)^2 := by
  simp only [actualBrownian,AnnealedModelLaw.law]
  rw [integral_fun_snd (μ:=AnnealedModelLaw.parameterLaw N p) (ν:=VectorBrownian.law N) (fun ω : VectorBrownian.Space N => ‖brownianVector (r+h) ω-brownianVector r ω‖^4)]
  simpa only [probReal_univ,one_smul] using (BrownianVectorIncrementFourthMoment.increment_fourthMoment (N:=N) r h).2

theorem normalizedBrownian_increment_fourthMoment (hN : 1≤N) (r h : ℝ≥0) :
    (∫ω,‖normalizedBrownian (N:=N) (p:=p) (r+h) ω-normalizedBrownian r ω‖^4 ∂AnnealedModelLaw.law N p)
      ≤3*(h:ℝ)^2 := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr (by omega : 0<N)
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  simp only [normalizedBrownian,←smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le),mul_pow]
  rw [integral_const_mul]
  calc
    _≤((Real.sqrt N)⁻¹)^4*(3*(N:ℝ)^2*(h:ℝ)^2) :=
      mul_le_mul_of_nonneg_left (actualBrownian_increment_fourthMoment r h) (by positivity)
    _=3*(h:ℝ)^2 := by
      rw [inv_pow,show (4:ℕ)=2*2 from rfl,pow_mul,Real.sq_sqrt hn.le]
      field_simp

@[expose] def brownianBadTail (T : ℝ≥0) (m : ℕ) : Set (AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :=
  badTail normalizedBrownian T dyadicRatio m

@[expose] def brownianTailProbabilityCeiling (T : ℝ≥0) (m : ℕ) : ℝ :=
  (3*(T:ℝ)^2)*(1/(2*dyadicRatio^4))^(m+1)/(1-1/(2*dyadicRatio^4))

theorem normalizedBrownian_grid_fourthMoment (hN : 1≤N) (T : ℝ≥0) (n k : ℕ) :
    (∫ω,‖normalizedBrownian (N:=N) (p:=p) (uniformPartitionTime T (2^n) (k+1)) ω-
      normalizedBrownian (uniformPartitionTime T (2^n) k) ω‖^4 ∂AnnealedModelLaw.law N p)
      ≤(3*(T:ℝ)^2)/(2^n:ℝ)^2 := by
  rw [uniformPartitionTime_succ_add]
  simpa only [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_ofNat,div_pow,mul_div_assoc] using
    normalizedBrownian_increment_fourthMoment (p:=p) hN (uniformPartitionTime T (2^n) k) (T/(2^n:ℝ≥0))

theorem brownianBadTail_measure_le (hN : 1≤N) (T : ℝ≥0) (m : ℕ) :
    (AnnealedModelLaw.law N p) (brownianBadTail (N:=N) (p:=p) T m)
      ≤ENNReal.ofReal (brownianTailProbabilityCeiling T m) := by
  apply badTail_measure_le _ _ _ _ (by positivity) (by norm_num [dyadicRatio]) (by norm_num [dyadicRatio]) m
  intro n
  apply badGrid_measure_le _ _ _ _ (by norm_num [dyadicRatio]) n
  · intro k
    rw [uniformPartitionTime_succ_add]
    exact normalizedBrownian_increment_memLp_four (uniformPartitionTime T (2^n) k.val) (T/(2^n:ℝ≥0))
  · intro k
    exact normalizedBrownian_grid_fourthMoment hN T n k.val

theorem brownian_grid_approximation_on_good (T : ℝ≥0) (m : ℕ)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N)
    (hgood : ω∉brownianBadTail T m) (s : ℝ≥0) (hs : s≤T) :
    ‖normalizedBrownian (timeApprox T m s) ω-normalizedBrownian s ω‖≤gridErrorCeiling m :=
  path_distance_to_grid_on_good (by norm_num [dyadicRatio]) (by norm_num [dyadicRatio]) hgood
    (normalizedBrownian_continuous ω) s hs

theorem brownianTailProbabilityCeiling_tendsto_zero (T : ℝ≥0) :
    Tendsto (brownianTailProbabilityCeiling T) atTop (𝓝 0) := by
  unfold brownianTailProbabilityCeiling
  have hh := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (by norm_num [dyadicRatio] : |1/(2*dyadicRatio^4)|<1)).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def,mul_zero,zero_div] using
    (hh.const_mul (3*(T:ℝ)^2)).div_const (1-1/(2*dyadicRatio^4))
theorem brownianBadTail_measurableSet (T : ℝ≥0) (m : ℕ) :
    MeasurableSet (brownianBadTail (N:=N) (p:=p) T m) := by
  unfold brownianBadTail badTail
  apply MeasurableSet.iUnion
  intro j
  have h : MeasurableSet (⋃k : Fin (2^(m+j+1)),{ω | dyadicRatio^(m+j+1)<
      ‖normalizedBrownian (N:=N) (p:=p) (uniformPartitionTime T (2^(m+j+1)) (k.val+1)) ω-
        normalizedBrownian (uniformPartitionTime T (2^(m+j+1)) k.val) ω‖}) := by
    apply MeasurableSet.iUnion
    intro k
    exact measurableSet_lt measurable_const
      ((normalizedBrownian_stronglyMeasurable _).sub (normalizedBrownian_stronglyMeasurable _)).norm.measurable
  convert h using 1
  ext ω
  simp only [badGrid,mem_iUnion,mem_setOf_eq]

theorem normalizedBrownian_norm_le_sup (T s : ℝ≥0) (hs : s≤T)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :
    ‖normalizedBrownian s ω‖≤ActualBrownianCompactSupSecondMoment.normalizedBrownianSup T ω := by
  simp only [normalizedBrownian,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    ActualBrownianCompactSupSecondMoment.normalizedBrownianSup,div_eq_mul_inv]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (ActualBrownianCompactSupSecondMoment.actualBrownian_norm_le_sup T s hs ω)
    (inv_nonneg.mpr (Real.sqrt_nonneg (N:ℝ)))

end SphericalAging.BrownianNormalizedDyadicTightness
