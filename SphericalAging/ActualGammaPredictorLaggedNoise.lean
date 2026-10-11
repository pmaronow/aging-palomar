module

public import SphericalAging.ActualGammaPredictorNoiseBounds
public import SphericalAging.WeightedBrownianNoiseRow

public section

/-! Actual Γ predictor noise rows evaluated at an earlier physical state,
with their genuine past measurability and dimension-sharp second moments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualGammaPredictorLaggedNoise
open FiniteModel HardSphereDynamics LocalSDE ActualSphereTransition ActualSphereMeanDerivative
open ActualGammaBackwardPredictor ActualGammaFutureInnovation ActualSphereGammaVariance
open ActualDisorderGammaVariance ActualSphereLinearTransition BrownianVectorMoments
open ActualGammaPredictorNoiseBounds WeightedBrownianNoiseRow
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem noiseRow_continuous (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (T t s q : ℝ≥0) (hT : 0<T) (j : Fin N) :
    Continuous (fun z : State N×State N => noiseRow β R hR J T t s q z.1 z.2 j) := by
  unfold noiseRow
  have hl : Continuous (fun z : State N×State N => fderiv ℝ (linearTest β R hR J t q z.2) z.1 (noiseColumn z.1 j)) := by
    simp_rw [linearTest_fderiv]
    exact (continuous_snd.inner
      ((((ActualSphereMeanSpatialC2.mean_contDiff_two (VectorBrownian.driver N) β J R hR (t-q)).continuous_fderiv (by norm_num)).comp continuous_fst).clm_apply
        ((contDiff_noiseColumn j).continuous.comp continuous_fst))).div_const _
  have hg : Continuous (fun x : State N => fderiv ℝ (initialMean β R hR J T (t-q) (s-q)) x (noiseColumn x j)) :=
    ((gammaMean_initial_contDiff_two β R hR J T (t-q) (s-q) hT).continuous_fderiv (by norm_num)).clm_apply (contDiff_noiseColumn j).continuous
  have hm : Continuous (fun x : State N => (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-q) x) j/(Real.sqrt 2*(N : ℝ))) :=
    ((VariationalCoefficients.coordinate j).continuous.comp
      (ActualSphereMeanSpatialC2.mean_contDiff_two (VectorBrownian.driver N) β J R hR (t-q)).continuous).div_const _
  exact (hl.add (hg.comp continuous_fst)).add (hm.comp continuous_fst)

section Actual
variable (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    {Z0 : VectorBrownian.Space N→State N}
    (X : ℝ≥0→VectorBrownian.Space N→State N)
    (hX : ∀ H,AnnealedSDECore.IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X H)
    (T t s r q : ℝ≥0) (hT : 0<T)

include hX hT in
theorem lagged_noiseRow_stronglyMeasurable (j : Fin N) :
    StronglyMeasurable[NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) r]
      (fun ω => noiseRow β R hR J T t s q (X r ω) (brownianVector r ω) j) := by
  letI : MeasurableSpace (VectorBrownian.Space N) :=
    NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) r
  have hx : StronglyMeasurable (X r) := (hX 0).2.1 r
  have hb : StronglyMeasurable (brownianVector (N:=N) r) :=
    (brownianVector_waiting_measurable (N:=N) r).stronglyMeasurable
  have hh : StronglyMeasurable (fun ω => (X r ω,brownianVector (N:=N) r ω)) := hx.prodMk hb
  have hc : StronglyMeasurable ((fun z : State N×State N => noiseRow β R hR J T t s q z.1 z.2 j)∘
      (fun ω => (X r ω,brownianVector (N:=N) r ω))) :=
    (noiseRow_continuous β R hR J T t s q hT j).comp_stronglyMeasurable hh
  simpa only [Function.comp_def] using hc

variable (hN : 3≤N) (hp : 2≤p) (hNR : (N : ℝ)<(R : ℝ)^2)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ u,OnSphere (X u ω))
    (ht : t≤T) (hrq : r≤q) (hqs : q≤s)

include hX hT hN hp hNR hSphere ht hrq hqs in
/-- No independence of the physical state and the observed Brownian vector
is assumed. The earlier evaluation preserves the sharp row bound. -/
theorem lagged_noiseRow_secondMoment :
    Integrable (fun ω => ∑j : Fin N,(noiseRow β R hR J T t s q (X r ω) (brownianVector r ω) j)^2)
      (VectorBrownian.law N) ∧
      (∫ ω,∑j : Fin N,(noiseRow β R hR J T t s q (X r ω) (brownianVector r ω) j)^2 ∂VectorBrownian.law N)≤
        ((3*(s : ℝ))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T)+3/2)/(N : ℝ) := by
  let P := VectorBrownian.law N
  let E : ℝ := Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T)
  let f : VectorBrownian.Space N→ℝ := fun ω => ∑j : Fin N,(noiseRow β R hR J T t s q (X r ω) (brownianVector r ω) j)^2
  let g : VectorBrownian.Space N→ℝ := fun ω =>
    (3*‖brownianVector r ω‖^2/(N : ℝ)^2+3*((s-q : ℝ≥0) : ℝ)/(N : ℝ))*E+3/(2*(N : ℝ))
  have hfm : StronglyMeasurable f := by
    apply Finset.stronglyMeasurable_fun_sum
    intro j _
    exact ((lagged_noiseRow_stronglyMeasurable β R hR J X hX T t s r q hT j).mono
      ((NullAugmentation.augment (VectorBrownian.filtration N) P).le r)).pow 2
  have hgi : Integrable g P :=
    ((((brownianVector_memLp (N:=N) r (q:=2) (by norm_num)).integrable_norm_pow'.const_mul 3).div_const ((N : ℝ)^2)).add
      (integrable_const (3*((s-q : ℝ≥0) : ℝ)/(N : ℝ))) |>.mul_const E |>.add (integrable_const (3/(2*(N : ℝ)))))
  have hbound : ∀ᵐ ω ∂P,f ω≤g ω := hSphere.mono
    (fun ω h => noiseRow_square_sum_le hN hp β R hR hNR J T t s q ht hT (X r ω) (brownianVector r ω) (h r))
  have hfi : Integrable f P := hgi.mono' hfm.aestronglyMeasurable (hbound.mono (fun ω h => by
    change ‖f ω‖≤g ω
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact h))
  refine ⟨hfi,(integral_mono_ae hfi hgi hbound).trans ?_⟩
  dsimp only [g]
  have hAi : Integrable (fun ω => 3*‖brownianVector r ω‖^2/(N : ℝ)^2) P :=
    ((brownianVector_memLp (N:=N) r (q:=2) (by norm_num)).integrable_norm_pow'.const_mul 3).div_const _
  have hbase : Integrable (fun ω => (3*‖brownianVector r ω‖^2/(N : ℝ)^2+3*((s-q : ℝ≥0) : ℝ)/(N : ℝ))*E) P :=
    (hAi.add (integrable_const _)).mul_const E
  rw [integral_add hbase (integrable_const _),integral_mul_const,
    integral_add hAi (integrable_const _),integral_div,integral_const_mul,brownianVector_secondMoment]
  simp only [integral_const,probReal_univ,one_smul]
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr (by omega : 0<N)
  rw [NNReal.coe_sub hqs]
  calc
    _=((3*(r : ℝ)+3*((s : ℝ)-(q : ℝ)))*E+3/2)/(N : ℝ) := by field_simp
    _≤((3*(s : ℝ))*E+3/2)/(N : ℝ) := by
      apply div_le_div_of_nonneg_right _ hn.le
      have hrq' : (r : ℝ)≤q := by exact_mod_cast hrq
      have hE : 0≤E := Real.exp_nonneg _
      nlinarith
    _=_ := rfl

include hX hT hN hp hNR hSphere ht hrq hqs in
theorem lagged_noiseRow_memLp (j : Fin N) :
    MemLp (fun ω => noiseRow β R hR J T t s q (X r ω) (brownianVector r ω) j) 2 (VectorBrownian.law N) := by
  have hm := (lagged_noiseRow_stronglyMeasurable β R hR J X hX T t s r q hT j).mono
    ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le r)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hf := (lagged_noiseRow_secondMoment β R hR J X hX T t s r q hT hN hp hNR hSphere ht hrq hqs).1
  apply hf.mono' (hm.pow 2).aestronglyMeasurable
  exact .of_forall (fun ω => by
    change ‖(noiseRow β R hR J T t s q (X r ω) (brownianVector r ω) j)^2‖≤_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ j))

end Actual
end SphericalAging.ActualGammaPredictorLaggedNoise
