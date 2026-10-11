module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import SphericalAging.BrownianCompactSupTail
public import SphericalAging.WeakSecondMomentFirstMoment
public import SphericalAging.ActualBrownianPrimitiveTimeModulus

public section

/-! Dimension-uniform compact Brownian supremum under the literal full law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualBrownianCompactSupSecondMoment
open VectorBrownian BrownianVectorMoments BrownianCompactSupTail ActualBrownianPrimitiveTimeModulus
open HardSphereDynamics
variable {N p : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem coordinateSup_square_integrable_le (i : Fin N) (T : ℝ≥0) :
    Integrable (fun ω => (coordinateSup i T ω)^2) (law N) ∧
      (∫ω,(coordinateSup i T ω)^2 ∂law N)≤1+3*(T:ℝ)^2 := by
  exact WeakSecondMomentFirstMoment.integrable_and_integral_le_of_quadratic_tail
    (fun ω => (coordinateSup i T ω)^2) ((coordinateSup_measurable i T).pow_const 2).aestronglyMeasurable
    (fun _ => sq_nonneg _) (3*(T:ℝ)^2) (by positivity) (coordinateSup_square_tail i T)

@[expose] def compactVectorPath (T : ℝ≥0) (ω : Space N) : C(Icc (0:ℝ≥0) T,State N) :=
  ⟨fun s => brownianVector s.val ω,
    (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp
      (continuous_pi fun i => (ω i).continuous.comp continuous_subtype_val)⟩

@[expose] def brownianSup (T : ℝ≥0) (ω : Space N) : ℝ := ‖compactVectorPath T ω‖

theorem brownianSup_measurable (T : ℝ≥0) : Measurable (brownianSup (N:=N) T) := by
  apply Measurable.norm
  apply _root_.ContinuousMap.measurable_iff_eval.mpr
  intro s
  exact (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.comp (process_measurable N s.val)

theorem brownian_norm_le_sup (T s : ℝ≥0) (hs : s≤T) (ω : Space N) :
    ‖brownianVector s ω‖≤brownianSup T ω :=
  (compactVectorPath T ω).norm_coe_le_norm ⟨s,bot_le,hs⟩

theorem brownianSup_sq_le_coordinate_sum (T : ℝ≥0) (ω : Space N) :
    (brownianSup T ω)^2≤∑i : Fin N,(coordinateSup i T ω)^2 := by
  let K : ℝ := ∑i : Fin N,(coordinateSup i T ω)^2
  have hK : 0≤K := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : brownianSup T ω≤Real.sqrt K := by
    apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg K)).mpr
    intro s
    apply (Real.le_sqrt (norm_nonneg _) hK).mpr
    rw [←real_inner_self_eq_norm_sq,←coordinate_square_sum]
    apply Finset.sum_le_sum
    intro i _
    change (coordinate i s.val ω)^2≤(coordinateSup i T ω)^2
    have he := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg (compactCoordinatePath i T ω))).mpr
      (coordinate_le_sup i T s.val s.property.2 ω)
    simpa only [sq_abs,coordinateSup] using he
  have hh := (sq_le_sq₀ (norm_nonneg (compactVectorPath T ω)) (Real.sqrt_nonneg K)).mpr hb
  simpa only [Real.sq_sqrt hK,brownianSup,K] using hh

theorem brownianSup_square_integrable (T : ℝ≥0) :
    Integrable (fun ω => (brownianSup (N:=N) T ω)^2) (law N) := by
  have hi := integrable_finsetSum Finset.univ fun (i : Fin N) _ => (coordinateSup_square_integrable_le i T).1
  apply hi.mono' ((brownianSup_measurable T).pow_const 2).aestronglyMeasurable
  filter_upwards with ω
  change |(brownianSup T ω)^2|≤∑i : Fin N,(coordinateSup i T ω)^2
  rw [abs_of_nonneg (sq_nonneg _)]
  exact brownianSup_sq_le_coordinate_sum T ω

theorem brownianSup_secondMoment_le (T : ℝ≥0) :
    (∫ω,(brownianSup (N:=N) T ω)^2 ∂law N)≤(N:ℝ)*(1+3*(T:ℝ)^2) := by
  calc
    _≤∫ω,∑i : Fin N,(coordinateSup i T ω)^2 ∂law N :=
      integral_mono (brownianSup_square_integrable T)
        (integrable_finsetSum Finset.univ fun (i : Fin N) _ => (coordinateSup_square_integrable_le i T).1)
        (brownianSup_sq_le_coordinate_sum T)
    _=∑i : Fin N,∫ω,(coordinateSup i T ω)^2 ∂law N :=
      integral_finsetSum _ fun i _ => (coordinateSup_square_integrable_le i T).1
    _≤(N:ℝ)*(1+3*(T:ℝ)^2) := by
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
        Finset.sum_le_sum (s:=Finset.univ) (fun i _ => (coordinateSup_square_integrable_le i T).2)

@[expose] def compactBrownianSup (T : ℝ≥0) (ω : AnnealedCutoffProcess.Parameter N p×Space N) : ℝ :=
  brownianSup T ω.2

theorem compactBrownianSup_stronglyMeasurable (T : ℝ≥0) :
    StronglyMeasurable (compactBrownianSup (N:=N) (p:=p) T) :=
  ((brownianSup_measurable T).comp measurable_snd).stronglyMeasurable

theorem actualBrownian_norm_le_sup (T s : ℝ≥0) (hs : s≤T)
    (ω : AnnealedCutoffProcess.Parameter N p×Space N) :
    ‖actualBrownian s ω‖≤compactBrownianSup T ω := brownian_norm_le_sup T s hs ω.2

theorem compactBrownianSup_memLp_two (T : ℝ≥0) :
    MemLp (compactBrownianSup (N:=N) (p:=p) T) 2 (AnnealedModelLaw.law N p) :=
  ((memLp_two_iff_integrable_sq (brownianSup_measurable T).aestronglyMeasurable).mpr
    (brownianSup_square_integrable T)).comp_measurePreserving
      (measurePreserving_snd (μ:=AnnealedModelLaw.parameterLaw N p) (ν:=law N))

theorem compactBrownianSup_secondMoment_le (T : ℝ≥0) :
    (∫ω,(compactBrownianSup (N:=N) (p:=p) T ω)^2 ∂AnnealedModelLaw.law N p)
      ≤(N:ℝ)*(1+3*(T:ℝ)^2) := by
  simp only [compactBrownianSup,AnnealedModelLaw.law]
  rw [integral_fun_snd (μ:=AnnealedModelLaw.parameterLaw N p) (ν:=law N) (fun ω : Space N => (brownianSup T ω)^2)]
  simpa only [probReal_univ,one_smul] using brownianSup_secondMoment_le (N:=N) T

@[expose] def normalizedBrownianSup (T : ℝ≥0) (ω : AnnealedCutoffProcess.Parameter N p×Space N) : ℝ :=
  compactBrownianSup T ω/Real.sqrt N

theorem normalizedBrownianSup_nonneg (T : ℝ≥0) (ω : AnnealedCutoffProcess.Parameter N p×Space N) :
    0≤normalizedBrownianSup T ω := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

theorem normalizedBrownianSup_stronglyMeasurable (T : ℝ≥0) :
    StronglyMeasurable (normalizedBrownianSup (N:=N) (p:=p) T) :=
  (continuous_id.div_const (Real.sqrt N)).comp_stronglyMeasurable (compactBrownianSup_stronglyMeasurable T)

theorem normalizedBrownianSup_memLp_two (T : ℝ≥0) :
    MemLp (normalizedBrownianSup (N:=N) (p:=p) T) 2 (AnnealedModelLaw.law N p) :=
  by
    change MemLp (fun ω => compactBrownianSup (N:=N) (p:=p) T ω/Real.sqrt N) 2 (AnnealedModelLaw.law N p)
    simpa only [div_eq_mul_inv] using (compactBrownianSup_memLp_two (N:=N) (p:=p) T).mul_const ((Real.sqrt N)⁻¹)

theorem normalizedBrownianSup_secondMoment_le (hN : 1≤N) (T : ℝ≥0) :
    (∫ω,(normalizedBrownianSup (N:=N) (p:=p) T ω)^2 ∂AnnealedModelLaw.law N p)
      ≤1+3*(T:ℝ)^2 := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr (by omega : 0<N)
  simp only [normalizedBrownianSup,div_pow]
  rw [integral_div,Real.sq_sqrt hn.le]
  exact (div_le_iff₀ hn).mpr (by simpa only [mul_comm] using compactBrownianSup_secondMoment_le (N:=N) (p:=p) T)

end SphericalAging.ActualBrownianCompactSupSecondMoment
