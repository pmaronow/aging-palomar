module

public import SphericalAging.ActualNormalizedGamma
public import SphericalAging.ActualOverlapCompactPathConcentration

public section

/-! The actual Γ path admits a weighted finite mesh approximation outside
a genuine dimension-uniform exceptional event. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualGammaDyadicApproximation
open HardSphereDynamics ActualNormalizedStateFourthIncrement ActualNormalizedOverlap
open ActualNormalizedGamma ActualBrownianPrimitiveTimeModulus BrownianNormalizedDyadicTightness
open ActualBrownianCompactSupSecondMoment ActualStateDyadicTightness ActualOverlapDyadicApproximation
open DyadicContinuousChaining ActualOverlapCompactPathConcentration
variable {N p : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose] def gammaBadTail (β R : ℝ≥0) (hR : 0<(R:ℝ)) (T : ℝ≥0) (m : ℕ) :
    Set (AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :=
  stateBadTail β R hR T m ∪ brownianBadTail T m

@[expose] def gammaTailProbabilityCeiling (p : ℕ) (β T : ℝ≥0) (m : ℕ) : ℝ :=
  tailProbabilityCeiling p β T m+brownianTailProbabilityCeiling T m

theorem gammaTailProbabilityCeiling_nonneg (p : ℕ) (β T : ℝ≥0) (m : ℕ) :
    0≤gammaTailProbabilityCeiling p β T m := by
  have hs := tailProbabilityCeiling_nonneg p β T m
  have hb : 0≤brownianTailProbabilityCeiling T m := by
    unfold brownianTailProbabilityCeiling
    norm_num [dyadicRatio]
    positivity
  exact add_nonneg hs hb

theorem gammaBadTail_measurableSet (β R : ℝ≥0) (hR : 0<(R:ℝ)) (T : ℝ≥0) (m : ℕ) :
    MeasurableSet (gammaBadTail (N:=N) (p:=p) β R hR T m) :=
  (stateBadTail_measurableSet β R hR T m).union (brownianBadTail_measurableSet T m)

theorem gammaBadTail_real_le (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (T : ℝ≥0) (m : ℕ) :
    (AnnealedModelLaw.law N p).real (gammaBadTail β R hR T m)≤gammaTailProbabilityCeiling p β T m := by
  have hB := ENNReal.toReal_mono ENNReal.ofReal_ne_top (brownianBadTail_measure_le (p:=p) hN T m)
  have hb0 : 0≤brownianTailProbabilityCeiling T m := by
    unfold brownianTailProbabilityCeiling
    norm_num [dyadicRatio]
    positivity
  have hB' : (AnnealedModelLaw.law N p).real (brownianBadTail T m)≤brownianTailProbabilityCeiling T m := by
    simpa only [measureReal_def,ENNReal.toReal_ofReal hb0] using hB
  exact (measureReal_union_le _ _).trans (add_le_add
    (stateBadTail_real_le hN hp β R hR hNR T m) hB')

theorem actualGamma_grid_approximation_on_good (hN : 1≤N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (T : ℝ≥0) (m : ℕ) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,ω∉gammaBadTail (p:=p) β R hR T m→
      ∀t s : ℝ≥0,t≤T→s≤T→
        |actualGamma β R hR t s ω-
          actualGamma β R hR (timeApprox T m t) (timeApprox T m s) ω|≤
            gridErrorCeiling m*(1+gammaEnvelope T ω) := by
  have he : 0≤gridErrorCeiling m := by norm_num [gridErrorCeiling,dyadicRatio]; positivity
  filter_upwards [state_grid_approximation_on_good (p:=p) β R hR T m,
    normalizedState_norm_one hN β R hR hNR] with ω hω hunit hgood t s ht hs
  have hState : ω∉stateBadTail β R hR T m := fun h => hgood (Or.inl h)
  have hBrownian : ω∉brownianBadTail T m := fun h => hgood (Or.inr h)
  have ht' := hω hState t ht
  have hs' := brownian_grid_approximation_on_good T m ω hBrownian s hs
  rw [norm_sub_rev] at ht' hs'
  rw [actualGamma_eq_normalized_inner (by omega : 0<N),actualGamma_eq_normalized_inner (by omega : 0<N),
    ←sub_div,abs_div,abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hb := normalizedBrownian_norm_le_sup T s hs ω
  have hinner := inner_difference_weighted (normalizedState β R hR t ω) (normalizedBrownian s ω)
    (normalizedState β R hR (timeApprox T m t) ω) (normalizedBrownian (timeApprox T m s) ω)
    (hunit _)
  have hh : |⟪normalizedState β R hR t ω,normalizedBrownian s ω⟫_ℝ-
      ⟪normalizedState β R hR (timeApprox T m t) ω,normalizedBrownian (timeApprox T m s) ω⟫_ℝ|≤
        gridErrorCeiling m*(1+gammaEnvelope T ω) := by
    refine hinner.trans ?_
    calc
      _≤gridErrorCeiling m*gammaEnvelope T ω+gridErrorCeiling m :=
        add_le_add (mul_le_mul ht' hb (norm_nonneg _) he) hs'
      _=_ := by ring
  exact (div_le_div_of_nonneg_right hh (Real.sqrt_nonneg 2)).trans
    (div_le_self (mul_nonneg he (by linarith [gammaEnvelope_nonneg T ω])) (by norm_num))

theorem gammaTailProbabilityCeiling_tendsto_zero (p : ℕ) (β T : ℝ≥0) :
    Tendsto (gammaTailProbabilityCeiling p β T) atTop (𝓝 0) := by
  unfold gammaTailProbabilityCeiling
  simpa only [add_zero] using
    (tailProbabilityCeiling_tendsto_zero p β T).add (brownianTailProbabilityCeiling_tendsto_zero T)

end SphericalAging.ActualGammaDyadicApproximation
