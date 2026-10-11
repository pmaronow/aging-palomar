module

public import SphericalAging.AdaptiveInitialSpanCost

public section

/-! Source10.7 Step1: the actual normalized initial projection is bounded
by the literal algorithm energy deficit at the dimension limit. -/
noncomputable section
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AdaptiveInitialSpanLimit
open Set Filter MeasureTheory FiniteModel AdaptiveInitialSpanCost AdaptiveResidualEnergyLimit
open AlgorithmEnergyDeficit ExternalFieldUniformCost ExternalFieldElementaryPenalty ExternalFieldSharpScalar
open GaussianLandscapeMoments
open scoped Topology NNReal

theorem initial_span_limsup {p k : ℕ} (hp : 3≤p) {L : ℝ≥0}
    (H : PublishedFieldThreshold p L) (dim : ℕ→ℕ)
    (hDim : ∀n,0<dim n) (hTop : Tendsto dim atTop atTop)
    {S : ℕ→Type} [∀n,MeasurableSpace (S n)] (ν : ∀n,Measure (S n))
    [∀n,IsProbabilityMeasure (ν n)]
    (W : ∀n,S n→Submodule ℝ (Vector (dim n)))
    (hW : ∀n,Measurable (fun z : S n×Vector (dim n) => (W n z.1).starProjection z.2))
    (hRank : ∀n s,Module.finrank ℝ (W n s)≤k)
    (A : ∀n,S n×Disorder (dim n) p→Vector (dim n))
    (hA : ∀n,Measurable (A n)) (hball : ∀n z,‖A n z‖≤Real.sqrt (dim n))
    (hLip : ∀n,∀ᵐs ∂ν n,LipschitzWith L
      (fun J : EuclideanSpace ℝ (TensorIndex (dim n) p) => A n (s,J.ofLp))) :
    limsup (fun n => projectionEnergy (ν n)
      (fun z : S n×Disorder (dim n) p => W n z.1) (A n)) atTop≤
        (k:ℝ)*(deficit (thresholdEnergy p) (fun n => meanEnergy (ν n) (A n))/betaD p)^(2/(p:ℝ)) := by
  let a : ℕ→ℝ := fun n => meanEnergy (ν n) (A n)
  let m : ℕ→ℝ := fun n => projectionEnergy (ν n)
    (fun z : S n×Disorder (dim n) p => W n z.1) (A n)
  let D : ℝ := deficit (thresholdEnergy p) a
  change limsup m atTop≤(k:ℝ)*(D/betaD p)^(2/(p:ℝ))
  have hD : 0≤D := deficit_nonnegative (thresholdEnergy p) a
  have hβ : 0<betaD p := betaD_positive hp
  have hpow : 0≤2/(p:ℝ) := by positivity
  have hP n : Measurable (fun z : S n×Disorder (dim n) p => (W n z.1).starProjection (A n z)) := by
    have hpair : Measurable (fun z : S n×Disorder (dim n) p => (z.1,A n z)) :=
      measurable_fst.prodMk (hA n)
    have hh := (hW n).comp hpair
    exact hh
  have hMB n : 0≤m n ∧ m n≤1 :=
    projectionEnergy_bounds (S := S n) (N := dim n) (p := p) (hDim n) (ν n)
      (fun z => W n z.1) (A n) (hP n) (hball n)
  have hAB n : |a n|≤momentCeiling p 1 :=
    meanEnergy_abs_bound (hDim n) (by omega : 0<p) (ν n) (A n) (hA n) (hball n)
  have haBelow : IsBoundedUnder (·≥·) atTop a := isBoundedUnder_of_eventually_ge
    (Eventually.of_forall fun n => show -momentCeiling p 1≤a n from by
      linarith [hAB n,neg_abs_le (a n)])
  have hmCo : IsCoboundedUnder (·≤·) atTop m :=
    isCoboundedUnder_le_of_le atTop (fun n => (hMB n).1)
  have hLower : thresholdEnergy p-D≤liminf a atTop := energy_lower (thresholdEnergy p) a
  have hbound (ε : ℝ) (hε : 0<ε) :
      limsup m atTop≤(k:ℝ)*((D+2*ε)/betaD p)^(2/(p:ℝ)) := by
    have hc := initial_span_cost_eventually hp H dim hDim hTop ν W hW hRank A hA hball hLip ε hε
    have he := eventually_lt_of_lt_liminf
      (show thresholdEnergy p-D-ε<liminf a atTop by linarith) haBelow
    apply limsup_le_of_le hmCo
    filter_upwards [hc,he] with n hn he
    have hmax : max 0 (thresholdEnergy p+ε-a n)≤D+2*ε := by
      apply max_le
      · positivity
      · linarith
    exact hn.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg (le_max_left _ _) hβ.le)
        (div_le_div_of_nonneg_right hmax hβ.le) hpow) (Nat.cast_nonneg k))
  have hεlim : Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hbase : Tendsto (fun j : ℕ => (D+2*(1/((j:ℝ)+1)))/betaD p)
      atTop (𝓝 (D/betaD p)) := by
    simpa only [mul_zero,add_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => D) atTop (𝓝 D)).add
        (hεlim.const_mul 2)).div_const (betaD p)
  have hlimit : Tendsto (fun j : ℕ => (k:ℝ)*((D+2*(1/((j:ℝ)+1)))/betaD p)^(2/(p:ℝ)))
      atTop (𝓝 ((k:ℝ)*(D/betaD p)^(2/(p:ℝ)))) :=
    ((Real.continuous_rpow_const hpow).tendsto _ |>.comp hbase).const_mul (k:ℝ)
  exact ge_of_tendsto hlimit (Eventually.of_forall fun j : ℕ =>
    hbound (1/((j:ℝ)+1)) (div_pos zero_lt_one (by positivity : 0<(j:ℝ)+1)))

end SphericalAging.AdaptiveInitialSpanLimit
