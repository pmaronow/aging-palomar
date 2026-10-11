module

public import SphericalAging.AdaptiveSourceProjectionMoments

public section

/-! The "in particular" clause of source10.7 for literal ball-valued
vectors in the disclosed span; no measurability in the past is required. -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteSpanPairingBound
open MeasureTheory Filter FiniteModel AdaptiveResidualEnergyLimit
open scoped Topology InnerProductSpace

theorem pointwise {N : ℕ} (hN : 0<N) (W : Submodule ℝ (Vector N)) (A Y : Vector N)
    (hY : Y∈W) (hYb : ‖Y‖≤Real.sqrt N) :
    |⟪A,Y⟫_ℝ/(N:ℝ)|^2≤‖W.starProjection A‖^2/(N:ℝ) := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hE : ⟪A,Y⟫_ℝ=⟪W.starProjection A,Y⟫_ℝ := by
    have hh := W.starProjection_inner_eq_zero A Y hY
    rw [inner_sub_left] at hh
    linarith
  have hI : |⟪A,Y⟫_ℝ|≤‖W.starProjection A‖*Real.sqrt N := by
    rw [hE]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hYb (norm_nonneg _))
  have hs := pow_le_pow_left₀ (abs_nonneg _) hI 2
  rw [mul_pow,Real.sq_sqrt hNr.le,sq_abs] at hs
  rw [sq_abs,div_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos hNr) hNr).mpr
  have ht := mul_le_mul_of_nonneg_right hs hNr.le
  simpa only [pow_two,mul_assoc] using ht

theorem mean_pairing_le_projection {N p : ℕ} {S : Type} [MeasurableSpace S]
    (hN : 0<N) (μ : Measure S) [IsProbabilityMeasure μ]
    (W : S×Disorder N p→Submodule ℝ (Vector N)) (A Y : S×Disorder N p→Vector N)
    (hP : Measurable (fun z => (W z).starProjection (A z))) (hA : Measurable A) (hY : Measurable Y)
    (hAb : ∀z,‖A z‖≤Real.sqrt N) (hYb : ∀z,‖Y z‖≤Real.sqrt N) (hmem : ∀z,Y z∈W z) :
    (∫z,|⟪A z,Y z⟫_ℝ/(N:ℝ)|^2 ∂μ.prod (disorderLaw N p))≤projectionEnergy μ W A := by
  have hpb z : ‖(W z).starProjection (A z)‖≤Real.sqrt N :=
    ((W z).norm_starProjection_apply_le _).trans (hAb z)
  have hm : MemLp (fun z => (W z).starProjection (A z)) 2 (μ.prod (disorderLaw N p)) :=
    MemLp.of_bound hP.aestronglyMeasurable (Real.sqrt N) (ae_of_all _ hpb)
  have hpi := ((memLp_two_iff_integrable_sq hm.norm.aestronglyMeasurable).mp hm.norm).div_const (N:ℝ)
  have hmeas : AEStronglyMeasurable (fun z => |⟪A z,Y z⟫_ℝ/(N:ℝ)|^2) (μ.prod (disorderLaw N p)) :=
    ((continuous_abs.measurable.comp ((hA.inner hY).div_const (N:ℝ))).pow_const 2).aestronglyMeasurable
  have hpair := hpi.mono' hmeas (ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pointwise hN (W z) (A z) (Y z) (hmem z) (hYb z)))
  exact integral_mono hpair hpi (fun z => pointwise hN (W z) (A z) (Y z) (hmem z) (hYb z))

theorem pairing_limit_of_projection_limit {Θ : Type*} {l : Filter Θ} {p : ℕ}
    {dim : ℕ→ℕ} (hDim : ∀n,0<dim n)
    {S : Θ→ℕ→Type} [∀θ n,MeasurableSpace (S θ n)]
    (μ : ∀θ n,Measure (S θ n)) [∀θ n,IsProbabilityMeasure (μ θ n)]
    (W : ∀θ n,S θ n×Disorder (dim n) p→Submodule ℝ (Vector (dim n)))
    (A Y : ∀θ n,S θ n×Disorder (dim n) p→Vector (dim n))
    (hP : ∀θ n,Measurable (fun z => (W θ n z).starProjection (A θ n z)))
    (hA : ∀θ n,Measurable (A θ n)) (hY : ∀θ n,Measurable (Y θ n))
    (hAb : ∀θ n z,‖A θ n z‖≤Real.sqrt (dim n))
    (hYb : ∀θ n z,‖Y θ n z‖≤Real.sqrt (dim n)) (hmem : ∀θ n z,Y θ n z∈W θ n z)
    (hlimit : Tendsto (fun θ => limsup (fun n => projectionEnergy (μ θ n) (W θ n) (A θ n)) atTop) l (𝓝 0)) :
    Tendsto (fun θ => limsup (fun n => ∫z,|⟪A θ n z,Y θ n z⟫_ℝ/(dim n:ℝ)|^2
      ∂(μ θ n).prod (disorderLaw (dim n) p)) atTop) l (𝓝 0) := by
  have hb θ n := projectionEnergy_bounds (hDim n) (μ θ n) (W θ n) (A θ n) (hP θ n) (hAb θ n)
  have hc θ n := mean_pairing_le_projection (hDim n) (μ θ n) (W θ n) (A θ n) (Y θ n)
    (hP θ n) (hA θ n) (hY θ n) (hAb θ n) (hYb θ n) (hmem θ n)
  have hnon θ n : (0:ℝ)≤∫z,|⟪A θ n z,Y θ n z⟫_ℝ/(dim n:ℝ)|^2
      ∂(μ θ n).prod (disorderLaw (dim n) p) := integral_nonneg (fun _ => sq_nonneg _)
  have hAbove θ : IsBoundedUnder (·≤·) atTop (fun n => projectionEnergy (μ θ n) (W θ n) (A θ n)) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (fun n => (hb θ n).2))
  have hPairAbove θ : IsBoundedUnder (·≤·) atTop (fun n => ∫z,|⟪A θ n z,Y θ n z⟫_ℝ/(dim n:ℝ)|^2
      ∂(μ θ n).prod (disorderLaw (dim n) p)) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (fun n => (hc θ n).trans (hb θ n).2))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimit
    (fun θ => le_limsup_of_frequently_le (Eventually.of_forall (hnon θ)).frequently (hPairAbove θ))
    (fun θ => limsup_le_limsup (Eventually.of_forall (hc θ))
      (isCoboundedUnder_le_of_le atTop (hnon θ)) (hAbove θ))

end SphericalAging.FiniteSpanPairingBound
