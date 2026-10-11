module

public import SphericalAging.RenewalSupportSemigroup
public import SphericalAging.RenewalRemainder

public section

/-! A genuine maximum principle for bounded uniformly continuous harmonic
profiles of positive nonarithmetic renewal laws, under only source hypotheses. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalAging.PositiveRenewalHarmonicMaximum
noncomputable section
set_option backward.isDefEq.respectTransparency false
open RenewalSupportSemigroup RenewalFirstMoment RenewalRemainder AbsorptionCutoff.Renewal

/-- A maximum of an actual harmonic profile propagates through each point
of the actual topological support of the increment law. -/
theorem harmonic_maximum_support_shift {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {F : ℝ → ℝ} (hc : Continuous F) (B : ℝ) (hb : ∀x,‖F x‖≤B)
    (hHarm : ∀x : ℝ,F x=∫ y,F (x-y) ∂μ) {M : ℝ} (hMax : ∀x,F x≤M)
    {x : ℝ} (hx : F x=M) {y : ℝ} (hy : y∈μ.support) : F (x-y)=M := by
  have hi : Integrable (fun y : ℝ => F (x-y)) μ :=
    Integrable.of_bound (by fun_prop) B (Eventually.of_forall fun y => hb (x-y))
  have hnn : 0≤ᵐ[μ] (fun y : ℝ => M-F (x-y)) :=
    Eventually.of_forall fun y => sub_nonneg.mpr (hMax (x-y))
  have hzero : (∫ y : ℝ,M-F (x-y) ∂μ)=0 := by
    rw [integral_sub (integrable_const M) hi,integral_const,←hHarm x,hx]
    simp
  have heq : ∀ᵐ y ∂μ,F (x-y)=M := by
    have ha := (integral_eq_zero_iff_of_nonneg_ae hnn ((integrable_const M).sub hi)).mp hzero
    filter_upwards [ha] with y hy
    change M-F (x-y)=0 at hy
    linarith
  have hclosed : IsClosed {y : ℝ | F (x-y)=M} :=
    isClosed_eq (hc.comp (continuous_const.sub continuous_id)) continuous_const
  exact Measure.support_subset_of_isClosed hclosed heq hy

theorem harmonic_maximum_semigroup_shift {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {F : ℝ → ℝ} (hc : Continuous F) (B : ℝ) (hb : ∀x,‖F x‖≤B)
    (hHarm : ∀x : ℝ,F x=∫ y,F (x-y) ∂μ) {M : ℝ} (hMax : ∀x,F x≤M)
    {s : ℝ} (hs : s∈supportSemigroup μ) : ∀x : ℝ,F x=M → F (x-s)=M := by
  change s∈AddSubmonoid.closure μ.support at hs
  refine AddSubmonoid.closure_induction (motive:=fun s _ => ∀x : ℝ,F x=M → F (x-s)=M) ?_ ?_ ?_ hs
  · intro y hy x hx
    exact harmonic_maximum_support_shift hc B hb hHarm hMax hx hy
  · intro x hx
    simpa only [sub_zero] using hx
  · intro a b ha hb hpa hpb x hx
    have hxa := hpa x hx
    have hxab := hpb (x-a) hxa
    simpa only [sub_sub] using hxab

/-- Eventual support-semigroup density and uniform continuity force the
actual maximum-attaining harmonic profile to converge to its maximum at
negative infinity. -/
theorem harmonic_maximum_tendsto_atBot {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hna : ¬Arithmetic μ) {F : ℝ → ℝ}
    (huc : UniformContinuous F) (B : ℝ) (hb : ∀x,‖F x‖≤B)
    (hHarm : ∀x : ℝ,F x=∫ y,F (x-y) ∂μ) (x₀ : ℝ) (hMax : ∀x,F x≤F x₀) :
    Tendsto F atBot (𝓝 (F x₀)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδF⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  obtain ⟨T,hT⟩ := source_positive_support_eventually_dense hp hna hδ
  filter_upwards [eventually_le_atBot (x₀-T)] with x hx
  obtain ⟨s,hs,hsl,hsd⟩ := hT (x₀-x) (by linarith)
  have hdist : dist (x₀-s) x<δ := by
    rw [Real.dist_eq,abs_of_nonneg (by linarith : 0≤x₀-s-x)]
    linarith
  have hshift : F (x₀-s)=F x₀ :=
    harmonic_maximum_semigroup_shift huc.continuous B hb hHarm hMax hs x₀ rfl
  have he := hδF hdist
  rw [hshift,dist_comm] at he
  exact he

/-- An actual bounded harmonic profile with an actual limit at negative
infinity is constant for every positive increment law. -/
theorem bounded_harmonic_constant_of_atBot {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {F : ℝ → ℝ} (hm : Measurable F)
    (B : ℝ) (hb : ∀x,‖F x‖≤B) (hHarm : ∀x : ℝ,F x=∫ y,F (x-y) ∂μ)
    {M : ℝ} (hBot : Tendsto F atBot (𝓝 M)) : ∀x,F x=M := by
  let H : ℝ → ℝ := fun x => F x-M
  let C : ℝ := B+|M|
  have hB : 0≤B := (norm_nonneg (F 0)).trans (hb 0)
  have hC : 0≤C := add_nonneg hB (abs_nonneg M)
  have hHm : Measurable H := hm.sub measurable_const
  have hHb : ∀x,‖H x‖≤C := by
    intro x
    dsimp [H,C]
    calc
      _≤‖F x‖+‖M‖ := norm_sub_le _ _
      _≤B+|M| := by rw [Real.norm_eq_abs M];exact add_le_add (hb x) le_rfl
  have hHBot : Tendsto H atBot (𝓝 0) := by
    simpa only [H,sub_self] using hBot.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => M) atBot (𝓝 M))
  have hOne : (fun x => renewalAverage μ H 1 x)=H := by
    funext x
    change (∫ y,(F (x-y)-M) ∂convPow μ 1)=F x-M
    rw [convPow_one,integral_sub]
    · rw [←hHarm x,integral_const]
      simp
    · exact Integrable.of_bound ((hm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable) B
        (Eventually.of_forall fun y => hb (x-y))
    · exact integrable_const M
  intro x
  have hAvg : ∀n : ℕ,renewalAverage μ H n x=H x := by
    intro n
    induction n with
    | zero => simp only [renewalAverage,convPow_zero,integral_dirac,sub_zero]
    | succ n ih => rw [renewalAverage_succ μ H hHm C hHb,hOne,ih]
  have hrem := renewalAverage_tendsto_zero μ 1 (by norm_num)
    (KeyRenewal.expTransform_lt_one_of_positive_support (by norm_num : (0:ℝ)<1) hp)
    H hHm C hC hHb hHBot x
  have hz : H x=0 := tendsto_nhds_unique tendsto_const_nhds
    (hrem.congr' (Eventually.of_forall fun n => hAvg n))
  change F x-M=0 at hz
  linarith

/-- A fully proved source-nonarithmetic maximum principle. This is a
renewal proof ingredient, not an assumed constant-limit conclusion. -/
theorem positive_nonarithmetic_harmonic_maximum_constant {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hna : ¬Arithmetic μ) {F : ℝ → ℝ}
    (huc : UniformContinuous F) (B : ℝ) (hb : ∀x,‖F x‖≤B)
    (hHarm : ∀x : ℝ,F x=∫ y,F (x-y) ∂μ) (x₀ : ℝ) (hMax : ∀x,F x≤F x₀) :
    ∀x : ℝ,F x=F x₀ :=
  bounded_harmonic_constant_of_atBot hp huc.continuous.measurable B hb hHarm
    (harmonic_maximum_tendsto_atBot hp hna huc B hb hHarm x₀ hMax)

end
end SphericalAging.PositiveRenewalHarmonicMaximum
