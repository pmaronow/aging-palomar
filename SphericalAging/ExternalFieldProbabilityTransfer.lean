module

public import SphericalAging.ExternalFieldFiniteCover
public import SphericalAging.HamiltonianBallBounds
public import SphericalAging.SphereBadEventFisherMass
public import SphericalAging.SphereGibbsEntropy

public section

/-! Genuine finite-field/probability transfer of the preceding published
external-field theorem 10.1. The external research input concerns only
single-field probability tails; the positive absolute-overlap mean penalty
is derived from actual Gaussian landscape moments and constructed finite
field covers. This auxiliary bound uses elementaryPenalty; the sharp beta_d coefficient
is proved separately in ExternalFieldSharpFiniteCover. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ExternalFieldProbabilityTransfer
open Set Filter MeasureTheory FiniteModel GaussianLandscape GaussianLandscapeMoments
open ExternalFieldElementaryPenalty ExternalFieldFiniteCover HamiltonianBallBounds
open SphereBadEventFisherMass SphereGibbsEntropy
open scoped Topology BigOperators InnerProductSpace

@[expose]  def badFields {N p : ℕ} (G : Finset ℝ) (e a : Disorder N p→ℝ) (η : ℝ) : Set (Disorder N p) :=
  ⋃κ∈G,{J | algorithmicField p κ+η≤e J+κ*|a J|}

 theorem badFields_measurable {N p : ℕ} (G : Finset ℝ) {e a : Disorder N p→ℝ} (η : ℝ)
    (he : Measurable e) (ha : Measurable a) : MeasurableSet (badFields G e a η) := by
  exact MeasurableSet.biUnion (to_countable _) (fun κ _ =>
    measurableSet_le measurable_const (he.add (measurable_const.mul (continuous_abs.measurable.comp ha))))

 theorem badFields_probability_tendsto_zero {p : ℕ} (G : Finset ℝ) (hG : ∀κ∈G,0≤κ)
    (dim : ℕ→ℕ) (e a : ∀n,Disorder (dim n) p→ℝ) {η : ℝ} (hη : 0<η)
    (htail : ∀κ∈G,
      Tendsto (fun n => (disorderLaw (dim n) p).real {J | algorithmicField p κ+η≤e n J+κ*a n J}) atTop (𝓝 0) ∧
      Tendsto (fun n => (disorderLaw (dim n) p).real {J | algorithmicField p κ+η≤e n J-κ*a n J}) atTop (𝓝 0)) :
    Tendsto (fun n => (disorderLaw (dim n) p).real (badFields G (e n) (a n) η)) atTop (𝓝 0) := by
  have hs n : badFields G (e n) (a n) η⊆⋃κ∈G,
      {J | algorithmicField p κ+η≤e n J+κ*a n J}∪
      {J | algorithmicField p κ+η≤e n J-κ*a n J} := by
    intro J hJ
    obtain ⟨κ,hκ⟩ := mem_iUnion.mp hJ
    obtain ⟨hk,hcost⟩ := mem_iUnion.mp hκ
    refine mem_iUnion.mpr ⟨κ,mem_iUnion.mpr ⟨hk,?_⟩⟩
    by_cases ha : 0≤a n J
    · exact Or.inl (by simpa only [mem_setOf_eq,abs_of_nonneg ha] using hcost)
    · exact Or.inr (by simpa only [mem_setOf_eq,abs_of_neg (lt_of_not_ge ha),mul_neg,sub_eq_add_neg] using hcost)
  have hb n : (disorderLaw (dim n) p).real (badFields G (e n) (a n) η)≤
      ∑κ∈G,((disorderLaw (dim n) p).real {J | algorithmicField p κ+η≤e n J+κ*a n J}+
        (disorderLaw (dim n) p).real {J | algorithmicField p κ+η≤e n J-κ*a n J}) := by
    exact ((measureReal_mono (μ:=disorderLaw (dim n) p) (hs n) (measure_ne_top _ _)).trans
      (measureReal_biUnion_finset_le (μ:=disorderLaw (dim n) p) G _)).trans
      (Finset.sum_le_sum (fun κ _ => measureReal_union_le (μ:=disorderLaw (dim n) p) _ _))
  have ht := tendsto_finsetSum G (fun κ hk => (htail κ hk).1.add (htail κ hk).2)
  apply squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) (Eventually.of_forall hb)
  simpa only [add_zero,Finset.sum_const_zero] using ht

 theorem landscape_bad_mass_tendsto_zero {p : ℕ} (hp : 0<p) (dim : ℕ→ℕ)
    (hDim : ∀n,1≤dim n) (B : ∀n,Set (Disorder (dim n) p)) (hB : ∀n,MeasurableSet (B n))
    (hprob : Tendsto (fun n => (disorderLaw (dim n) p).real (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫J : Disorder (dim n) p,(B n).indicator (landscapeNorm (dim n) p) J
      ∂disorderLaw (dim n) p) atTop (𝓝 0) := by
  have hb n : (∫J : Disorder (dim n) p,(B n).indicator (landscapeNorm (dim n) p) J
      ∂disorderLaw (dim n) p)≤Real.sqrt (momentCeiling p 2)*
        Real.sqrt ((disorderLaw (dim n) p).real (B n)) := by
    have hm := uniform_real_power_moment (hDim n) hp (k:=2) (by norm_num)
    simp only [Real.rpow_two] at hm
    exact (event_integral_le_sqrt_moment_probability (disorderLaw (dim n) p)
      (landscapeNorm_continuous (dim n) p).aestronglyMeasurable hm.1
      (landscapeNorm_nonnegative (dim n) p) (B n) (hB n)).trans
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hm.2) (Real.sqrt_nonneg _))
  have hn n : 0≤∫J : Disorder (dim n) p,(B n).indicator (landscapeNorm (dim n) p) J
      ∂disorderLaw (dim n) p := integral_nonneg (fun J => show (0:ℝ)≤(B n).indicator (landscapeNorm (dim n) p) J from by
    by_cases hJ : J∈B n
    · simpa only [indicator_of_mem hJ] using landscapeNorm_nonnegative (dim n) p J
    · simp only [indicator_of_notMem hJ,Pi.zero_apply,le_refl])
  apply squeeze_zero' (Eventually.of_forall hn) (Eventually.of_forall hb)
  simpa only [Real.sqrt_zero,mul_zero,Function.comp_def] using
    ((Real.continuous_sqrt.tendsto 0).comp hprob).const_mul (Real.sqrt (momentCeiling p 2))

/-- Annealed transfer from the genuine preceding single-field probability
input. Bounds used here are the actual ball Hamiltonian and overlap bounds;
the stronger sharp coefficient is not assumed. -/
 theorem positive_penalty_mean_of_field_tails {p : ℕ} (hp : 3≤p) (dim : ℕ→ℕ)
    (hDim : ∀n,1≤dim n) (e a : ∀n,Disorder (dim n) p→ℝ)
    (he : ∀n,Measurable (e n)) (ha : ∀n,Measurable (a n))
    (heBound : ∀n J,|e n J|≤landscapeNorm (dim n) p J)
    (haBound : ∀n J,|a n J|≤1)
    (htail : ∀κ≥0,∀η>0,
      Tendsto (fun n => (disorderLaw (dim n) p).real {J | algorithmicField p κ+η≤e n J+κ*a n J}) atTop (𝓝 0) ∧
      Tendsto (fun n => (disorderLaw (dim n) p).real {J | algorithmicField p κ+η≤e n J-κ*a n J}) atTop (𝓝 0)) :
    ∀ε>0,∀ᶠn in atTop,
      (∫J : Disorder (dim n) p,e n J+elementaryPenalty p*|a n J|^p ∂disorderLaw (dim n) p)
        ≤thresholdEnergy p+ε := by
  intro ε hε
  obtain ⟨G,hG0,hG,hcover⟩ := exists_finite_fields hp (show 0<ε/4 by linarith)
  let B : ∀n,Set (Disorder (dim n) p) := fun n => badFields G (e n) (a n) (ε/4)
  have hB n : MeasurableSet (B n) := badFields_measurable G _ (he n) (ha n)
  have hprob : Tendsto (fun n => (disorderLaw (dim n) p).real (B n)) atTop (𝓝 0) :=
    badFields_probability_tendsto_zero G (fun κ hk => (hG κ hk).1) dim e a
      (show 0<ε/4 by linarith) (fun κ hk => htail κ (hG κ hk).1 _ (by linarith))
  have hbad := landscape_bad_mass_tendsto_zero (show 0<p by omega) dim hDim B hB hprob
  have herr : Tendsto (fun n => (∫J : Disorder (dim n) p,(B n).indicator
      (landscapeNorm (dim n) p) J ∂disorderLaw (dim n) p)+
      elementaryPenalty p*(disorderLaw (dim n) p).real (B n)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using hbad.add (hprob.const_mul (elementaryPenalty p))
  have hα : 0≤elementaryPenalty p := (elementaryPenalty_positive hp).le
  have hE : 0≤thresholdEnergy p := by unfold thresholdEnergy;positivity
  filter_upwards [herr.eventually (eventually_lt_nhds (show (0:ℝ)<ε/2 by linarith))] with n hn
  have hNn : 0<dim n := lt_of_lt_of_le Nat.zero_lt_one (hDim n)
  have hQi := landscapeNorm_integrable hNn (show 1≤p by omega)
  have hei : Integrable (e n) (disorderLaw (dim n) p) := hQi.mono'
    (he n).aestronglyMeasurable (Eventually.of_forall (fun J => by simpa only [Real.norm_eq_abs] using heBound n J))
  have hai : Integrable (fun J => |a n J|^p) (disorderLaw (dim n) p) :=
    (integrable_const (1:ℝ)).mono'
      ((continuous_abs.measurable.comp (ha n)).pow_const p).aestronglyMeasurable
      (Eventually.of_forall (fun J => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        exact pow_le_one₀ (abs_nonneg _) (haBound n J)))
  have hci := hei.add (hai.const_mul (elementaryPenalty p))
  have hbi := (hQi.add (integrable_const (elementaryPenalty p))).indicator (hB n)
  have hpoint J : e n J+elementaryPenalty p*|a n J|^p≤thresholdEnergy p+ε/2+
      (B n).indicator (fun J => landscapeNorm (dim n) p J+elementaryPenalty p) J := by
    by_cases hJ : J∈B n
    · rw [indicator_of_mem hJ]
      have heJ := (le_abs_self (e n J)).trans (heBound n J)
      have haJ : elementaryPenalty p*|a n J|^p≤elementaryPenalty p :=
        mul_le_of_le_one_right hα (pow_le_one₀ (abs_nonneg _) (haBound n J))
      linarith
    · rw [indicator_of_notMem hJ]
      obtain ⟨κ,hκ,hcost⟩ := hcover |a n J| ⟨abs_nonneg _,haBound n J⟩
      have hnot : ¬algorithmicField p κ+ε/4≤e n J+κ*|a n J| := by
        intro hx
        exact hJ (mem_iUnion.mpr ⟨κ,mem_iUnion.mpr ⟨hκ,hx⟩⟩)
      have hx := lt_of_not_ge hnot
      linarith
  have hi := integral_mono hci ((integrable_const (thresholdEnergy p+ε/2)).add hbi) hpoint
  have heq : (∫J : Disorder (dim n) p,thresholdEnergy p+ε/2+
      (B n).indicator (fun J => landscapeNorm (dim n) p J+elementaryPenalty p) J ∂disorderLaw (dim n) p)=
      thresholdEnergy p+ε/2+(∫J : Disorder (dim n) p,(B n).indicator
        (landscapeNorm (dim n) p) J ∂disorderLaw (dim n) p)+
        elementaryPenalty p*(disorderLaw (dim n) p).real (B n) := by
    have hh := integral_add (f:=fun _ : Disorder (dim n) p => thresholdEnergy p+ε/2)
      (g:=(B n).indicator (fun J => landscapeNorm (dim n) p J+elementaryPenalty p))
      (integrable_const _) hbi
    have ha := integral_add (f:=(B n).indicator (landscapeNorm (dim n) p))
      (g:=(B n).indicator (fun _ => elementaryPenalty p))
      (hQi.indicator (hB n)) ((integrable_const _).indicator (hB n))
    have hx := congrArg (fun f : Disorder (dim n) p→ℝ => ∫J,f J ∂disorderLaw (dim n) p)
      (indicator_add (B n) (landscapeNorm (dim n) p) (fun _ => elementaryPenalty p))
    have hz := hx.trans ha
    rw [integral_indicator_const _ (hB n)] at hz
    rw [integral_const] at hh
    simp only [probReal_univ,one_smul] at hh
    calc
      _ = thresholdEnergy p+ε/2+(∫J : Disorder (dim n) p,
        (B n).indicator (fun J => landscapeNorm (dim n) p J+elementaryPenalty p) J ∂disorderLaw (dim n) p) := hh
      _ = _ := by rw [hz];simp only [smul_eq_mul];ring
  change (∫J : Disorder (dim n) p,e n J+elementaryPenalty p*|a n J|^p ∂disorderLaw (dim n) p)≤
    (∫J : Disorder (dim n) p,thresholdEnergy p+ε/2+
      (B n).indicator (fun J => landscapeNorm (dim n) p J+elementaryPenalty p) J ∂disorderLaw (dim n) p) at hi
  rw [heq] at hi
  linarith

@[expose]  def ballEnergy {N p : ℕ} (A : Disorder N p→Vector N) (J : Disorder N p) : ℝ :=
  Hamiltonian N p J (A J)/(N:ℝ)
@[expose]  def ballOverlap {N p : ℕ} (w : Vector N) (A : Disorder N p→Vector N) (J : Disorder N p) : ℝ :=
  ⟪w,A J⟫_ℝ/(N:ℝ)

 theorem ballEnergy_measurable {N p : ℕ} {A : Disorder N p→Vector N} (hA : Measurable A) :
    Measurable (ballEnergy A) :=
  ((Hamiltonian_joint_continuous N p).measurable.comp (measurable_id.prodMk hA)).div_const _
 theorem ballOverlap_measurable {N p : ℕ} (w : Vector N) {A : Disorder N p→Vector N} (hA : Measurable A) :
    Measurable (ballOverlap w A) := (((continuous_const.inner continuous_id).measurable).comp hA).div_const _

 /-- Actual Gaussian ball-valued algorithm mean-cost bound from the preceding
 external-field research input only. -/
 theorem actual_ball_algorithm_positive_penalty {p : ℕ} (hp : 3≤p) (dim : ℕ→ℕ)
    (hDim : ∀n,1≤dim n) (w : ∀n,Vector (dim n)) (hw : ∀n,‖w n‖=Real.sqrt (dim n))
    (A : ∀n,Disorder (dim n) p→Vector (dim n)) (hA : ∀n,Measurable (A n))
    (hBall : ∀n J,‖A n J‖≤Real.sqrt (dim n))
    (htail : ∀κ≥0,∀η>0,
      Tendsto (fun n => (disorderLaw (dim n) p).real
        {J | algorithmicField p κ+η≤ballEnergy (A n) J+κ*ballOverlap (w n) (A n) J}) atTop (𝓝 0) ∧
      Tendsto (fun n => (disorderLaw (dim n) p).real
        {J | algorithmicField p κ+η≤ballEnergy (A n) J-κ*ballOverlap (w n) (A n) J}) atTop (𝓝 0)) :
    ∀ε>0,∀ᶠn in atTop,
      (∫J : Disorder (dim n) p,ballEnergy (A n) J+
        elementaryPenalty p*|ballOverlap (w n) (A n) J|^p ∂disorderLaw (dim n) p)
        ≤thresholdEnergy p+ε := by
  apply positive_penalty_mean_of_field_tails hp dim hDim (fun n => ballEnergy (A n))
    (fun n => ballOverlap (w n) (A n)) (fun n => ballEnergy_measurable (hA n))
    (fun n => ballOverlap_measurable (w n) (hA n)) _ _ htail
  · intro n J
    have hNn : 0<dim n := lt_of_lt_of_le Nat.zero_lt_one (hDim n)
    simpa only [ballEnergy,abs_div,abs_of_pos (show 0<(dim n:ℝ) by exact_mod_cast hNn)] using
      Hamiltonian_ball_bound hNn (show 1≤p by omega) J (hBall n J)
  · intro n J
    have hNn : 0<dim n := lt_of_lt_of_le Nat.zero_lt_one (hDim n)
    exact overlap_abs_le_one hNn (w n) (A n J) (hw n) (hBall n J)

end SphericalAging.ExternalFieldProbabilityTransfer
