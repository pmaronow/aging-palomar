module

public import SphericalAging.ExternalFieldProbabilityTransfer
public import SphericalAging.ExternalFieldSharpFiniteCover

public section

/-! True sharp all-p absolute-overlap expectation bound from preceding
single-field probability tails. All finite cover and Gaussian bad-event
estimates are derived, with the literal beta_d coefficient. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ExternalFieldSharpProbabilityTransfer
open Set Filter MeasureTheory FiniteModel GaussianLandscape GaussianLandscapeMoments
open ExternalFieldElementaryPenalty ExternalFieldSharpScalar
open ExternalFieldProbabilityTransfer HamiltonianBallBounds SphereGibbsEntropy
open scoped Topology BigOperators InnerProductSpace

 theorem sharp_penalty_mean_of_field_tails {p : ℕ} (hp : 3≤p) (dim : ℕ→ℕ)
    (hDim : ∀n,1≤dim n) (e a : ∀n,Disorder (dim n) p→ℝ)
    (he : ∀n,Measurable (e n)) (ha : ∀n,Measurable (a n))
    (heBound : ∀n J,|e n J|≤landscapeNorm (dim n) p J)
    (haBound : ∀n J,|a n J|≤1)
    (htail : ∀κ≥0,∀η>0,
      Tendsto (fun n => (disorderLaw (dim n) p).real {J | algorithmicField p κ+η≤e n J+κ*a n J}) atTop (𝓝 0) ∧
      Tendsto (fun n => (disorderLaw (dim n) p).real {J | algorithmicField p κ+η≤e n J-κ*a n J}) atTop (𝓝 0)) :
    ∀ε>0,∀ᶠn in atTop,
      (∫J : Disorder (dim n) p,e n J+betaD p*|a n J|^p ∂disorderLaw (dim n) p)
        ≤thresholdEnergy p+ε := by
  intro ε hε
  obtain ⟨G,hG0,hG,hcover⟩ := ExternalFieldSharpFiniteCover.exists_finite_fields hp (show 0<ε/4 by linarith)
  let B : ∀n,Set (Disorder (dim n) p) := fun n => badFields G (e n) (a n) (ε/4)
  have hB n : MeasurableSet (B n) := badFields_measurable G _ (he n) (ha n)
  have hprob : Tendsto (fun n => (disorderLaw (dim n) p).real (B n)) atTop (𝓝 0) :=
    badFields_probability_tendsto_zero G (fun κ hk => hG κ hk) dim e a
      (show 0<ε/4 by linarith) (fun κ hk => htail κ (hG κ hk) _ (by linarith))
  have hbad := landscape_bad_mass_tendsto_zero (show 0<p by omega) dim hDim B hB hprob
  have herr : Tendsto (fun n => (∫J : Disorder (dim n) p,(B n).indicator
      (landscapeNorm (dim n) p) J ∂disorderLaw (dim n) p)+
      betaD p*(disorderLaw (dim n) p).real (B n)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using hbad.add (hprob.const_mul (betaD p))
  have hα : 0≤betaD p := (betaD_positive hp).le
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
  have hci := hei.add (hai.const_mul (betaD p))
  have hbi := (hQi.add (integrable_const (betaD p))).indicator (hB n)
  have hpoint J : e n J+betaD p*|a n J|^p≤thresholdEnergy p+ε/2+
      (B n).indicator (fun J => landscapeNorm (dim n) p J+betaD p) J := by
    by_cases hJ : J∈B n
    · rw [indicator_of_mem hJ]
      have heJ := (le_abs_self (e n J)).trans (heBound n J)
      have haJ : betaD p*|a n J|^p≤betaD p :=
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
      (B n).indicator (fun J => landscapeNorm (dim n) p J+betaD p) J ∂disorderLaw (dim n) p)=
      thresholdEnergy p+ε/2+(∫J : Disorder (dim n) p,(B n).indicator
        (landscapeNorm (dim n) p) J ∂disorderLaw (dim n) p)+
        betaD p*(disorderLaw (dim n) p).real (B n) := by
    have hh := integral_add (f:=fun _ : Disorder (dim n) p => thresholdEnergy p+ε/2)
      (g:=(B n).indicator (fun J => landscapeNorm (dim n) p J+betaD p))
      (integrable_const _) hbi
    have ha := integral_add (f:=(B n).indicator (landscapeNorm (dim n) p))
      (g:=(B n).indicator (fun _ => betaD p))
      (hQi.indicator (hB n)) ((integrable_const _).indicator (hB n))
    have hx := congrArg (fun f : Disorder (dim n) p→ℝ => ∫J,f J ∂disorderLaw (dim n) p)
      (indicator_add (B n) (landscapeNorm (dim n) p) (fun _ => betaD p))
    have hz := hx.trans ha
    rw [integral_indicator_const _ (hB n)] at hz
    rw [integral_const] at hh
    simp only [probReal_univ,one_smul] at hh
    calc
      _ = thresholdEnergy p+ε/2+(∫J : Disorder (dim n) p,
        (B n).indicator (fun J => landscapeNorm (dim n) p J+betaD p) J ∂disorderLaw (dim n) p) := hh
      _ = _ := by rw [hz];simp only [smul_eq_mul];ring
  change (∫J : Disorder (dim n) p,e n J+betaD p*|a n J|^p ∂disorderLaw (dim n) p)≤
    (∫J : Disorder (dim n) p,thresholdEnergy p+ε/2+
      (B n).indicator (fun J => landscapeNorm (dim n) p J+betaD p) J ∂disorderLaw (dim n) p) at hi
  rw [heq] at hi
  linarith

 /-- Actual Gaussian ball-valued algorithm mean-cost bound from the preceding
 external-field research input only. -/
 theorem actual_ball_algorithm_sharp_penalty {p : ℕ} (hp : 3≤p) (dim : ℕ→ℕ)
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
        betaD p*|ballOverlap (w n) (A n) J|^p ∂disorderLaw (dim n) p)
        ≤thresholdEnergy p+ε := by
  apply sharp_penalty_mean_of_field_tails hp dim hDim (fun n => ballEnergy (A n))
    (fun n => ballOverlap (w n) (A n)) (fun n => ballEnergy_measurable (hA n))
    (fun n => ballOverlap_measurable (w n) (hA n)) _ _ htail
  · intro n J
    have hNn : 0<dim n := lt_of_lt_of_le Nat.zero_lt_one (hDim n)
    simpa only [ballEnergy,abs_div,abs_of_pos (show 0<(dim n:ℝ) by exact_mod_cast hNn)] using
      Hamiltonian_ball_bound hNn (show 1≤p by omega) J (hBall n J)
  · intro n J
    have hNn : 0<dim n := lt_of_lt_of_le Nat.zero_lt_one (hDim n)
    exact overlap_abs_le_one hNn (w n) (A n J) (hw n) (hBall n J)

end SphericalAging.ExternalFieldSharpProbabilityTransfer
