module

public import SphericalAging.ActualOverlapTimeModulus
public import SphericalAging.ActualBrownianPrimitiveTimeModulus
public import SphericalAging.ResponseCompactness

public section

/-! Genuine dimension-uniform time moduli give actual Arzelà–Ascoli
extraction of correlation means and Brownian response primitives. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualMeanKernelTimeCompactness
open HardSphereDynamics ActualStateIncrementMoments ActualModelOverlapVariance
  ActualOverlapTimeModulus ActualBrownianPrimitiveTimeModulus
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def overlapMean (β R : ℝ≥0) (hR : 0<(R : ℝ)) (z : ℝ≥0×ℝ≥0) : ℝ :=
  ∫ ω,actualOverlap (N := N) (p := p) β R hR z.1 z.2 ω ∂AnnealedModelLaw.law N p

@[expose] def gammaMean (β R : ℝ≥0) (hR : 0<(R : ℝ)) (z : ℝ≥0×ℝ≥0) : ℝ :=
  ∫ ω,actualGamma (N := N) (p := p) β R hR z.1 z.2 ω ∂AnnealedModelLaw.law N p

@[expose] def overlapUpModulus (p : ℕ) (β : ℝ≥0) (u v : ℝ≥0) : ℝ :=
  Real.sqrt (2*incrementCeiling p β u+2*incrementCeiling p β v)

@[expose] def gammaUpModulus (p : ℕ) (β s u v : ℝ≥0) : ℝ :=
  Real.sqrt ((v : ℝ)+2*Real.sqrt 3*(s : ℝ)*Real.sqrt (incrementCeiling p β u))

@[expose] def overlapModulus (p : ℕ) (β : ℝ≥0) (z w : ℝ≥0×ℝ≥0) : ℝ :=
  overlapUpModulus p β (max z.1 w.1-z.1) (max z.2 w.2-z.2)+
  overlapUpModulus p β (max z.1 w.1-w.1) (max z.2 w.2-w.2)

@[expose] def gammaModulus (p : ℕ) (β : ℝ≥0) (z w : ℝ≥0×ℝ≥0) : ℝ :=
  gammaUpModulus p β z.2 (max z.1 w.1-z.1) (max z.2 w.2-z.2)+
  gammaUpModulus p β w.2 (max z.1 w.1-w.1) (max z.2 w.2-w.2)

lemma overlapModulus_continuous (p : ℕ) (β : ℝ≥0) (z : ℝ≥0×ℝ≥0) :
    Continuous (overlapModulus p β z) := by
  unfold overlapModulus overlapUpModulus incrementCeiling
  fun_prop

lemma gammaModulus_continuous (p : ℕ) (β : ℝ≥0) (z : ℝ≥0×ℝ≥0) :
    Continuous (gammaModulus p β z) := by
  unfold gammaModulus gammaUpModulus incrementCeiling
  fun_prop

lemma overlapModulus_self (p : ℕ) (β : ℝ≥0) (z : ℝ≥0×ℝ≥0) : overlapModulus p β z z=0 := by
  simp [overlapModulus,overlapUpModulus,incrementCeiling]

lemma gammaModulus_self (p : ℕ) (β : ℝ≥0) (z : ℝ≥0×ℝ≥0) : gammaModulus p β z z=0 := by
  simp [gammaModulus,gammaUpModulus,incrementCeiling]

 theorem overlapMean_difference_le (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (z w : ℝ≥0×ℝ≥0) :
    |overlapMean (N := N) (p := p) β R hR z-overlapMean (N := N) (p := p) β R hR w|≤overlapModulus p β z w := by
  let m : ℝ≥0×ℝ≥0 := (max z.1 w.1,max z.2 w.2)
  have hz := actual_overlap_mean_two_time_modulus hN hp β R hR hNR z.1 z.2
    (m.1-z.1) (m.2-z.2)
  have hw := actual_overlap_mean_two_time_modulus hN hp β R hR hNR w.1 w.2
    (m.1-w.1) (m.2-w.2)
  have hza : z.1+(m.1-z.1)=m.1 := add_tsub_cancel_of_le (le_max_left _ _)
  have hzb : z.2+(m.2-z.2)=m.2 := add_tsub_cancel_of_le (le_max_left _ _)
  have hwa : w.1+(m.1-w.1)=m.1 := add_tsub_cancel_of_le (le_max_right _ _)
  have hwb : w.2+(m.2-w.2)=m.2 := add_tsub_cancel_of_le (le_max_right _ _)
  rw [hza,hzb] at hz
  rw [hwa,hwb] at hw
  change |overlapMean (N := N) (p := p) β R hR m-overlapMean (N := N) (p := p) β R hR z|≤_ at hz
  change |overlapMean (N := N) (p := p) β R hR m-overlapMean (N := N) (p := p) β R hR w|≤_ at hw
  rw [abs_sub_comm] at hz
  exact (abs_sub_le (overlapMean (N := N) (p := p) β R hR z) (overlapMean (N := N) (p := p) β R hR m)
    (overlapMean (N := N) (p := p) β R hR w)).trans (add_le_add hz hw)

 theorem gammaMean_difference_le (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (z w : ℝ≥0×ℝ≥0) :
    |gammaMean (N := N) (p := p) β R hR z-gammaMean (N := N) (p := p) β R hR w|≤gammaModulus p β z w := by
  let m : ℝ≥0×ℝ≥0 := (max z.1 w.1,max z.2 w.2)
  have hz := actualGamma_mean_two_time_modulus hN hp β R hR hNR z.1 z.2
    (m.1-z.1) (m.2-z.2)
  have hw := actualGamma_mean_two_time_modulus hN hp β R hR hNR w.1 w.2
    (m.1-w.1) (m.2-w.2)
  have hza : z.1+(m.1-z.1)=m.1 := add_tsub_cancel_of_le (le_max_left _ _)
  have hzb : z.2+(m.2-z.2)=m.2 := add_tsub_cancel_of_le (le_max_left _ _)
  have hwa : w.1+(m.1-w.1)=m.1 := add_tsub_cancel_of_le (le_max_right _ _)
  have hwb : w.2+(m.2-w.2)=m.2 := add_tsub_cancel_of_le (le_max_right _ _)
  rw [hza,hzb] at hz
  rw [hwa,hwb] at hw
  change |gammaMean (N := N) (p := p) β R hR m-gammaMean (N := N) (p := p) β R hR z|≤_ at hz
  change |gammaMean (N := N) (p := p) β R hR m-gammaMean (N := N) (p := p) β R hR w|≤_ at hw
  rw [abs_sub_comm] at hz
  exact (abs_sub_le (gammaMean (N := N) (p := p) β R hR z) (gammaMean (N := N) (p := p) β R hR m)
    (gammaMean (N := N) (p := p) β R hR w)).trans (add_le_add hz hw)

 theorem actual_overlap_means_equicontinuous {A : Type*} (dim : A→ℕ) (hD : ∀ a,1≤dim a)
    (p : ℕ) (hp : 0<p) (β : ℝ≥0) (R : A→ℝ≥0) (hR : ∀ a,0<(R a : ℝ))
    (hNR : ∀ a,(dim a : ℝ)<(R a : ℝ)^2) :
    Equicontinuous (fun a z => overlapMean (N := dim a) (p := p) β (R a) (hR a) z) := by
  intro z
  apply Metric.equicontinuousAt_of_continuity_modulus (overlapModulus p β z)
    (by simpa only [overlapModulus_self] using (overlapModulus_continuous p β z).tendsto z)
  exact Eventually.of_forall (fun w a => by
    rw [Real.dist_eq]
    exact overlapMean_difference_le (hD a) hp β (R a) (hR a) (hNR a) z w)

 theorem actual_gamma_means_equicontinuous {A : Type*} (dim : A→ℕ) (hD : ∀ a,1≤dim a)
    (p : ℕ) (hp : 0<p) (β : ℝ≥0) (R : A→ℝ≥0) (hR : ∀ a,0<(R a : ℝ))
    (hNR : ∀ a,(dim a : ℝ)<(R a : ℝ)^2) :
    Equicontinuous (fun a z => gammaMean (N := dim a) (p := p) β (R a) (hR a) z) := by
  intro z
  apply Metric.equicontinuousAt_of_continuity_modulus (gammaModulus p β z)
    (by simpa only [gammaModulus_self] using (gammaModulus_continuous p β z).tendsto z)
  exact Eventually.of_forall (fun w a => by
    rw [Real.dist_eq]
    exact gammaMean_difference_le (hD a) hp β (R a) (hR a) (hNR a) z w)

end SphericalAging.ActualMeanKernelTimeCompactness
