module

public import SphericalAging.StationaryConvolutionDerivative

public section

/-! The actual ideal residual and its finite memory expansion. -/

open Set MeasureTheory Filter
open scoped Topology

namespace SphericalAging.StationaryIdealResidual
noncomputable section
open StationaryNormalization StationaryPowerProfiles StationaryConvolutionDerivative

/-- Normalized polynomial memory, with the linear coefficient fixed to one. -/
@[expose] def polynomialMemory (n : ℕ) (lam : ℕ → ℝ) (y : ℝ) : ℝ :=
  y + ∑ j ∈ Finset.range n, lam j * y^(j+2)

/-- The plus sign is the manuscript's -[M(hf)*j_f] with j_f=-f'. -/
@[expose] def idealResidual (n : ℕ) (lam : ℕ → ℝ) (h : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  h*f t - (1-h)*polynomialMemory n lam (h*f t) +
    h*causalConvolution (fun s => polynomialMemory n lam (h*f s)) (deriv f) t

theorem idealResidual_source_formula (n : ℕ) (lam : ℕ → ℝ) (h : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    idealResidual n lam h f t = h*f t-(1-h)*polynomialMemory n lam (h*f t)-
      h*causalConvolution (fun s => polynomialMemory n lam (h*f s)) (fun s => -deriv f s) t := by
  unfold idealResidual causalConvolution
  simp only [mul_neg,intervalIntegral.integral_neg]
  ring

/-- Genuine integrability of every polynomial-memory convolution term. -/
theorem corrected_derivative_convolution_integrable (a ε t : ℝ) (j : ℕ) (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => correctedPower a ε (t-s)^j * deriv (correctedPower a ε) s) volume 0 t := by
  have hf := correctedPower_c1 a ε
  apply ContinuousOn.intervalIntegrable
  intro s hs
  have hs0 : -1<s := by rcases mem_uIcc.mp hs with hs | hs <;> linarith
  have hts : -1<t-s := by rcases mem_uIcc.mp hs with hs | hs <;> linarith
  exact (((hf.derivative _ hts).continuousAt.comp_of_eq
    (show ContinuousAt (fun s : ℝ => t-s) s by fun_prop) rfl).pow j |>.mul
      (hf.derivative_continuousAt s hs0)).continuousWithinAt

theorem corrected_memory_convolution_expansion (a ε h t : ℝ) (n : ℕ) (lam : ℕ → ℝ) (ht : 0 ≤ t) :
    causalConvolution (fun s => polynomialMemory n lam (h*correctedPower a ε s))
      (deriv (correctedPower a ε)) t =
      h*causalConvolution (correctedPower a ε) (deriv (correctedPower a ε)) t +
        ∑ j ∈ Finset.range n, lam j*h^(j+2)*
          causalConvolution (fun s => correctedPower a ε s^(j+2)) (deriv (correctedPower a ε)) t := by
  have h1 := corrected_derivative_convolution_integrable a ε t 1 ht
  simp only [pow_one] at h1
  have hsum : IntervalIntegrable (fun s => ∑ j ∈ Finset.range n,
      (lam j*h^(j+2))*(correctedPower a ε (t-s)^(j+2)*deriv (correctedPower a ε) s)) volume 0 t := by
    have hs := IntervalIntegrable.sum (Finset.range n) (fun j _ =>
      (corrected_derivative_convolution_integrable a ε t (j+2) ht).const_mul (lam j*h^(j+2)))
    convert hs using 1
    funext s
    simp only [Finset.sum_apply]
  unfold causalConvolution polynomialMemory
  have hi : (∫ s in 0..t, (h*correctedPower a ε (t-s)+∑ j ∈ Finset.range n,
      lam j*(h*correctedPower a ε (t-s))^(j+2))*deriv (correctedPower a ε) s) =
      ∫ s in 0..t, h*(correctedPower a ε (t-s)*deriv (correctedPower a ε) s)+
        ∑ j ∈ Finset.range n, (lam j*h^(j+2))*(correctedPower a ε (t-s)^(j+2)*deriv (correctedPower a ε) s) := by
    apply intervalIntegral.integral_congr
    intro s _
    simp only [add_mul,Finset.sum_mul,mul_pow]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  rw [hi,intervalIntegral.integral_add (h1.const_mul h) hsum,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum]
  · apply congrArg (fun y => h*(∫ s in 0..t,correctedPower a ε (t-s)*deriv (correctedPower a ε) s)+y)
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul]
  · intro j _
    exact (corrected_derivative_convolution_integrable a ε t (j+2) ht).const_mul _

/-- The exact unseparated ideal residual expansion used before the critical
quadratic coefficient and remainder are isolated. -/
theorem idealResidual_expansion (a ε h t : ℝ) (n : ℕ) (lam : ℕ → ℝ) (ht : 0 ≤ t) :
    idealResidual n lam h (correctedPower a ε) t =
      h^2*deriv (causalConvolution (correctedPower a ε) (correctedPower a ε)) t +
        ∑ j ∈ Finset.range n, lam j*
          (-h^(j+2)*correctedPower a ε t^(j+2)+h^(j+3)*
            deriv (causalConvolution (fun s => correctedPower a ε s^(j+2)) (correctedPower a ε)) t) := by
  have hd1 := corrected_power_convolution_derivative_identity a ε t 1 ht
  simp only [pow_one] at hd1
  unfold idealResidual
  rw [corrected_memory_convolution_expansion a ε h t n lam ht]
  unfold polynomialMemory
  rw [hd1]
  simp only [mul_pow]
  have hd j := corrected_power_convolution_derivative_identity a ε t (j+2) ht
  simp_rw [hd]
  have hsum : (∑ j ∈ Finset.range n, lam j*
      (-h^(j+2)*correctedPower a ε t^(j+2)+h^(j+3)*
        (correctedPower a ε t^(j+2)+causalConvolution (fun s => correctedPower a ε s^(j+2)) (deriv (correctedPower a ε)) t))) =
      -(1-h)*(∑ j ∈ Finset.range n,lam j*(h^(j+2)*correctedPower a ε t^(j+2)))+
        h*(∑ j ∈ Finset.range n,lam j*h^(j+2)*causalConvolution (fun s => correctedPower a ε s^(j+2)) (deriv (correctedPower a ε)) t) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [show j+3=(j+2)+1 by omega,pow_succ]
    ring
  rw [hsum]
  ring


/-- Causal convolution is commutative by actual interval reflection. -/
theorem causal_convolution_comm (F G : ℝ → ℝ) (t : ℝ) :
    causalConvolution F G t = causalConvolution G F t := by
  have hi := intervalIntegral.integral_comp_sub_mul (fun s => F (t-s)*G s)
    (by norm_num : (1:ℝ) ≠ 0) t (a:=0) (b:=t)
  simp only [one_mul,inv_one,one_smul,sub_self,sub_zero,sub_sub_cancel] at hi
  unfold causalConvolution
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro s _
  change F s*G (t-s)=G (t-s)*F s
  ring

@[expose] def correctedQuadraticResidual (a ε t : ℝ) : ℝ :=
  deriv (causalConvolution (correctedPower a ε) (correctedPower a ε)) t -
    CriticalEndpoint.exponentCoefficient a*correctedPower a ε t^2

/-- The exact quadratic expansion of Lemma16.6, with actual derivatives. -/
theorem corrected_quadratic_expansion (a ε t : ℝ) (ht : 0 ≤ t) :
    correctedQuadraticResidual a ε t =
      (1+ε)^2*StationaryShiftedResidual.quadraticResidual a t -
        2*ε*(1+ε)*StationaryPowerAsymptotics.crossResidual a t +
          ε^2*StationaryPowerAsymptotics.quarticResidual a t := by
  have he := StationaryHigherPowerBound.corrected_power_convolution_derivative a ε t 1 (by linarith)
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.choose_zero_right,Nat.choose_self,
    StationaryHigherPowerBound.correctedPowCoefficient,Nat.cast_one,one_mul,mul_one,
    pow_zero,pow_one,add_zero,Nat.sub_self,Nat.sub_zero] at he
  have hcomm : deriv (causalConvolution (fun s => shiftedPower a s^2) (shiftedPower a)) t =
      deriv (causalConvolution (shiftedPower a) (fun s => shiftedPower a s^2)) t := by
    apply congrArg (fun f : ℝ → ℝ => deriv f t)
    funext s
    exact causal_convolution_comm _ _ s
  unfold correctedQuadraticResidual
  rw [he,hcomm]
  unfold correctedPower StationaryShiftedResidual.quadraticResidual
    StationaryPowerAsymptotics.crossResidual StationaryPowerAsymptotics.quarticResidual
  ring


@[expose] def idealRemainder (a ε h : ℝ) (n : ℕ) (lam : ℕ → ℝ) (t : ℝ) : ℝ :=
  CriticalEndpoint.exponentCoefficient a*h^3*
    deriv (causalConvolution (fun s => correctedPower a ε s^2) (correctedPower a ε)) t +
      ∑ j ∈ Finset.range n, lam (j+1)*
        (-h^(j+3)*correctedPower a ε t^(j+3)+h^(j+4)*
          deriv (causalConvolution (fun s => correctedPower a ε s^(j+3)) (correctedPower a ε)) t)

/-- The exact manuscript ideal expansion with its actual memory remainder. -/
theorem idealResidual_critical_expansion (a ε h t : ℝ) (n : ℕ) (lam : ℕ → ℝ)
    (hθ : lam 0 = CriticalEndpoint.exponentCoefficient a) (ht : 0 ≤ t) :
    idealResidual (n+1) lam h (correctedPower a ε) t =
      h^2*correctedQuadraticResidual a ε t + idealRemainder a ε h n lam t := by
  rw [idealResidual_expansion a ε h t (n+1) lam ht,Finset.sum_range_succ']
  simp only [zero_add,add_assoc,hθ]
  unfold correctedQuadraticResidual idealRemainder
  ring


/-- Every higher-power remainder term obeys the uniform critical cubic bound. -/
theorem higher_remainder_term_bound (a ε h t K : ℝ) (j : ℕ)
    (ha : 0 < a) (hε : |ε| ≤ 1/4) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (ht : 0 ≤ t) (hj : 3 ≤ j)
    (_hK : 0 ≤ K)
    (hd : |deriv (causalConvolution (fun s => correctedPower a ε s^j) (correctedPower a ε)) t| ≤ K*shiftedPower a t^3) :
    |-h^j*correctedPower a ε t^j+h^(j+1)*
      deriv (causalConvolution (fun s => correctedPower a ε s^j) (correctedPower a ε)) t| ≤
      ((5/4:ℝ)^3+K)*h^3*shiftedPower a t^3 := by
  have hf0 := (correctedPower_pos a ε t ha.le hε ht).le
  have hf1 := ((correctedPower_admissible a ε ha hε).values t ht).2
  have hfb := (correctedPower_bounds a ε t ha.le hε ht).2
  have hfp : correctedPower a ε t^j ≤ (5/4:ℝ)^3*shiftedPower a t^3 := by
    calc
      _ ≤ correctedPower a ε t^3 := pow_le_pow_of_le_one hf0 hf1 hj
      _ ≤ ((5/4:ℝ)*shiftedPower a t)^3 := pow_le_pow_left₀ hf0 hfb 3
      _ = _ := by rw [mul_pow]
  have hhj := pow_le_pow_of_le_one hh0 hh1 hj
  have hhjp := pow_le_pow_of_le_one hh0 hh1 (show 3 ≤ j+1 by omega)
  calc
    _ ≤ |h^j*correctedPower a ε t^j|+|h^(j+1)*
      deriv (causalConvolution (fun s => correctedPower a ε s^j) (correctedPower a ε)) t| := by
      simpa only [neg_mul,abs_neg] using abs_add_le (-h^j*correctedPower a ε t^j)
        (h^(j+1)*deriv (causalConvolution (fun s => correctedPower a ε s^j) (correctedPower a ε)) t)
    _ ≤ h^3*((5/4:ℝ)^3*shiftedPower a t^3)+h^3*(K*shiftedPower a t^3) := by
      rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hh0 _),abs_of_nonneg (pow_nonneg hh0 _),
        abs_of_nonneg (pow_nonneg hf0 _)]
      exact add_le_add (mul_le_mul hhj hfp (pow_nonneg hf0 _) (pow_nonneg hh0 _))
        (mul_le_mul hhjp hd (abs_nonneg _) (pow_nonneg hh0 _))
    _ = _ := by ring

/-- Exact uniform O(h³g³) bound for the actual ideal memory remainder. -/
theorem idealRemainder_bound (a : ℝ) (n : ℕ) (lam : ℕ → ℝ)
    (ha0 : 0 < a) (ha1 : a < 1/2) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ ε : ℝ, |ε| ≤ 1/4 → ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      ∀ t ≥ 0, |idealRemainder a ε h n lam t| ≤ K₀*h^3*shiftedPower a t^3 := by
  have hb (j : ℕ) := StationaryHigherPowerBound.corrected_higher_convolution_bound
    a (j+2) ha0 ha1 (by omega)
  choose K hK hbound using hb
  let C := |CriticalEndpoint.exponentCoefficient a| *K 0 +
    ∑ j ∈ Finset.range n, |lam (j+1)| *((5/4:ℝ)^3+K (j+1))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (mul_nonneg (abs_nonneg _) (hK 0).le)
      (Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _)
        (add_nonneg (by norm_num) (hK (j+1)).le)))
  refine ⟨C+1,by positivity,?_⟩
  intro ε hε h hh0 hh1 t ht
  have hg := pow_nonneg (shiftedPower_pos a t ht).le 3
  have hh := pow_nonneg hh0 3
  have hfirst : |CriticalEndpoint.exponentCoefficient a*h^3*
      deriv (causalConvolution (fun s => correctedPower a ε s^2) (correctedPower a ε)) t| ≤
      |CriticalEndpoint.exponentCoefficient a| *K 0*h^3*shiftedPower a t^3 := by
    rw [abs_mul,abs_mul,abs_of_nonneg hh]
    have he := mul_le_mul_of_nonneg_left (hbound 0 ε hε t ht) (mul_nonneg (abs_nonneg (CriticalEndpoint.exponentCoefficient a)) hh)
    norm_num only [zero_add] at he
    convert he using 1; ring
  have hsum : |∑ j ∈ Finset.range n, lam (j+1)*
      (-h^(j+3)*correctedPower a ε t^(j+3)+h^(j+4)*
        deriv (causalConvolution (fun s => correctedPower a ε s^(j+3)) (correctedPower a ε)) t)| ≤
      (∑ j ∈ Finset.range n,|lam (j+1)| *((5/4:ℝ)^3+K (j+1)))*h^3*shiftedPower a t^3 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul]
    have hd := hbound (j+1) ε hε t ht
    simp only [add_assoc] at hd
    have he := mul_le_mul_of_nonneg_left
      (higher_remainder_term_bound a ε h t (K (j+1)) (j+3) ha0 hε hh0 hh1 ht (by omega) (hK (j+1)).le hd)
      (abs_nonneg (lam (j+1)))
    convert he using 1; ring
  unfold idealRemainder
  calc
    _ ≤ |CriticalEndpoint.exponentCoefficient a*h^3*
      deriv (causalConvolution (fun s => correctedPower a ε s^2) (correctedPower a ε)) t| +
      |∑ j ∈ Finset.range n, lam (j+1)*
        (-h^(j+3)*correctedPower a ε t^(j+3)+h^(j+4)*
          deriv (causalConvolution (fun s => correctedPower a ε s^(j+3)) (correctedPower a ε)) t)| := abs_add_le _ _
    _ ≤ C*h^3*shiftedPower a t^3 := by
      dsimp [C]
      have he := add_le_add hfirst hsum
      convert he using 1; ring
    _ ≤ (C+1)*h^3*shiftedPower a t^3 := by nlinarith [mul_nonneg hh hg]

end
end SphericalAging.StationaryIdealResidual
