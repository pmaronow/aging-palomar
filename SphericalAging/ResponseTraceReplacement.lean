module

public import SphericalAging.ResponseMatrixEnergyContraction

public section

/-! Weighted signed-trace replacement for the actual two-time response.
The normalized trace is controlled directly by its physical column
moments, without a pathwise operator-norm moment premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set StochasticCalculus
open scoped BigOperators InnerProductSpace NNReal ENNReal
namespace SphericalAging.ResponseTraceReplacement
open HardSphereDynamics FiniteModel FiniteCorrelationIto
open ResponseMatrixEnergyContraction TwoTimeResponseMatrix
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

lemma integral_abs_mul_le_sqrt {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (∫ ω,|f ω*g ω| ∂P)≤Real.sqrt (∫ ω,(f ω)^2 ∂P)*Real.sqrt (∫ ω,(g ω)^2 ∂P) := by
  have hc : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have h := integral_mul_norm_le_Lp_mul_Lq hc (by simpa using hf) (by simpa using hg)
  simpa [Real.norm_eq_abs,Real.rpow_two,sq_abs,Real.sqrt_eq_rpow,one_div,abs_mul] using h

lemma fourthMoment_to_secondMoment {f : Ω → ℝ} (hf : MemLp f 4 P) {C : ℝ}
    (hC : (∫ ω,|f ω|^4 ∂P)≤C) : MemLp f 2 P ∧ (∫ ω,(f ω)^2 ∂P)≤1+C := by
  have hf2 : MemLp f 2 P := hf.mono_exponent (by norm_num)
  refine ⟨hf2,?_⟩
  calc
    _ ≤ ∫ ω,1+|f ω|^4 ∂P := integral_mono_ae hf2.integrable_sq
      ((integrable_const 1).add (by simpa only [Real.norm_eq_abs] using hf.integrable_norm_pow'))
      (ae_of_all P (fun ω => by nlinarith [sq_nonneg ((f ω)^2-1),sq_abs (f ω)]))
    _ = 1+(∫ ω,|f ω|^4 ∂P) := by
      rw [integral_add (integrable_const 1) (by simpa only [Real.norm_eq_abs] using hf.integrable_norm_pow')];simp
    _ ≤ 1+C := add_le_add_right hC 1

lemma pow_difference_abs_le (n : ℕ) {a b : ℝ} (ha : |a|≤1) (hb : |b|≤1) :
    |a^n-b^n|≤(n : ℝ)*|a-b| := by
  calc
    _ ≤ |a-b| *(n : ℝ)*(max |a| |b|)^(n-1) := abs_pow_sub_pow_le a b n
    _ ≤ |a-b| *(n : ℝ)*1^(n-1) := by gcongr;exact max_le ha hb
    _ = _ := by simp;ring

/-- The overlap replacement uses the actual signed trace itself. -/
theorem weighted_trace_replacement {a r : Ω → ℝ} {b C : ℝ} (n : ℕ)
    (ha : AEStronglyMeasurable a P) (hab : ∀ᵐ ω ∂P,|a ω|≤1) (hb : |b|≤1)
    (hr : MemLp r 4 P) (hC : (∫ ω,|r ω|^4 ∂P)≤C) :
    Integrable (fun ω => |((a ω)^n-b^n)*r ω|) P ∧
    (∫ ω,|((a ω)^n-b^n)*r ω| ∂P)≤
      (n : ℝ)*Real.sqrt (∫ ω,(a ω-b)^2 ∂P)*Real.sqrt (1+C) := by
  have hd : MemLp (fun ω => a ω-b) 2 P := MemLp.of_bound (ha.sub aestronglyMeasurable_const) 2
    (hab.mono (fun ω hw => by
      rw [Real.norm_eq_abs]
      exact (abs_sub (a ω) b).trans (by linarith)))
  have htr := fourthMoment_to_secondMoment hr hC
  have hg : Integrable (fun ω => |a ω-b| *|r ω|) P := by
    simpa only [Real.norm_eq_abs,Pi.mul_apply] using
      (((hd.norm).fun_mul htr.1.norm : MemLp (fun ω => ‖a ω-b‖*‖r ω‖) 1 P).integrable (by norm_num))
  have hmajor := hg.const_mul (n : ℝ)
  have hbound : ∀ᵐ ω ∂P,|((a ω)^n-b^n)*r ω|≤(n : ℝ)*(|a ω-b| *|r ω|) := by
    filter_upwards [hab] with ω hw
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (pow_difference_abs_le n hw hb) (abs_nonneg _)).trans_eq (by ring)
  have hi : Integrable (fun ω => |((a ω)^n-b^n)*r ω|) P :=
    hmajor.mono' (((ha.pow n).sub aestronglyMeasurable_const).mul hr.aestronglyMeasurable).norm
      (hbound.mono (fun ω hw => by simpa only [Real.norm_eq_abs,abs_abs] using hw))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω,(n : ℝ)*(|a ω-b| *|r ω|) ∂P := integral_mono_ae hi hmajor hbound
    _ = (n : ℝ)*(∫ ω,|(a ω-b)*r ω| ∂P) := by simp only [integral_const_mul,abs_mul]
    _ ≤ (n : ℝ)*(Real.sqrt (∫ ω,(a ω-b)^2 ∂P)*Real.sqrt (∫ ω,(r ω)^2 ∂P)) :=
      mul_le_mul_of_nonneg_left (integral_abs_mul_le_sqrt hd htr.1) (Nat.cast_nonneg n)
    _ ≤ (n : ℝ)*(Real.sqrt (∫ ω,(a ω-b)^2 ∂P)*Real.sqrt (1+C)) := by
      gcongr
      exact htr.2
    _ = _ := by ring

variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Actual finite-N response/overlap replacement. The response moment is
derived from its physical SDE rather than required as a premise. -/
theorem actual_weighted_trace_replacement (hN : 0<N) (hp : 2≤p)
    (D : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun t => X t ω))
    {Kb Ks : ℝ≥0} (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (s T : ℝ≥0) (hSphere : ∀ᵐ ω ∂P,OnSphere (X s ω))
    (hSpherePath : ∀ᵐ ω ∂P,∀ t,t≤s+T → OnSphere (X t ω))
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t≤T) (n : ℕ) (b : ℝ) (hbb : |b|≤1) :
    let M := terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s T hSphere t
    Integrable (fun ω => |((overlap (X (s+t) ω) (X s ω))^n-b^n)*sampleTrace M ω|) P ∧
    (∫ ω,|((overlap (X (s+t) ω) (X s ω))^n-b^n)*sampleTrace M ω| ∂P)≤
      (n : ℝ)*Real.sqrt (∫ ω,(overlap (X (s+t) ω) (X s ω)-b)^2 ∂P)*
        Real.sqrt (1+uniformFourthConstant p β J t) := by
  dsimp only
  have hm := actual_response_contraction_moments hN hp D β R hR hNR J X hXa hXc hb hs s T
    hSphere hSpherePath hnull t ht
  have hx : ∀ᵐ ω ∂P,OnSphere (X (s+t) ω) := hSpherePath.mono
    (fun ω hw => hw (s+t) (add_le_add le_rfl ht))
  have ha : AEStronglyMeasurable (fun ω => overlap (X (s+t) ω) (X s ω)) P := by
    simpa only [overlap,div_eq_mul_inv] using
      ((((hXa (s+t)).mono (F.le _)).aestronglyMeasurable.inner
        ((hXa s).mono (F.le _)).aestronglyMeasurable).mul_const (N : ℝ)⁻¹)
  have hab : ∀ᵐ ω ∂P,|overlap (X (s+t) ω) (X s ω)|≤1 := by
    filter_upwards [hx,hSphere] with ω hxx hyy
    exact overlap_abs_le_one hN hxx hyy
  exact weighted_trace_replacement n ha hab hbb hm.1 hm.2.1

end SphericalAging.ResponseTraceReplacement
