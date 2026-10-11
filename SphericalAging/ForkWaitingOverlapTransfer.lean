module

public import SphericalAging.ForkNormalizedEnergy
public import SphericalAging.GaussianSeedOverlapBounds
public import SphericalAging.FiniteStateOrthogonalityBounds

public section

/-! True L² comparison against a physical waiting state, which may
depend arbitrarily on the disorder and all previous Brownian noise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SphericalAging.ForkWaitingOverlapTransfer
open MeasureTheory Filter FiniteModel ForkEnergyComparison RandomGaussianPairing
  ForkNormalizedEnergy FiniteStateOrthogonalityBounds GaussianSeedOverlapBounds
open scoped ENNReal InnerProductSpace
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem ball_L2_norm_bound {N : ℕ} {X : Ω→Vector N} (hX : MemLp X 2 μ)
    (hXb : ∀ᵐω ∂μ,‖X ω‖≤Real.sqrt N) : ‖hX.toLp X‖≤Real.sqrt N := by
  have hb : ∀ᵐω ∂μ,‖hX.toLp X ω‖≤Real.sqrt N := by
    filter_upwards [hX.coeFn_toLp,hXb] with ω hx hb
    simpa only [hx] using hb
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (Real.sqrt_nonneg (N:ℝ)) hb

theorem waiting_pairing_comparison {N : ℕ} (hN : 0<N) {A M X : Ω→Vector N}
    (hA : MemLp A 2 μ) (hM : MemLp M 2 μ) (hX : MemLp X 2 μ)
    (hXb : ∀ᵐω ∂μ,‖X ω‖≤Real.sqrt N) :
    |pairing (μ:=μ) A X-pairing (μ:=μ) M X|≤distanceRoot μ N A M := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hr : 0<Real.sqrt N := Real.sqrt_pos.mpr hn
  have he : pairing (μ:=μ) A X-pairing (μ:=μ) M X=pairing (μ:=μ) (A-M) X := by
    unfold pairing
    rw [←sub_div,←integral_sub (inner_integrable hA hX) (inner_integrable hM hX)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by simp only [Pi.sub_apply,inner_sub_left]
  rw [he]
  unfold pairing distanceRoot
  rw [abs_div,abs_of_pos hn,integral_inner_eq (hA.sub hM) hX]
  have hnorm := ball_L2_norm_bound hX hXb
  calc
    _≤(‖(hA.sub hM).toLp (A-M)‖*Real.sqrt N)/(N:ℝ) :=
      div_le_div_of_nonneg_right ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))) hn.le
    _=lpNorm (fun ω => ‖A ω-M ω‖) 2 μ/Real.sqrt N := by
      rw [Lp.norm_toLp]
      change lpNorm (A-M) 2 μ*Real.sqrt N/(N:ℝ)=lpNorm (fun ω => ‖A ω-M ω‖) 2 μ/Real.sqrt N
      have hnormeq : lpNorm (A-M) 2 μ=lpNorm (fun ω => ‖A ω-M ω‖) 2 μ := by
        symm
        exact congrArg ENNReal.toReal (eLpNorm_norm (A-M) (hA.sub hM).aestronglyMeasurable)
      rw [hnormeq]
      apply (div_eq_div_iff hn.ne' hr.ne').mpr
      calc
        _=lpNorm (fun ω => ‖A ω-M ω‖) 2 μ*(Real.sqrt N*Real.sqrt N) := by ring
        _=_ := by rw [Real.mul_self_sqrt hn.le]

theorem waiting_pairing_le_sqrt_overlap {N : ℕ} (hN : 0<N) {A X : Ω→Vector N}
    (hA : MemLp A 2 μ) (hX : MemLp X 2 μ)
    (hAb : ∀ᵐω ∂μ,‖A ω‖≤Real.sqrt N) (hXb : ∀ᵐω ∂μ,‖X ω‖≤Real.sqrt N) :
    pairing (μ:=μ) A X≤Real.sqrt (∫ω,|inner ℝ (A ω) (X ω)/(N:ℝ)|^2 ∂μ) := by
  have hm : AEStronglyMeasurable (fun ω => |inner ℝ (A ω) (X ω)/(N:ℝ)|) μ := by
    simpa only [Real.norm_eq_abs,div_eq_mul_inv] using
      ((hA.aestronglyMeasurable.inner hX.aestronglyMeasurable).mul_const (N:ℝ)⁻¹).norm
  have hp := probability_power_mean_le hm (by
    filter_upwards [hAb,hXb] with ω ha hx
    exact ⟨abs_nonneg _,ball_overlap_abs_le_one hN ha hx⟩) 2
  have hz : 0≤∫ω,|inner ℝ (A ω) (X ω)/(N:ℝ)| ∂μ := integral_nonneg fun _ => abs_nonneg _
  have hs : (∫ω,|inner ℝ (A ω) (X ω)/(N:ℝ)| ∂μ)≤
      Real.sqrt (∫ω,|inner ℝ (A ω) (X ω)/(N:ℝ)|^2 ∂μ) := by
    have hi : 0≤∫ω,|inner ℝ (A ω) (X ω)/(N:ℝ)|^2 ∂μ :=
      integral_nonneg fun _ => sq_nonneg _
    nlinarith [Real.sq_sqrt hi,Real.sqrt_nonneg (∫ω,|inner ℝ (A ω) (X ω)/(N:ℝ)|^2 ∂μ),hp.2.2]
  apply le_trans _ hs
  unfold pairing
  rw [←integral_div]
  exact integral_mono ((inner_integrable hA hX).div_const _) hp.1 (fun _ => le_abs_self _)

theorem normalized_center_waiting_pairing_le {N : ℕ} (hN : 0<N) {Q : ℝ}
    {A M X : Ω→Vector N} (hA : MemLp A 2 μ) (hM : MemLp M 2 μ) (hX : MemLp X 2 μ)
    (hAb : ∀ᵐω ∂μ,‖A ω‖≤Real.sqrt N) (hXb : ∀ᵐω ∂μ,‖X ω‖≤Real.sqrt N) :
    pairing (μ:=μ) M X/Real.sqrt Q≤
      Real.sqrt (∫ω,|inner ℝ (A ω) (X ω)/(N:ℝ)|^2 ∂μ)+
        distanceRoot μ N A (normalized Q M) := by
  have hc := waiting_pairing_comparison hN hA (normalized_memLp (Q:=Q) hM) hX hXb
  have hp := waiting_pairing_le_sqrt_overlap hN hA hX hAb hXb
  have he : pairing (μ:=μ) (normalized Q M) X=pairing (μ:=μ) M X/Real.sqrt Q := by
    rw [normalized,pairing_smul]
    ring
  rw [he] at hc
  linarith [neg_abs_le (pairing (μ:=μ) A X-pairing (μ:=μ) M X/Real.sqrt Q)]

end SphericalAging.ForkWaitingOverlapTransfer
