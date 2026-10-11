module

public import SphericalAging.HamiltonianBallBounds
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

public section

/-! The actual probability estimates converting finite query-span
orthogonality into orthogonality to its Euler-approximated waiting state. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SphericalAging.FiniteStateOrthogonalityBounds
open MeasureTheory Filter Set FiniteModel
open scoped Topology InnerProductSpace

theorem ball_overlap_abs_le_one {N : ℕ} (hN : 0<N) {a x : Vector N}
    (ha : ‖a‖≤Real.sqrt N) (hx : ‖x‖≤Real.sqrt N) :
    |inner ℝ a x/(N:ℝ)|≤1 := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  rw [abs_div,abs_of_pos hn,div_le_one hn]
  calc
    |inner ℝ a x|≤‖a‖*‖x‖ := abs_real_inner_le_norm _ _
    _≤Real.sqrt N*Real.sqrt N := mul_le_mul ha hx (norm_nonneg _) (Real.sqrt_nonneg _)
    _=(N:ℝ) := Real.mul_self_sqrt hn.le

theorem ball_overlap_comparison {N : ℕ} (hN : 0<N) {a x y : Vector N}
    (ha : ‖a‖≤Real.sqrt N) :
    |inner ℝ a x/(N:ℝ)|^2≤2*|inner ℝ a y/(N:ℝ)|^2+2*(‖x-y‖^2/(N:ℝ)) := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hr : 0<Real.sqrt N := Real.sqrt_pos.mpr hn
  have hb : |inner ℝ a (x-y)/(N:ℝ)|≤‖x-y‖/Real.sqrt N := by
    rw [abs_div,abs_of_pos hn]
    calc
      |inner ℝ a (x-y)|/(N:ℝ)≤(Real.sqrt N*‖x-y‖)/(N:ℝ) :=
        div_le_div_of_nonneg_right ((abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right ha (norm_nonneg _))) hn.le
      _=‖x-y‖/Real.sqrt N := by
        apply (div_eq_div_iff hn.ne' hr.ne').mpr
        calc
          Real.sqrt N*‖x-y‖*Real.sqrt N=‖x-y‖*(Real.sqrt N*Real.sqrt N) := by ring
          _=‖x-y‖*(N:ℝ) := by rw [Real.mul_self_sqrt hn.le]
  have ht : |inner ℝ a x/(N:ℝ)|≤|inner ℝ a y/(N:ℝ)|+‖x-y‖/Real.sqrt N := by
    have he : inner ℝ a x/(N:ℝ)=inner ℝ a y/(N:ℝ)+inner ℝ a (x-y)/(N:ℝ) := by
      rw [inner_sub_right];ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add le_rfl hb)
  have hs : (‖x-y‖/Real.sqrt N)^2=‖x-y‖^2/(N:ℝ) := by
    rw [div_pow,Real.sq_sqrt hn.le]
  have hd : 0≤‖x-y‖/Real.sqrt N := div_nonneg (norm_nonneg _) hr.le
  nlinarith [sq_nonneg (|inner ℝ a y/(N:ℝ)|-‖x-y‖/Real.sqrt N),abs_nonneg (inner ℝ a x/(N:ℝ)),abs_nonneg (inner ℝ a y/(N:ℝ))]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem overlap_square_integrable_bound {N : ℕ} (hN : 0<N) {A X : Ω→Vector N}
    (hA : AEStronglyMeasurable A μ) (hX : AEStronglyMeasurable X μ)
    (hAb : ∀ᵐω ∂μ,‖A ω‖≤Real.sqrt N) (hXb : ∀ᵐω ∂μ,‖X ω‖≤Real.sqrt N) :
    Integrable (fun ω => |inner ℝ (A ω) (X ω)/(N:ℝ)|^2) μ ∧
    (∫ω,|inner ℝ (A ω) (X ω)/(N:ℝ)|^2 ∂μ)∈Icc (0:ℝ) 1 := by
  have hm : AEStronglyMeasurable (fun ω => |inner ℝ (A ω) (X ω)/(N:ℝ)|^2) μ := by
    convert (((hA.inner hX).mul_const (N:ℝ)⁻¹).norm.pow 2) using 1
    funext ω
    simp only [Pi.pow_apply,Real.norm_eq_abs,div_eq_mul_inv]
  have hb : ∀ᵐω ∂μ,|inner ℝ (A ω) (X ω)/(N:ℝ)|^2≤1 := by
    filter_upwards [hAb,hXb] with ω ha hx
    exact pow_le_one₀ (abs_nonneg _) (ball_overlap_abs_le_one hN ha hx)
  have hi : Integrable (fun ω => |inner ℝ (A ω) (X ω)/(N:ℝ)|^2) μ :=
    (integrable_const (1:ℝ)).mono' hm (hb.mono fun ω hω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (|inner ℝ (A ω) (X ω)/(N:ℝ)|))]
      exact hω)
  refine ⟨hi,integral_nonneg (fun _ => sq_nonneg _),?_⟩
  simpa using integral_mono_ae hi (integrable_const (1:ℝ)) hb

theorem distance_square_integrable_bound {N : ℕ} (hN : 0<N) {X Y : Ω→Vector N}
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ)
    (hXb : ∀ᵐω ∂μ,‖X ω‖≤Real.sqrt N) (hYb : ∀ᵐω ∂μ,‖Y ω‖≤Real.sqrt N) :
    Integrable (fun ω => ‖X ω-Y ω‖^2/(N:ℝ)) μ ∧
    (∫ω,‖X ω-Y ω‖^2/(N:ℝ) ∂μ)∈Icc (0:ℝ) 4 := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hm : AEStronglyMeasurable (fun ω => ‖X ω-Y ω‖^2/(N:ℝ)) μ := by
    simpa only [div_eq_mul_inv,Pi.pow_apply,Pi.sub_apply] using ((hX.sub hY).norm.pow 2).mul_const (N:ℝ)⁻¹
  have hb : ∀ᵐω ∂μ,‖X ω-Y ω‖^2/(N:ℝ)≤4 := by
    filter_upwards [hXb,hYb] with ω hx hy
    have ht : ‖X ω-Y ω‖≤2*Real.sqrt N := by linarith [norm_sub_le (X ω) (Y ω)]
    rw [div_le_iff₀ hn]
    nlinarith [norm_nonneg (X ω-Y ω),Real.mul_self_sqrt hn.le,Real.sqrt_nonneg (N:ℝ)]
  have hi : Integrable (fun ω => ‖X ω-Y ω‖^2/(N:ℝ)) μ :=
    (integrable_const (4:ℝ)).mono' hm (hb.mono fun ω hω => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) hn.le)] using hω)
  refine ⟨hi,integral_nonneg (fun _ => div_nonneg (sq_nonneg _) hn.le),?_⟩
  simpa using integral_mono_ae hi (integrable_const (4:ℝ)) hb

theorem overlap_mean_square_comparison {N : ℕ} (hN : 0<N) {A X Y : Ω→Vector N}
    (hA : AEStronglyMeasurable A μ) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ)
    (hAb : ∀ᵐω ∂μ,‖A ω‖≤Real.sqrt N) (hXb : ∀ᵐω ∂μ,‖X ω‖≤Real.sqrt N)
    (hYb : ∀ᵐω ∂μ,‖Y ω‖≤Real.sqrt N) :
    (∫ω,|inner ℝ (A ω) (X ω)/(N:ℝ)|^2 ∂μ)≤
      2*(∫ω,|inner ℝ (A ω) (Y ω)/(N:ℝ)|^2 ∂μ)+
      2*(∫ω,‖X ω-Y ω‖^2/(N:ℝ) ∂μ) := by
  have hx := (overlap_square_integrable_bound hN hA hX hAb hXb).1
  have hy := (overlap_square_integrable_bound hN hA hY hAb hYb).1
  have hd := (distance_square_integrable_bound hN hX hY hXb hYb).1
  have hb := integral_mono_ae hx ((hy.const_mul 2).add (hd.const_mul 2))
    (hAb.mono fun ω hω => ball_overlap_comparison hN hω)
  simp only [Pi.add_apply] at hb
  rw [integral_add (f := fun ω => 2*|inner ℝ (A ω) (Y ω)/(N:ℝ)|^2)
    (g := fun ω => 2*(‖X ω-Y ω‖^2/(N:ℝ))) (hy.const_mul 2) (hd.const_mul 2),
    integral_const_mul,integral_const_mul] at hb
  exact hb

end SphericalAging.FiniteStateOrthogonalityBounds
