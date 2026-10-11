module

public import SphericalAging.StationaryClusterInputs
public import SphericalAging.ForkParameterBounds

public section

/-! The deterministic stationary passage for every continuous weight on
the late response window, including the finite-fork energy weight. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SphericalAging.StationaryWeightedResponseWindow
open MeasureTheory Set Filter Topology CKSpecification CKPhysicalConsequences
  StationaryClusterInputs GreenCovariance PrefixRectangleStability ForkParameterBounds

theorem stationary_weighted_response_window {p : ℕ} {β : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n) {L : ℝ} (hL : 0≤L)
    (w : ℝ→ℝ) (hw : Continuous w) :
    Tendsto (fun n => ∫u in T n..(T n+L),w (T n+L-u)*d.R (T n+L) u)
      atTop (nhds (∫τ in (0:ℝ)..L,w τ*r τ)) := by
  let F : ℕ→ℝ→ℝ := fun n v => w (L-v)*clampedResponse d (T n+L) (T n+v)
  have hF (n : ℕ) : Continuous (F n) := by
    exact (hw.comp (continuous_const.sub continuous_id)).mul
      ((clampedResponse_continuous h).comp (continuous_const.prodMk (continuous_const.add continuous_id)))
  have hi : Tendsto (fun n => ∫v in (0:ℝ)..L,F n v)
      atTop (nhds (∫v in (0:ℝ)..L,w (L-v)*r (L-v))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun v => |w (L-v)|)
    · exact Eventually.of_forall fun n => (hF n).aestronglyMeasurable
    · exact Eventually.of_forall fun n => ae_of_all _ (fun v _ => by
        let a := max (T n+L) (max 0 (T n+v))
        let b := max 0 (T n+v)
        have hb0 : 0≤b := le_max_left _ _
        have hba : b≤a := le_max_right _ _
        have hh := physical_bounds_of_equations h
        have hb : |clampedResponse d (T n+L) (T n+v)|≤1 := by
          change |d.R a b|≤1
          rw [abs_of_nonneg (hh.2 a b hb0 hba)]
          exact (response_le_correlation h hb0 hba).trans (hh.1 a b (hb0.trans hba) hb0).2
        dsimp only [F]
        rw [Real.norm_eq_abs,abs_mul]
        exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (mul_one _))
    · exact ((hw.comp (continuous_const.sub continuous_id)).abs).intervalIntegrable 0 L
    · apply ae_of_all
      intro v hv
      rw [uIoc_of_le hL] at hv
      have hr := (H.response L hL).tendsto_at
        (show (L,v)∈triangle L from ⟨⟨hL,le_rfl⟩,⟨hv.1.le,hv.2⟩⟩)
      have hc : Tendsto (fun n => clampedResponse d (T n+L) (T n+v)) atTop (nhds (r (L-v))) := by
        apply hr.congr'
        exact Eventually.of_forall fun n =>
          (clampedResponse_eq (add_nonneg (hT n) hv.1.le) (by linarith [hv.2])).symm
      exact hc.const_mul (w (L-v))
  have hreflect : (∫v in (0:ℝ)..L,w (L-v)*r (L-v))=∫τ in (0:ℝ)..L,w τ*r τ := by
    simpa only [sub_zero,sub_self] using
      (intervalIntegral.integral_comp_sub_left (fun τ => w τ*r τ) L (a:=(0:ℝ)) (b:=L))
  rw [hreflect] at hi
  apply hi.congr'
  exact Eventually.of_forall fun n => by
    have he := intervalIntegral.integral_comp_add_right
      (a:=(0:ℝ)) (b:=L) (fun u => w (T n+L-u)*d.R (T n+L) u) (T n)
    have he' : (∫v in (0:ℝ)..L,w (T n+L-(v+T n))*d.R (T n+L) (v+T n))=
        ∫u in T n..(T n+L),w (T n+L-u)*d.R (T n+L) u := by
      simpa only [zero_add,add_comm L (T n)] using he
    apply Eq.trans (b:=∫v in (0:ℝ)..L,w (T n+L-(v+T n))*d.R (T n+L) (v+T n)) ?_ he'
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hL] at hv
    dsimp only [F]
    rw [clampedResponse_eq (add_nonneg (hT n) hv.1) (by linarith [hv.2])]
    congr 2 <;> ring

@[expose] def continuousForkWeight (p K : ℕ) (c : ℝ→ℝ) (L τ : ℝ) : ℝ :=
  c (max τ 0)^(p-1)-mixedOverlap (fun u => c (max u 0)) K L τ^(p-1)

theorem continuousForkWeight_continuous {c r : ℝ→ℝ} {q : ℝ}
    (H : ProfileCenterEnergy.Profile c r q) (p K : ℕ) (L : ℝ) :
    Continuous (continuousForkWeight p K c L) := by
  have hc : Continuous (fun u => c (max u 0)) :=
    H.continuous_c.comp_continuous (continuous_id.max continuous_const)
      (fun u => le_max_right u 0)
  unfold continuousForkWeight mixedOverlap
  have hm : Continuous (fun u => (c (max u 0)+((K:ℝ)-1)*c (max (2*L-u) 0))/(K:ℝ)) :=
    (hc.add ((hc.comp (continuous_const.sub continuous_id)).const_mul ((K:ℝ)-1))).div_const (K:ℝ)
  exact (hc.pow (p-1)).sub (hm.pow (p-1))

theorem continuousForkWeight_on_window (p K : ℕ) (c : ℝ→ℝ) {L τ : ℝ}
    (hL : 0≤L) (hτ : τ∈Icc 0 L) :
    continuousForkWeight p K c L τ=c τ^(p-1)-mixedOverlap c K L τ^(p-1) := by
  simp only [continuousForkWeight,mixedOverlap,max_eq_left hτ.1,
    max_eq_left (show 0≤2*L-τ by linarith [hτ.2])]

end SphericalAging.StationaryWeightedResponseWindow
