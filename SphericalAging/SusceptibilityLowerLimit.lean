module

public import SphericalAging.CausalSusceptibilityBound
public import SphericalAging.SusceptibilityReceiptTail
public import SphericalAging.FiniteLimitLowerBound
public import Mathlib.Topology.Instances.ENNReal.Lemmas

public section

/-! Literal source Theorem 14.7: real-ray susceptibility lower limits, including
the stronger finite-D lower bound. All root, trace, diagonal, localization and
prefix mass conclusions are derived from independent selected-profile inputs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalAging.SusceptibilityLowerLimit
open CKSpecification CKPhysicalConsequences CubicResponseLocalization SusceptibilityDiagonalTheorem
open SusceptibilityDiagonal SusceptibilityReceiptTail CausalSusceptibilityBound FiniteLimitLowerBound

 theorem finite_sequence_strong_lower_bound {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) (t : ℕ→ℝ) (ht : Tendsto t atTop atTop)
    {γ D : ℝ} (hD : 0<D)
    (hχ : Tendsto (fun n => susceptibility d (t n) 0) atTop (𝓝 γ)) :
    (1-q)+q*(1-q)/c (2*D)≤γ := by
  obtain ⟨N0,i,A,hrecent⟩ := source14_7_step1 H t ht
  have ht0 := ht.comp (tendsto_add_atTop_nat N0)
  have hχ0 := hχ.comp (tendsto_add_atTop_nat N0)
  obtain ⟨N1,hN1⟩ := eventually_atTop.mp (A.waiting_tendsto.eventually (eventually_ge_atTop D))
  have A1 := receipt_tail A N1
  exact finite_limit_strong_lower_bound H A1 (ht0.comp (tendsto_add_atTop_nat N1)) hD
    (fun n => hN1 (n+N1) (Nat.le_add_left _ _)) (hχ0.comp (tendsto_add_atTop_nat N1))

 theorem finite_sequence_lower_bound {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) (t : ℕ→ℝ) (ht : Tendsto t atTop atTop)
    {γ : ℝ} (hχ : Tendsto (fun n => susceptibility d (t n) 0) atTop (𝓝 γ)) :
    2*(1-q)≤γ := by
  have htwo : Tendsto (fun D : ℝ => 2*D) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (show (0:ℝ)<2 by norm_num)).mpr tendsto_id
  have hh := tendsto_const_nhds (x:=1-q) |>.add
    (tendsto_const_nhds (x:=q*(1-q)) |>.div (H.plateau_limit.comp htwo) (ne_of_gt H.q_positive))
  have he : (1-q)+q*(1-q)/q=2*(1-q) := by field_simp [ne_of_gt H.q_positive]; ring
  rw [he] at hh
  apply le_of_tendsto hh
  filter_upwards [eventually_gt_atTop (0:ℝ)] with D hD
  exact finite_sequence_strong_lower_bound H t ht hD hχ

 theorem susceptibility_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0≤t) : 0≤susceptibility d t 0 := by
  apply intervalIntegral.integral_nonneg ht
  exact fun u hu => (physical_bounds_of_equations h).2 t u hu.1 hu.2

 theorem strong_eventually_lower_bound {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) {D : ℝ} (hD : 0<D) :
    ∀ε : ℝ,0<ε → ∀ᶠt : ℝ in atTop,(1-q)+q*(1-q)/c (2*D)-ε≤susceptibility d t 0 :=
  eventually_lower_of_finite_limits (fun t ht => susceptibility_nonnegative h ht)
    (fun t ht γ hχ => finite_sequence_strong_lower_bound H t ht hD hχ)

 theorem eventually_lower_bound {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) :
    ∀ε : ℝ,0<ε → ∀ᶠt : ℝ in atTop,2*(1-q)-ε≤susceptibility d t 0 :=
  eventually_lower_of_finite_limits (fun t ht => susceptibility_nonnegative h ht)
    (fun t ht γ hχ => finite_sequence_lower_bound H t ht hχ)

 theorem ofReal_liminf_lower {f : ℝ→ℝ} {b : ℝ}
    (hbound : ∀ε : ℝ,0<ε → ∀ᶠt : ℝ in atTop,b-ε≤f t) :
    ENNReal.ofReal b≤liminf (fun t : ℝ => ENNReal.ofReal (f t)) atTop := by
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (b-ε)) (𝓝[>] (0:ℝ)) (𝓝 (ENNReal.ofReal b)) := by
    simpa only [sub_zero] using ENNReal.tendsto_ofReal (tendsto_const_nhds.sub hid)
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact le_liminf_of_le (h := (hbound ε hε).mono (fun t ht => ENNReal.ofReal_le_ofReal ht))

 theorem source14_7 {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) :
    ENNReal.ofReal (2*(1-q))≤liminf (fun t : ℝ => ENNReal.ofReal (susceptibility d t 0)) atTop ∧
    ∀D : ℝ,0<D → ENNReal.ofReal ((1-q)+q*(1-q)/c (2*D))≤
      liminf (fun t : ℝ => ENNReal.ofReal (susceptibility d t 0)) atTop :=
  ⟨ofReal_liminf_lower (eventually_lower_bound H),
    fun D hD => ofReal_liminf_lower (strong_eventually_lower_bound H hD)⟩

end SphericalAging.SusceptibilityLowerLimit
