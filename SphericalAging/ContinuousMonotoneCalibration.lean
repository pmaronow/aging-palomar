module

public import SphericalAging.AlgorithmicCorrelationMonotonicity
public import Mathlib.Topology.Order.IntermediateValue

public section

/-! A genuine monotone calibration of correlation values by Gaussian noise
parameters, obtained from continuity and the intermediate value theorem. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.ContinuousMonotoneCalibration
open Set

theorem exists_parameter (χ : ℝ→ℝ) (hχ : ContinuousOn χ (Icc 0 1))
    (r : ℝ) (hr : r∈Icc (χ 0) (χ 1)) : ∃s : ℝ,s∈Icc 0 1 ∧ χ s=r := by
  obtain ⟨s,hs,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hχ hr
  exact ⟨s,hs,he⟩

@[expose] def parameter (χ : ℝ→ℝ) (hχ : ContinuousOn χ (Icc 0 1)) (r : ℝ) : ℝ :=
  if hr : r∈Icc (χ 0) (χ 1) then Classical.choose (exists_parameter χ hχ r hr) else 0

theorem parameter_mem (χ : ℝ→ℝ) (hχ : ContinuousOn χ (Icc 0 1))
    (r : ℝ) (hr : r∈Icc (χ 0) (χ 1)) : parameter χ hχ r∈Icc 0 1 := by
  rw [parameter,dif_pos hr]
  exact (Classical.choose_spec (exists_parameter χ hχ r hr)).1

theorem parameter_spec (χ : ℝ→ℝ) (hχ : ContinuousOn χ (Icc 0 1))
    (r : ℝ) (hr : r∈Icc (χ 0) (χ 1)) : χ (parameter χ hχ r)=r := by
  rw [parameter,dif_pos hr]
  exact (Classical.choose_spec (exists_parameter χ hχ r hr)).2

theorem parameter_monotoneOn (χ : ℝ→ℝ) (hχ : ContinuousOn χ (Icc 0 1))
    (hm : MonotoneOn χ (Icc 0 1)) : MonotoneOn (parameter χ hχ) (Icc (χ 0) (χ 1)) := by
  intro a ha b hb hab
  by_cases heq : a=b
  · subst b;exact le_refl _
  by_contra hbad
  have hba : parameter χ hχ b≤parameter χ hχ a := (lt_of_not_ge hbad).le
  have hh := hm (parameter_mem χ hχ b hb) (parameter_mem χ hχ a ha) hba
  rw [parameter_spec χ hχ b hb,parameter_spec χ hχ a ha] at hh
  exact heq (le_antisymm hab hh)

theorem calibrated_schedule (χ : ℝ→ℝ) (hχ : ContinuousOn χ (Icc 0 1))
    (hm : MonotoneOn χ (Icc 0 1)) (q : ℕ→ℝ) (hq : Monotone q)
    (hrange : ∀l,q l∈Icc (χ 0) (χ 1)) :
    let v := fun l => parameter χ hχ (q l)
    Monotone v ∧ (∀l,v l∈Icc 0 1) ∧ (∀l,χ (v l)=q l) := by
  exact ⟨fun a b hab => parameter_monotoneOn χ hχ hm (hrange a) (hrange b) (hq hab),
    fun l => parameter_mem χ hχ (q l) (hrange l),
    fun l => parameter_spec χ hχ (q l) (hrange l)⟩

end SphericalAging.ContinuousMonotoneCalibration
