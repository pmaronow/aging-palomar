module

public import SphericalAging.SphereOnlyParameterIntegral
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

public section

/-! Spatial smooth positive localization. A compact-set positive smooth
function has a globally positive smooth representative agreeing on an
open neighborhood of that compact set. No ambient evolution is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.SmoothPositiveSpatialReplacement
open Set Filter
open scoped Topology

@[expose] def positiveClamp (c s : ℝ) : ℝ :=
  Real.smoothTransition (2*s/c-1)*s+(1-Real.smoothTransition (2*s/c-1))*c

theorem positiveClamp_pos {c : ℝ} (hc : 0<c) (s : ℝ) : 0<positiveClamp c s := by
  by_cases hs : s≤c/2
  · have ht : 2*s/c-1≤0 := by
      have hh : 2*s/c≤1 := (div_le_iff₀ hc).mpr (by linarith)
      linarith
    simp only [positiveClamp,Real.smoothTransition.zero_of_nonpos ht,zero_mul,sub_zero,one_mul,zero_add]
    exact hc
  · have hs0 : 0<s := by linarith
    have ht0 := Real.smoothTransition.nonneg (2*s/c-1)
    have ht1 := Real.smoothTransition.le_one (2*s/c-1)
    by_cases ht : Real.smoothTransition (2*s/c-1)=1
    · simpa only [positiveClamp,ht,one_mul,sub_self,zero_mul,add_zero] using hs0
    · unfold positiveClamp
      exact add_pos_of_nonneg_of_pos (mul_nonneg ht0 hs0.le)
        (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht1 ht)) hc)

theorem positiveClamp_eq_of_le {c s : ℝ} (hc : 0<c) (hcs : c≤s) :
    positiveClamp c s=s := by
  have ht : 1≤2*s/c-1 := by
    have hh : 2≤2*s/c := (le_div_iff₀ hc).mpr (by linarith)
    linarith
  simp only [positiveClamp,Real.smoothTransition.one_of_one_le ht,one_mul,sub_self,zero_mul,add_zero]

theorem positiveClamp_contDiff (n : ℕ) (c : ℝ) : ContDiff ℝ n (positiveClamp c) := by
  have ht : ContDiff ℝ n (fun s : ℝ => Real.smoothTransition (2*s/c-1)) :=
    Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul contDiff_id).div_const c).sub contDiff_const)
  exact (ht.mul contDiff_id).add ((contDiff_const.sub ht).mul contDiff_const)

theorem exists_positive_near_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) {ρ : E→ℝ} {n : ℕ} (hρ : ContDiff ℝ n ρ)
    (hpos : ∀x∈K,0<ρ x) :
    ∃g : E→ℝ,ContDiff ℝ n g ∧ (∀x,0<g x) ∧ (∀x∈K,g=ᶠ[𝓝 x]ρ) := by
  obtain ⟨c,hc,hbound⟩ := hK.exists_forall_le' hρ.continuous.continuousOn hpos
  have hc' : 0<c/2 := by linarith
  refine ⟨fun x => positiveClamp (c/2) (ρ x),
    (positiveClamp_contDiff n (c/2)).comp hρ,fun x => positiveClamp_pos hc' (ρ x),?_⟩
  intro x hx
  have hl : c/2<ρ x := by have hh:=hbound x hx;linarith
  filter_upwards [hρ.continuous.continuousAt.eventually (Ioi_mem_nhds hl)] with y hy
  exact positiveClamp_eq_of_le hc' hy.le

theorem exists_positive_near_sphere {N : ℕ} {ρ : FiniteModel.Vector N→ℝ} {n : ℕ}
    (hρ : ContDiff ℝ n ρ) (hpos : ∀x,HardSphereDynamics.OnSphere x→0<ρ x) :
    ∃g : FiniteModel.Vector N→ℝ,ContDiff ℝ n g ∧ (∀x,0<g x) ∧
      (∀x,HardSphereDynamics.OnSphere x→g=ᶠ[𝓝 x]ρ) :=
  exists_positive_near_compact (SphereOnlyParameterIntegral.physicalSphere_compact N) hρ hpos

end SphericalAging.SmoothPositiveSpatialReplacement
