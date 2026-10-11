module

public import SphericalAging.ActualFirstPassage

public section

/-! Actual selected-profile first passages need no extra window assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.FirstPassageSelected
open CKSpecification GeneralCenterDeficit PrefixRectangleStability ActualFirstPassage

theorem lag_window_uniform {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q A : ℝ} (H : SelectedInputs h c r q) (hA : 0≤A) :
    TendstoUniformlyOn (fun s u => d.C (s+u) s) c atTop (Icc 0 A) := by
  have hh := ((H.translated_correlation A hA).comp (fun u : ℝ => (u,0))).mono
    (show Icc 0 A⊆(fun u : ℝ => (u,0)) ⁻¹' square A from fun u hu => ⟨hu,⟨le_rfl,hA⟩⟩)
  have hh' : TendstoUniformlyOn (fun s u => d.C (s+u) s) (fun u => c |u|) atTop (Icc 0 A) := by
    simpa only [Function.comp_def,add_zero,sub_zero] using hh
  exact hh'.congr_right (fun u hu => congrArg c (abs_of_nonneg hu.1))

theorem actual_first_passages {p : ℕ} {β level : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q) (hl : level∈Ioo 0 q)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0)) :
    (∀s : ℝ,0≤s → 0<firstPassage d level s ∧
      d.C (s+firstPassage d level s) s=level ∧
      ∀u : ℝ,0≤u → u<firstPassage d level s → level<d.C (s+u) s) ∧
    Tendsto (firstPassage d level) atTop atTop :=
  ⟨fun s hs => firstPassage_spec h hs hl.1 (hl.2.trans H.plateau_lt_one) (hf s hs),
    firstPassage_tendsto h hl.1 hl.2 H.plateau_lt_one hf
      (fun u hu => (H.correlation_bounds u hu).1) (fun _ hA => lag_window_uniform H hA)⟩

end SphericalAging.FirstPassageSelected
