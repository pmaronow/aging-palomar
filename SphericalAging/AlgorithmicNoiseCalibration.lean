module

public import SphericalAging.ContinuousMonotoneCalibration
public import SphericalAging.PartialVarianceBranchingCoefficients

public section

/-! Calibrate every actual overlap level while preserving literal independent
root and original-disorder leaf endpoints, even for a flat correlation. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace SphericalAging.AlgorithmicNoiseCalibration
open Set ContinuousMonotoneCalibration

@[expose] def levelParameter (χ : ℝ→ℝ) (hχ : ContinuousOn χ (Icc 0 1)) (q : ℕ→ℝ)
    (D l : ℕ) : ℝ := if l=0 then 0 else if D≤l then 1 else parameter χ hχ (q l)

theorem levelParameter_mem (χ : ℝ→ℝ) (hχ : ContinuousOn χ (Icc 0 1)) (q : ℕ→ℝ)
    (hrange : ∀l,q l∈Icc (χ 0) (χ 1)) (D l : ℕ) : levelParameter χ hχ q D l∈Icc 0 1 := by
  unfold levelParameter
  split_ifs
  · exact ⟨le_refl _,by norm_num⟩
  · exact ⟨by norm_num,le_refl _⟩
  · exact parameter_mem χ hχ _ (hrange l)

theorem levelParameter_monotone (χ : ℝ→ℝ) (hχ : ContinuousOn χ (Icc 0 1))
    (hm : MonotoneOn χ (Icc 0 1)) (q : ℕ→ℝ) (hq : Monotone q)
    (hrange : ∀l,q l∈Icc (χ 0) (χ 1)) (D : ℕ) : Monotone (levelParameter χ hχ q D) := by
  intro a b hab
  by_cases ha : a=0
  · subst a
    simpa [levelParameter] using (levelParameter_mem χ hχ q hrange D b).1
  by_cases hb : D≤b
  · have hbone : levelParameter χ hχ q D b=1 := by
      have hbn : b≠0 := by intro h;subst b;omega
      simp only [levelParameter,if_neg hbn,if_pos hb]
    rw [hbone]
    exact (levelParameter_mem χ hχ q hrange D a).2
  have hbn : b≠0 := by intro h;subst b;omega
  have han : ¬D≤a := by omega
  simp only [levelParameter,if_neg ha,if_neg hbn,if_neg hb,if_neg han]
  exact parameter_monotoneOn χ hχ hm (hrange a) (hrange b) (hq hab)

theorem levelParameter_spec (χ : ℝ→ℝ) (hχ : ContinuousOn χ (Icc 0 1)) (q : ℕ→ℝ)
    (hrange : ∀l,q l∈Icc (χ 0) (χ 1)) (D : ℕ) (hD : 0<D)
    (hzero : q 0=χ 0) (hterminal : q D=χ 1) (l : ℕ) (hl : l≤D) :
    χ (levelParameter χ hχ q D l)=q l := by
  by_cases h0 : l=0
  · subst l;simp only [levelParameter,if_pos rfl];exact hzero.symm
  by_cases hlast : D≤l
  · have heq : l=D := by omega
    subst l
    simp only [levelParameter,if_neg h0,if_pos (le_refl D)]
    exact hterminal.symm
  · simp only [levelParameter,if_neg h0,if_neg hlast]
    exact parameter_spec χ hχ _ (hrange l)

@[expose] def varianceSchedule (χ : ℝ→ℝ) (hχ : ContinuousOn χ (Icc 0 1)) (q : ℕ→ℝ) (D j : ℕ) : ℝ :=
  levelParameter χ hχ q D (D-j)

theorem actual_calibrated_variance_schedule (χ : ℝ→ℝ) (hχ : ContinuousOn χ (Icc 0 1))
    (hm : MonotoneOn χ (Icc 0 1)) (q : ℕ→ℝ) (hq : Monotone q)
    (hrange : ∀l,q l∈Icc (χ 0) (χ 1)) (D : ℕ) (hD : 0<D)
    (hzero : q 0=χ 0) (hterminal : q D=χ 1) :
    let V := varianceSchedule χ hχ q D
    V 0=1 ∧ V D=0 ∧ (∀j,V j∈Icc 0 1) ∧ (∀j,V (j+1)≤V j) ∧
      ∀l,l≤D→χ (V (D-l))=q l := by
  have hmlevel := levelParameter_monotone χ hχ hm q hq hrange D
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [varianceSchedule,levelParameter,hD.ne']
  · simp [varianceSchedule,levelParameter]
  · intro j;exact levelParameter_mem χ hχ q hrange D _
  · intro j;exact hmlevel (Nat.sub_le_sub_left (Nat.le_succ j) D)
  · intro l hl
    have he : D-(D-l)=l := Nat.sub_sub_self hl
    simpa only [varianceSchedule,he] using levelParameter_spec χ hχ q hrange D hD hzero hterminal l hl

end SphericalAging.AlgorithmicNoiseCalibration
