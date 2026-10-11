module

public import SphericalAging.RecentWeightedResponseLimit

public section

/-! Complete local source12.1: both ordered weighted slow-response limits
and the full-row weighted signed-defect limit for the actual CK kernels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.WeightedSlowRatioTheorem
open CKSpecification CKPhysicalConsequences GeneralCenterDeficit PlateauAlgebra
  WeightedResponseIdentities RecentWeightedResponseLimit StrongBackwardDefect

@[expose] def slowRatio (p : ℕ) (q : ℝ) : ℝ := ((p:ℝ)-2)*(1-q)/q
@[expose] def defectBudget (p : ℕ) (q : ℝ) : ℝ := ((p:ℝ)-1)*q^p-((p:ℝ)-2)*q^(p-1)
@[expose] def oldWeightedMass (p : ℕ) (d : CKData) (A t : ℝ) : ℝ :=
  (p:ℝ)*(∫ u in (0:ℝ)..t-A,d.C t u^(p-1)*d.R t u)
@[expose] def ratioDenominator (p : ℕ) (d : CKData) (A t : ℝ) : ℝ :=
  d.C t (t-A)^p-d.C t 0^p
@[expose] def weightedSlowRatio (p : ℕ) (d : CKData) (A t : ℝ) : ℝ :=
  oldWeightedMass p d A t/ratioDenominator p d A t

theorem defectBudget_eq {p : ℕ} {q : ℝ} (hp : 1≤p) (hq : q≠0) :
    defectBudget p q=(1-slowRatio p q)*q^p := by
  have hn : p=(p-1)+1 := by omega
  have hpow : q^p=q^(p-1)*q := by
    nth_rw 1 [hn]
    rw [pow_succ]
  unfold defectBudget slowRatio
  rw [hpow]
  field_simp [hq]
  ring

theorem selected_energy_div {p : ℕ} {β q : ℝ} (hβ : β≠0) :
    selectedEnergy p β q/β=1-defectBudget p q := by
  unfold selectedEnergy defectBudget
  field_simp [hβ]
  ring

theorem oldWeightedMass_eq {p : ℕ} {β t A : ℝ} {d : CKData}
    (h : CKEquations p β d) (hA : 0≤A) (ht : A≤t) :
    oldWeightedMass p d A t=energy p β d t/β-
      (p:ℝ)*(∫ u in t-A..t,d.C t u^(p-1)*d.R t u) := by
  have hc := ((correlation_row_continuous h (hA.trans ht)).pow (p-1)).mul
    (response_row_continuous h)
  have hleft : IntervalIntegrable (fun u => d.C t u^(p-1)*d.R t u) volume 0 (t-A) :=
    (hc.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc (by linarith)
  have hright : IntervalIntegrable (fun u => d.C t u^(p-1)*d.R t u) volume (t-A) t :=
    (hc.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc (by linarith)
  have he := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hw := weighted_response_energy (t:=t) h
  unfold oldWeightedMass
  nlinarith

theorem oldWeightedMass_tendsto {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q A : ℝ} (H : SelectedInputs h c r q)
    (hE : Tendsto (energy p β d) atTop (𝓝 (selectedEnergy p β q))) (hA : 0≤A) :
    Tendsto (oldWeightedMass p d A) atTop (𝓝 (c A^p-defectBudget p q)) := by
  have hh := (hE.div_const β).sub (recent_weighted_response_limit H hA)
  rw [selected_energy_div h.beta_pos.ne'] at hh
  have he : 1-defectBudget p q-(1-c A^p)=c A^p-defectBudget p q := by ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop A] with t ht
  exact (oldWeightedMass_eq h hA ht).symm

theorem ratioDenominator_tendsto {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q A : ℝ} (H : SelectedInputs h c r q)
    (hforget : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0)) (hA : 0≤A) :
    Tendsto (ratioDenominator p d A) atTop (𝓝 (c A^p)) := by
  have hc := (recent_coefficients H hA ⟨hA,le_rfl⟩).1
  have he := (hc.pow p).sub ((hforget 0 le_rfl).pow p)
  have hp : p≠0 := by have hg:=h.spin_ge_three; omega
  change Tendsto (fun t => d.C t (t-A)^p-d.C t 0^p) atTop (𝓝 (c A^p))
  simpa only [zero_pow hp,sub_zero] using he

theorem source12_1 {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q)
    (hE : Tendsto (energy p β d) atTop (𝓝 (selectedEnergy p β q)))
    (hforget : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0)) :
    (∀A : ℝ,0<A →
      (∀ᶠ t : ℝ in atTop,0<ratioDenominator p d A t) ∧
      Tendsto (weightedSlowRatio p d A) atTop (𝓝 ((c A^p-defectBudget p q)/c A^p))) ∧
      Tendsto (fun A : ℝ => limUnder atTop (weightedSlowRatio p d A))
        atTop (𝓝 (slowRatio p q)) ∧
      Tendsto (fun t : ℝ => (p:ℝ)*(∫ u in (0:ℝ)..t,
        d.C t u^(p-1)*backwardDefect p β d t u)) atTop (𝓝 (defectBudget p q)) := by
  have hfix (A : ℝ) (hA : 0≤A) :
      (∀ᶠ t : ℝ in atTop,0<ratioDenominator p d A t) ∧
      Tendsto (weightedSlowRatio p d A) atTop (𝓝 ((c A^p-defectBudget p q)/c A^p)) := by
    have hcp : 0<c A := H.q_positive.trans_le (H.correlation_bounds A hA).1
    have hp : 0<c A^p := pow_pos hcp p
    have hd := ratioDenominator_tendsto H hforget hA
    exact ⟨hd.eventually (lt_mem_nhds hp),
      (oldWeightedMass_tendsto H hE hA).div hd hp.ne'⟩
  refine ⟨fun A hA => hfix A hA.le,?_,?_⟩
  · have hh := ((H.plateau_limit.pow p).sub_const (defectBudget p q)).div
      (H.plateau_limit.pow p) (pow_pos H.q_positive p).ne'
    have he : (q^p-defectBudget p q)/q^p=slowRatio p q := by
      rw [defectBudget_eq (by have hg:=h.spin_ge_three; omega) H.q_positive.ne']
      field_simp [(pow_pos H.q_positive p).ne']
      ring
    rw [he] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with A hA
    exact (hfix A hA).2.limUnder_eq.symm
  · have hp : p≠0 := by have hg:=h.spin_ge_three; omega
    have hh := ((tendsto_const_nhds (x:=(1:ℝ))).sub ((hforget 0 le_rfl).pow p)).sub
      (hE.div_const β)
    rw [selected_energy_div h.beta_pos.ne'] at hh
    have he : 1-(0:ℝ)^p-(1-defectBudget p q)=defectBudget p q := by rw [zero_pow hp]; ring
    rw [he] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact (weighted_defect_identity h ht).symm

end SphericalAging.WeightedSlowRatioTheorem
