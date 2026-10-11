module

public import SphericalAging.ExternalFieldElementaryPenalty
public import Mathlib.Topology.Compactness.Compact

public section

/-! Compactness constructs an actual finite family of fields that uniformly
approximates the proved positive all-p overlap penalty. No finite-grid cost
or uniform conjugate approximation is among the hypotheses. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace SphericalAging.ExternalFieldFiniteCover
open Set ExternalFieldElementaryPenalty

 theorem exists_finite_fields {p : ℕ} (hp : 3≤p) {ε : ℝ} (hε : 0<ε) :
    ∃G : Finset ℝ,0∈G ∧ (∀κ∈G,0≤κ ∧ κ≤criticalField p) ∧
      ∀a∈Icc (0:ℝ) 1,∃κ∈G,
        algorithmicField p κ-κ*a+elementaryPenalty p*a^p<thresholdEnergy p+ε := by
  classical
  let κ : Icc (0:ℝ) 1→ℝ := fun a => criticalField p*a.val^(p-1)
  let U : Icc (0:ℝ) 1→Set ℝ := fun a =>
    {b | algorithmicField p (κ a)-κ a*b+elementaryPenalty p*b^p<thresholdEnergy p+ε}
  have hU a : IsOpen (U a) := isOpen_lt
    ((continuous_const.sub (continuous_const.mul continuous_id)).add
      (continuous_const.mul (continuous_id.pow p))) continuous_const
  have hcover : Icc (0:ℝ) 1⊆⋃a,U a := by
    intro b hb
    apply mem_iUnion.mpr
    refine ⟨⟨b,hb⟩,?_⟩
    have he := matched_field_cost hp hb
    change algorithmicField p (criticalField p*b^(p-1))-criticalField p*b^(p-1)*b+
      elementaryPenalty p*b^p<thresholdEnergy p+ε
    rw [he]
    linarith
  obtain ⟨s,hs⟩ := isCompact_Icc.elim_finite_subcover U hU hcover
  refine ⟨insert 0 (s.image κ),Finset.mem_insert_self _ _,?_,?_⟩
  · intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact ⟨le_rfl,(criticalField_positive hp).le⟩
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hk
      exact ⟨mul_nonneg (criticalField_positive hp).le (pow_nonneg a.property.1 _),
        mul_le_of_le_one_right (criticalField_positive hp).le (pow_le_one₀ a.property.1 a.property.2)⟩
  · intro a ha
    obtain ⟨b,hb⟩ := mem_iUnion.mp (hs ha)
    obtain ⟨hb,hcost⟩ := mem_iUnion.mp hb
    exact ⟨κ b,Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b,hb,rfl⟩),hcost⟩

end SphericalAging.ExternalFieldFiniteCover
