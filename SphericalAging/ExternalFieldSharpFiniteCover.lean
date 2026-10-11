module

public import SphericalAging.ExternalFieldSharpScalar
public import Mathlib.Topology.Compactness.Compact

public section

/-! A constructed finite cover for the exact manuscript beta_d coefficient.
No conjugate ceiling or finite-grid conclusion is a hypothesis. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace SphericalAging.ExternalFieldSharpFiniteCover
open Set PlateauAlgebra ExternalFieldElementaryPenalty ExternalFieldSharpScalar

 theorem exists_finite_fields {p : ℕ} (hp : 3≤p) {ε : ℝ} (hε : 0<ε) :
    ∃G : Finset ℝ,0∈G ∧ (∀κ∈G,0≤κ) ∧
      ∀a∈Icc (0:ℝ) 1,∃κ∈G,
        algorithmicField p κ-κ*a+betaD p*a^p<thresholdEnergy p+ε := by
  classical
  have hm : ∀a : Icc (0:ℝ) 1,∃κ≥0,
      algorithmicField p κ-κ*a.val+betaD p*a.val^p<thresholdEnergy p+ε :=
    fun a => sharp_field_approximation hp hε a.property
  choose κ hκ hc using hm
  let U : Icc (0:ℝ) 1→Set ℝ := fun a =>
    {b | algorithmicField p (κ a)-κ a*b+betaD p*b^p<thresholdEnergy p+ε}
  have hU a : IsOpen (U a) := isOpen_lt
    ((continuous_const.sub (continuous_const.mul continuous_id)).add
      (continuous_const.mul (continuous_id.pow p))) continuous_const
  have hcover : Icc (0:ℝ) 1⊆⋃a,U a := by
    intro b hb
    exact mem_iUnion.mpr ⟨⟨b,hb⟩,hc ⟨b,hb⟩⟩
  obtain ⟨s,hs⟩ := isCompact_Icc.elim_finite_subcover U hU hcover
  refine ⟨insert 0 (s.image κ),Finset.mem_insert_self _ _,?_,?_⟩
  · intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact le_rfl
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hk
      exact hκ a
  · intro a ha
    obtain ⟨b,hb⟩ := mem_iUnion.mp (hs ha)
    obtain ⟨hb,hcost⟩ := mem_iUnion.mp hb
    exact ⟨κ b,Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b,hb,rfl⟩),hcost⟩

end SphericalAging.ExternalFieldSharpFiniteCover
