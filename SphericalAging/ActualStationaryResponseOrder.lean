module

public import SphericalAging.StationaryClusterInputs
public import SphericalAging.StationarySpectralRepresentation

public section

/-! The actual stationary response is antitone, derived from its constructed
spectral representation rather than supplied as an asymptotic hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.ActualStationaryResponseOrder
open CKSpecification StationaryClusterInputs

theorem response_antitone {p : ℕ} {β ell q : ℝ} {d : CKData} {h : CKEquations p β d}
    {T : ℕ → ℝ} {c r : ℝ → ℝ} (H : Cluster h T c r ell q) : AntitoneOn r (Ici 0) := by
  obtain ⟨ν,hν,hneg,hatom,hrep,hc,hr,hcm,hrm⟩ :=
    StationarySpectralRepresentation.stationary_cluster_spectral_representation h H.late
      H.correlation H.response H.multiplier H.fdt H.plateau
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f':=deriv r)
    (convex_Ici 0) H.stationary.continuous_r
  · intro t ht
    rw [interior_Ici] at ht
    exact (hr.differentiableOn (by simp) t ht).differentiableAt (Ioi_mem_nhds ht)
      |>.hasDerivAt.hasDerivWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hh := hrm 1 t ht
    simp only [iteratedDeriv_one,pow_one,neg_one_mul] at hh
    linarith

end SphericalAging.ActualStationaryResponseOrder
