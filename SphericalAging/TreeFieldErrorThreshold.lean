module

public import SphericalAging.FieldAlignedSphereBase

public section

/-! Constructed branching thresholds for the actual external-field
centroid correction. No small-correction conclusion is assumed. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.TreeFieldErrorThreshold
open FieldAlignedSphereBase

theorem field_correction_le (K d : ℕ) (hK : 0<K) (H ε : ℝ) (hH : 0≤H) (hε : 0<ε)
    (hnum : H^2≤(K:ℝ)*(d:ℝ)*ε^2) :
    H*Real.sqrt ((d:ℝ)/(K:ℝ))≤(d:ℝ)*ε := by
  have hk : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  have hd : 0≤(d:ℝ) := Nat.cast_nonneg d
  have hs : (Real.sqrt ((d:ℝ)/(K:ℝ)))^2=(d:ℝ)/(K:ℝ) :=
    Real.sq_sqrt (div_nonneg hd hk.le)
  have hprod := mul_le_mul_of_nonneg_right hnum hd
  have hb : (H*Real.sqrt ((d:ℝ)/(K:ℝ)))^2≤((d:ℝ)*ε)^2 := by
    rw [mul_pow,hs,←mul_div_assoc]
    apply (div_le_iff₀ hk).2
    nlinarith [hprod]
  have hl : 0≤H*Real.sqrt ((d:ℝ)/(K:ℝ)) := mul_nonneg hH (Real.sqrt_nonneg _)
  have hr : 0≤(d:ℝ)*ε := mul_nonneg hd hε.le
  nlinarith

theorem exists_field_branching_threshold (d : ℕ) (H ε : ℝ) (hH : 0≤H) (hε : 0<ε) :
    ∃K0 : ℕ,0<K0 ∧ ∀K≥K0,H*Real.sqrt ((d:ℝ)/(K:ℝ))≤(d:ℝ)*ε := by
  by_cases hd : d=0
  · refine ⟨1,by omega,?_⟩
    intro K hK
    simp [hd]
  · have hd0 : 0<(d:ℝ) := Nat.cast_pos.mpr (by omega)
    have hc : 0<(d:ℝ)*ε^2 := mul_pos hd0 (sq_pos_of_pos hε)
    obtain ⟨k,hk⟩ := exists_nat_gt (H^2/((d:ℝ)*ε^2))
    refine ⟨k+1,by omega,?_⟩
    intro K hK
    have hkr : (k:ℝ)≤(K:ℝ) := by exact_mod_cast (show k≤K by omega)
    have hh := (div_lt_iff₀ hc).mp hk
    apply field_correction_le K d (by omega) H ε hH hε
    exact hh.le.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hkr hc.le)

end SphericalAging.TreeFieldErrorThreshold
