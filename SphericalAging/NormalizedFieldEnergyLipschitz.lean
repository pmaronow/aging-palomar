module

public import SphericalAging.ForkEnergyComparison

public section

/-! Actual normalized Hamiltonian plus field perturbation cost on the ball,
derived from the original tensor landscape norm. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.NormalizedFieldEnergyLipschitz
open FiniteModel GaussianLandscape ForkEnergyComparison
open scoped InnerProductSpace

@[expose] def energy {N p : ℕ} (J : Disorder N p) (h x : Vector N) : ℝ :=
  Hamiltonian N p J x/(N:ℝ)+⟪h,x⟫_ℝ/(N:ℝ)

theorem actual_energy_distance {N p : ℕ} (hN : 0<N) (J : Disorder N p)
    (h x y : Vector N) (H : ℝ) (hH : 0≤H) (hh : ‖h‖≤Real.sqrt N*H)
    (hx : ‖x‖≤Real.sqrt N) (hy : ‖y‖≤Real.sqrt N) :
    |energy J h x-energy J h y|≤
      ((p:ℝ)*landscapeNorm N p J+H)*(‖x-y‖/Real.sqrt N) := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNr
  have hham := Hamiltonian_ball_lipschitz hN (by norm_num : (0:ℝ)≤1) J
    (by simpa only [one_mul] using hx) (by simpa only [one_mul] using hy)
  simp only [one_pow,mul_one] at hham
  have hfield : |⟪h,x-y⟫_ℝ|≤Real.sqrt N*H*‖x-y‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _))
  have hd : Real.sqrt (N:ℝ)/(N:ℝ)=1/Real.sqrt (N:ℝ) := by
    apply (div_eq_div_iff hNr.ne' hs.ne').mpr
    simpa only [one_mul] using Real.mul_self_sqrt hNr.le
  have he : energy J h x-energy J h y=
      ((Hamiltonian N p J x-Hamiltonian N p J y)+⟪h,x-y⟫_ℝ)/(N:ℝ) := by
    unfold energy;rw [inner_sub_right];ring
  rw [he,abs_div,abs_of_pos hNr]
  calc
    _≤(|Hamiltonian N p J x-Hamiltonian N p J y|+|⟪h,x-y⟫_ℝ|)/(N:ℝ) :=
      div_le_div_of_nonneg_right (abs_add_le _ _) hNr.le
    _≤((p:ℝ)*landscapeNorm N p J*Real.sqrt N*‖x-y‖+Real.sqrt N*H*‖x-y‖)/(N:ℝ) :=
      div_le_div_of_nonneg_right (add_le_add hham hfield) hNr.le
    _=(((p:ℝ)*landscapeNorm N p J+H)*‖x-y‖)*(Real.sqrt N/(N:ℝ)) := by ring
    _=_ := by rw [hd];ring

theorem actual_energy_error {N p : ℕ} (hN : 0<N) (J : Disorder N p)
    (h x y : Vector N) (C H ε : ℝ) (hC : landscapeNorm N p J≤C) (hH : 0≤H)
    (hh : ‖h‖≤Real.sqrt N*H) (hx : ‖x‖≤Real.sqrt N) (hy : ‖y‖≤Real.sqrt N)
    (hd : ‖x-y‖/Real.sqrt N≤ε) :
    |energy J h x-energy J h y|≤((p:ℝ)*C+H)*ε := by
  have hQ : 0≤landscapeNorm N p J := by unfold landscapeNorm;positivity
  have hcn : 0≤C := hQ.trans hC
  have hc : (p:ℝ)*landscapeNorm N p J+H≤(p:ℝ)*C+H :=
    add_le_add_left (mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg p)) H
  exact (actual_energy_distance hN J h x y H hH hh hx hy).trans
    (mul_le_mul hc hd (by positivity) (by positivity))

end SphericalAging.NormalizedFieldEnergyLipschitz
