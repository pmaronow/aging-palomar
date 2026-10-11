module

public import SphericalAging.EuclideanNets

public section

/-! Genuine radius-normalized sphere nets for the Huang--Sellke
uniform-concentration step, with dimension-exponential cardinality. -/
noncomputable section
namespace SphericalAging.NormalizedSphereNets
open FiniteModel EuclideanNets

theorem radius_sphere_net (N : ℕ) (R : ℝ) (hR : 0≤R) {ε : ℝ} (hε : 0<ε) :
    ∃S : Finset (Vector N),
      (∀x∈S,‖x‖=R) ∧ (∀x : Vector N,‖x‖=R→∃y∈S,dist x y≤ε*R) ∧
      (S.card:ℝ)≤(1+2/ε)^N := by
  classical
  by_cases hzero : R=0
  · subst R
    refine ⟨{0},by simp,?_,?_⟩
    · intro x hx
      have hx0 : x=0 := norm_eq_zero.mp hx
      subst x
      exact ⟨0,by simp,by simp⟩
    · simp only [Finset.card_singleton,Nat.cast_one]
      exact one_le_pow₀ (le_add_of_nonneg_right (by positivity : (0:ℝ)≤2/ε))
  have hRp : 0<R := lt_of_le_of_ne hR (Ne.symm hzero)
  obtain ⟨S,hS,hcov,hcard⟩ := unit_sphere_net N hε
  refine ⟨S.image (fun x => R • x),?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hR,hS y hy,mul_one]
  · intro x hx
    have hu : ‖R⁻¹ • x‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hR),hx,inv_mul_cancel₀ hzero]
    obtain ⟨y,hy,hxy⟩ := hcov (R⁻¹ • x) hu
    refine ⟨R • y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,?_⟩
    have hid : R • (R⁻¹ • x)=x := by rw [smul_smul,mul_inv_cancel₀ hzero,one_smul]
    rw [←hid,dist_smul₀,Real.norm_eq_abs,abs_of_nonneg hR]
    exact (mul_le_mul_of_nonneg_left hxy hR).trans_eq (mul_comm R ε)
  · exact (Nat.cast_le.mpr Finset.card_image_le).trans hcard

theorem normalized_sphere_net (N : ℕ) (r : ℝ) (hr : 0≤r) (hr1 : r≤1)
    {η : ℝ} (hη : 0<η) :
    ∃S : Finset (Vector N),
      (∀x∈S,‖x‖^2=(N:ℝ)*r) ∧
      (∀x : Vector N,‖x‖^2=(N:ℝ)*r→∃y∈S,dist x y≤η*Real.sqrt (N:ℝ)) ∧
      (S.card:ℝ)≤(1+2/η)^N := by
  obtain ⟨S,hS,hcov,hcard⟩ := radius_sphere_net N (Real.sqrt ((N:ℝ)*r)) (Real.sqrt_nonneg _) hη
  refine ⟨S,?_,?_,hcard⟩
  · intro x hx
    rw [hS x hx,Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hr)]
  · intro x hx
    have hx' : ‖x‖=Real.sqrt ((N:ℝ)*r) := by rw [←hx,Real.sqrt_sq (norm_nonneg x)]
    obtain ⟨y,hy,hxy⟩ := hcov x hx'
    refine ⟨y,hy,hxy.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hη.le
    apply Real.sqrt_le_sqrt
    nlinarith [show (0:ℝ)≤(N:ℝ) from Nat.cast_nonneg N]

end SphericalAging.NormalizedSphereNets
