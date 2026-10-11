module

public import SphericalAging.SphereOnlyForwardCalculus
public import SphericalAging.SphereOnlyInitialFisher
public import SphericalAging.SphereOnlyFisherBudget

public section

/-! Initial growth and Gaussian disorder integrability for the realizable
sphere-only forward calculus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.SphereOnlyFisherGrowth
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphereRotationGeometry SphereFisherClock
open SphereOnlyForwardCalculus SphereOnlyInitialFisher SphereOnlyFisherBudget
open GaussianLandscape GaussianLandscapeMoments
open scoped Topology
variable {N p : ℕ} {β : ℝ}

theorem initial_fisher_growth_bound (hN : 0<N) (hp : 2≤p) (hβ : 0≤β)
    (J : Disorder N p) (D : SphereForwardData N p β J)
    (hinit : ∀x,x∈physicalSphere N→D.ρ 0 x=1) {t : ℝ} (ht : 0≤t) :
    fisherInformation β J (D.ρ t)/(N:ℝ) ≤
      β^2*(p:ℝ)^2*(landscapeNorm N p J)^2*Real.exp (curvatureRate β J*t) := by
  have hh := div_le_div_of_nonneg_right
    (D.fisher_exponential_comparison hN hp hβ (s:=0) (by norm_num) ht) (Nat.cast_nonneg N)
  simp only [sub_zero,mul_div_assoc] at hh
  have hi := initial_fisher_normalized_bound_onSphere hN β J
    ((D.spatial 0).of_le (by norm_num)) hinit
  exact hh.trans ((mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le).trans_eq (by ring))

theorem fisher_disorder_integrable (hN : 0<N) (hp : 2≤p) (hβ : 0≤β)
    (D : ∀J : Disorder N p,SphereForwardData N p β J)
    (hinit : ∀J x,x∈physicalSphere N→(D J).ρ 0 x=1)
    {t : ℝ} (ht : 0≤t)
    (hmeas : AEStronglyMeasurable (fun J => fisherInformation β J ((D J).ρ t)) (disorderLaw N p)) :
    Integrable (fun J => fisherInformation β J ((D J).ρ t)/(N:ℝ)) (disorderLaw N p) := by
  let b : ℝ := 2*β*(p:ℝ)^2*t
  have hExp := (uniform_exponential_moment (by omega : 1≤N) (by omega : 0<p) (b+2)).1
  apply (hExp.const_mul (β^2*(p:ℝ)^2)).mono' (by
    simpa only [div_eq_mul_inv] using hmeas.mul_const (N:ℝ)⁻¹)
  exact ae_of_all _ fun J => by
    have hn := fisher_nonnegative_onSphere hN β J ((D J).positive t)
    rw [Real.norm_of_nonneg (div_nonneg hn (Nat.cast_nonneg N))]
    have hg := initial_fisher_growth_bound hN hp hβ J (D J) (hinit J) ht
    have hq := landscapeNorm_nonnegative N p J
    have hqexp : landscapeNorm N p J≤Real.exp (landscapeNorm N p J) := by
      linarith [Real.add_one_le_exp (landscapeNorm N p J)]
    have hsq := (sq_le_sq₀ hq (Real.exp_pos _).le).mpr hqexp
    have he : Real.exp (landscapeNorm N p J)^2*Real.exp (curvatureRate β J*t)=
        Real.exp ((b+2)*landscapeNorm N p J) := by
      rw [←Real.exp_nat_mul,←Real.exp_add]
      congr 1
      dsimp only [b,curvatureRate]
      ring
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hsq (Real.exp_pos (curvatureRate β J*t)).le)
      (mul_nonneg (sq_nonneg β) (sq_nonneg (p:ℝ)))
    have hh' : β^2*(p:ℝ)^2*(landscapeNorm N p J)^2*Real.exp (curvatureRate β J*t) ≤
        β^2*(p:ℝ)^2*Real.exp ((b+2)*landscapeNorm N p J) := by
      calc
        _ = (β^2*(p:ℝ)^2)*((landscapeNorm N p J)^2*Real.exp (curvatureRate β J*t)) := by ring
        _ ≤ (β^2*(p:ℝ)^2)*(Real.exp (landscapeNorm N p J)^2*Real.exp (curvatureRate β J*t)) := hh
        _ = _ := by rw [he]
    exact hg.trans hh'

end SphericalAging.SphereOnlyFisherGrowth
