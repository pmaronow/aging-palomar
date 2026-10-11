module

public import SphericalAging.GaussianSeedOverlapBounds
public import SphericalAging.ExternalFieldSharpScalar

public section

/-! The genuine energy lower limit and the preceding absolute field cost
force the seed-overlap upper limit. No overlap conclusion is supplied. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.SeedCostAsymptotic
open Set Filter MeasureTheory
open scoped Topology

theorem seed_overlap_limsup_le {p : ℕ} (hp : 1≤p)
    {α δ E : ℝ} (hα : 0<α) (hδ : 0≤δ)
    {energy moment sphere gaussian err : ℕ→ℝ}
    (heBound : IsBoundedUnder (·≥·) atTop energy)
    (heLow : E-δ≤liminf energy atTop)
    (hcost : ∀ε>0,∀ᶠn in atTop,energy n+α*moment n≤E+ε)
    (hsphere : ∀n,0≤sphere n ∧ sphere n^p≤moment n)
    (hgauss : ∀n,0≤gaussian n ∧ gaussian n≤sphere n+err n)
    (herr : Tendsto err atTop (𝓝 0)) :
    limsup gaussian atTop≤(δ/α)^((p:ℝ)⁻¹) := by
  let r := (δ/α)^((p:ℝ)⁻¹)
  have hr : 0≤r := Real.rpow_nonneg (div_nonneg hδ hα.le) _
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  have hrp : r^p=δ/α := by
    rw [←Real.rpow_natCast]
    dsimp only [r]
    rw [←Real.rpow_mul (div_nonneg hδ hα.le),inv_mul_cancel₀ hp0,Real.rpow_one]
  have hev (y : ℝ) (hy : r<y) : ∀ᶠn in atTop,gaussian n<y := by
    obtain ⟨z,hz,hzy⟩ := exists_between hy
    have hz0 : 0<z := hr.trans_lt hz
    have hpow : r^p<z^p := pow_lt_pow_left₀ hz hr (by omega : p≠0)
    have hg : δ<α*z^p := by
      rw [hrp] at hpow
      simpa only [mul_comm] using (div_lt_iff₀ hα).mp hpow
    let ε := (α*z^p-δ)/4
    have hε : 0<ε := by dsimp only [ε];linarith
    have hlow := eventually_lt_of_lt_liminf (show E-δ-ε<liminf energy atTop by linarith) heBound
    have herror := herr.eventually (eventually_lt_nhds (show (0:ℝ)<y-z by linarith))
    filter_upwards [hlow,hcost ε hε,herror] with n hn hc hnerr
    have hm : sphere n^p<z^p := by
      have hh := mul_le_mul_of_nonneg_left (hsphere n).2 hα.le
      have ht : α*sphere n^p<α*z^p := by dsimp only [ε] at *;linarith
      nlinarith [hα]
    have hs : sphere n<z := by
      by_contra hh
      have hge : z≤sphere n := le_of_not_gt hh
      exact (not_lt_of_ge (pow_le_pow_left₀ hz0.le hge p)) hm
    exact lt_of_le_of_lt (hgauss n).2 (by linarith)
  have hBound : IsBoundedUnder (·≤·) atTop gaussian :=
    isBoundedUnder_of_eventually_le ((hev (r+1) (by linarith)).mono fun _ hn => hn.le)
  apply (limsup_le_iff (isCoboundedUnder_le_of_le atTop fun n => (hgauss n).1) hBound).mpr
  exact hev

end SphericalAging.SeedCostAsymptotic
