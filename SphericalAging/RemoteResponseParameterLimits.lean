module

public import SphericalAging.ForkParameterLimits
public import SphericalAging.ExternalFieldSharpScalar

public section

/-! Actual source 11.11 fork deficits and response bounds. Source 10.5's
ordered normalization and source 8.2's equality case give age saturation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
open Filter Set
open scoped Topology
namespace SphericalAging.RemoteResponseParameterLimits
open ProfileCenterEnergy ForkParameterBounds ForkParameterLimits PlateauAlgebra
open ExternalFieldElementaryPenalty ExternalFieldSharpScalar

@[expose] def branchDeficit (p : ℕ) (β e : ℝ) (c r : ℝ→ℝ) (K : ℕ) (L : ℝ) : ℝ :=
  thresholdEnergy p-forkEnergy p β e c r K L/(forkNorm c K L)^((p:ℝ)/2)
@[expose] def profileDeficit (p : ℕ) (β e : ℝ) (c r : ℝ→ℝ) (L : ℝ) : ℝ :=
  thresholdEnergy p-prefixEnergy p β e c r L/(c (2*L))^((p:ℝ)/2)
@[expose] def branchBound (p : ℕ) (β e : ℝ) (c r : ℝ→ℝ) (K : ℕ) (L : ℝ) : ℝ :=
  forkNorm c K L/2*(betaD p)^(-(2/(p:ℝ)))*(branchDeficit p β e c r K L)^(2/(p:ℝ))
@[expose] def profileBound (p : ℕ) (β e : ℝ) (c r : ℝ→ℝ) (L : ℝ) : ℝ :=
  c (2*L)/2*(betaD p)^(-(2/(p:ℝ)))*(profileDeficit p β e c r L)^(2/(p:ℝ))

theorem branch_deficit_nonneg {p K : ℕ} {β e L : ℝ} {c r : ℝ→ℝ}
    (hQ : 0<forkNorm c K L)
    (hCeiling : forkEnergy p β e c r K L≤thresholdEnergy p*(forkNorm c K L)^((p:ℝ)/2)) :
    0≤branchDeficit p β e c r K L := by
  exact sub_nonneg.mpr ((div_le_iff₀ (Real.rpow_pos_of_pos hQ _)).mpr hCeiling)

theorem branch_deficit_tendsto {p : ℕ} {β e q L : ℝ} {c r : ℝ→ℝ}
    (H : Profile c r q) (hβ : 0≤β) (hL : 0≤L) (hq : 0<q)
    (hr : ∀u,0<u→0≤r u) :
    Tendsto (fun K : ℕ => branchDeficit p β e c r K L) atTop
      (𝓝 (profileDeficit p β e c r L)) :=
  tendsto_const_nhds.sub (normalized_branch_tendsto H hβ hL hq hr)

theorem branch_bound_tendsto {p : ℕ} {β e q L : ℝ} {c r : ℝ→ℝ}
    (H : Profile c r q) (hβ : 0≤β) (hL : 0≤L) (hq : 0<q)
    (hr : ∀u,0<u→0≤r u) :
    Tendsto (fun K : ℕ => branchBound p β e c r K L) atTop
      (𝓝 (profileBound p β e c r L)) := by
  exact (((norm_branch_tendsto H hL).div_const 2).mul_const ((betaD p)^(-(2/(p:ℝ))))).mul
    ((branch_deficit_tendsto H hβ hL hq hr).rpow_const (Or.inr (by positivity : 0≤2/(p:ℝ))))

theorem profile_deficit_tendsto {p : ℕ} {β ell e q : ℝ} {c r : ℝ→ℝ}
    (hp : 3≤p) (hβ : 0<β) (H : Profile c r q) (hq : 0<q) (hq1 : q<1)
    (hell : ell=multiplier p β q) (he : e=(ell-1)/((p:ℝ)*β))
    (hr : ∀u,0<u→0≤r u) (hm : β^2*marginalityPolynomial p q=1) :
    Tendsto (profileDeficit p β e c r) atTop (𝓝 0) := by
  have ho := ordered_normalization hp hβ H hq hq1 hell he hr hm
  have hh := ho.2.congr' (by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    exact (ho.1 L hL).limUnder_eq)
  change Tendsto (fun L => thresholdEnergy p-prefixEnergy p β e c r L/(c (2*L))^((p:ℝ)/2))
    atTop (𝓝 0)
  simpa only [show TreeEnergyCeilings.threshold p=thresholdEnergy p from rfl,sub_self] using
    (tendsto_const_nhds (x:=thresholdEnergy p)).sub hh

theorem profile_bound_tendsto {p : ℕ} {β ell e q : ℝ} {c r : ℝ→ℝ}
    (hp : 3≤p) (hβ : 0<β) (H : Profile c r q) (hq : 0<q) (hq1 : q<1)
    (hell : ell=multiplier p β q) (he : e=(ell-1)/((p:ℝ)*β))
    (hr : ∀u,0<u→0≤r u) (hm : β^2*marginalityPolynomial p q=1) :
    Tendsto (profileBound p β e c r) atTop (𝓝 0) := by
  have hd := profile_deficit_tendsto hp hβ H hq hq1 hell he hr hm
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hexp : 0<2/(p:ℝ) := div_pos (by norm_num) hp0
  have hpow := hd.rpow_const (Or.inr hexp.le)
  rw [Real.zero_rpow hexp.ne'] at hpow
  have hc := (prefix_age_limits hp hβ H hq1 hell he).1
  change Tendsto (fun L => c (2*L)/2*(betaD p)^(-(2/(p:ℝ)))*
    (profileDeficit p β e c r L)^(2/(p:ℝ))) atTop (𝓝 0)
  simpa only [mul_zero] using
    ((hc.div_const 2).mul_const ((betaD p)^(-(2/(p:ℝ))))).mul hpow

end SphericalAging.RemoteResponseParameterLimits
