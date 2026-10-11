module

public import SphericalAging.AsymptoticErrorTransfer
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

public section

/-! Source 11.11 Step 4: the time limit precedes removal of the approximation
error. Quantitative response bounds are proved from the actual error limits. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Filter Set
open scoped Topology
namespace SphericalAging.RemoteResponseScalarLimits

@[expose] def bound (p : ℕ) (Q βd δ ρ D ε γ κ : ℝ) : ℝ :=
  Q/2*(βd^(-((p:ℝ)⁻¹))*(δ+ρ*γ+D*(ε+κ))^((p:ℝ)⁻¹)+ε+κ)^2

theorem response_le_bound {p : ℕ} {Q βd δ ρ D ε γ κ S : ℝ}
    (hQ : 0<Q) (hβd : 0<βd) (hδ : 0≤δ) (hρ : 0≤ρ) (hD : 0≤D)
    (hε : 0≤ε) (hγ : 0≤γ) (hκ : 0≤κ) (hS : 0≤S)
    (h : Real.sqrt (2*S/Q)≤βd^(-((p:ℝ)⁻¹))*(δ+ρ*γ+D*(ε+κ))^((p:ℝ)⁻¹)+ε+κ) :
    S≤bound p Q βd δ ρ D ε γ κ := by
  have hr : 0≤βd^(-((p:ℝ)⁻¹))*(δ+ρ*γ+D*(ε+κ))^((p:ℝ)⁻¹)+ε+κ := by positivity
  have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) hr).mpr h
  rw [Real.sq_sqrt (by positivity)] at hh
  have hp := (div_le_iff₀ hQ).mp hh
  unfold bound
  nlinarith

theorem time_limit {p : ℕ} {Q βd δ ρ D : ℝ}
    (hQ : 0<Q) (hβd : 0<βd) (hδ : 0≤δ) (hρ : 0≤ρ) (hD : 0≤D)
    {S γ κ : ℕ→ℝ} (hS : ∀n,0≤S n) (hγ : ∀n,0≤γ n) (hκ : ∀n,0≤κ n)
    (hγLimit : Tendsto γ atTop (𝓝 0)) (hκLimit : Tendsto κ atTop (𝓝 0))
    (hpoint : ∀ε>0,∀n,Real.sqrt (2*S n/Q)≤
      βd^(-((p:ℝ)⁻¹))*(δ+ρ*γ n+D*(ε+κ n))^((p:ℝ)⁻¹)+ε+κ n) :
    IsBoundedUnder (·≤·) atTop S ∧
      limsup S atTop≤Q/2*(βd^(-((p:ℝ)⁻¹))*δ^((p:ℝ)⁻¹))^2 := by
  have hinner (ε : ℝ) : Tendsto (fun n => bound p Q βd δ ρ D ε (γ n) (κ n)) atTop
      (𝓝 (Q/2*(βd^(-((p:ℝ)⁻¹))*(δ+D*ε)^((p:ℝ)⁻¹)+ε)^2)) := by
    have hb := ((tendsto_const_nhds (x:=δ)).add (hγLimit.const_mul ρ)).add
      (((tendsto_const_nhds (x:=ε)).add hκLimit).const_mul D)
    have hr := (hb.rpow_const (Or.inr (by positivity : 0≤(p:ℝ)⁻¹))).const_mul
      (βd^(-((p:ℝ)⁻¹)))
    simpa only [bound,mul_zero,add_zero] using
      ((((hr.add_const ε).add hκLimit).pow 2).const_mul (Q/2))
  have hBound : IsBoundedUnder (·≤·) atTop S := by
    have hev := (hinner 1).eventually (eventually_lt_nhds
      (show Q/2*(βd^(-((p:ℝ)⁻¹))*(δ+D*1)^((p:ℝ)⁻¹)+1)^2<
        Q/2*(βd^(-((p:ℝ)⁻¹))*(δ+D*1)^((p:ℝ)⁻¹)+1)^2+1 by linarith))
    apply isBoundedUnder_of_eventually_le
    filter_upwards [hev] with n hn
    exact (response_le_bound hQ hβd hδ hρ hD (by norm_num) (hγ n) (hκ n)
      (hS n) (hpoint 1 (by norm_num) n)).trans hn.le
  refine ⟨hBound,?_⟩
  have hε (ε : ℝ) (hε : 0<ε) :
      limsup S atTop≤Q/2*(βd^(-((p:ℝ)⁻¹))*(δ+D*ε)^((p:ℝ)⁻¹)+ε)^2 := by
    have hh := limsup_le_limsup (Eventually.of_forall fun n =>
      response_le_bound hQ hβd hδ hρ hD hε.le (hγ n) (hκ n) (hS n) (hpoint ε hε n))
      (isCoboundedUnder_le_of_le atTop hS) (hinner ε).isBoundedUnder_le
    rw [(hinner ε).limsup_eq] at hh
    exact hh
  have houter : Tendsto
      (fun ε : ℝ => Q/2*(βd^(-((p:ℝ)⁻¹))*(δ+D*ε)^((p:ℝ)⁻¹)+ε)^2)
      (𝓝[>] (0:ℝ)) (𝓝 (Q/2*(βd^(-((p:ℝ)⁻¹))*δ^((p:ℝ)⁻¹))^2)) := by
    have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) :=
      (tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 (0:ℝ)) (𝓝 (0:ℝ))).mono_left inf_le_left
    have hb : Tendsto (fun ε : ℝ => δ+D*ε) (𝓝[>] (0:ℝ)) (𝓝 δ) := by
      simpa only [mul_zero,add_zero] using
        (tendsto_const_nhds (x:=δ)).add (hid.const_mul D)
    have hr := (hb.rpow_const (Or.inr (by positivity : 0≤(p:ℝ)⁻¹))).const_mul
      (βd^(-((p:ℝ)⁻¹)))
    simpa only [add_zero] using
      (((hr.add hid).pow 2).const_mul (Q/2))
  apply ge_of_tendsto houter
  filter_upwards [self_mem_nhdsWithin] with ε hε'
  exact hε ε hε'

theorem calibrated_power {p : ℕ} {Q βd δ : ℝ} (hβd : 0<βd) (hδ : 0≤δ) :
    Q/2*(βd^(-((p:ℝ)⁻¹))*δ^((p:ℝ)⁻¹))^2=
      Q/2*βd^(-(2/(p:ℝ)))*δ^(2/(p:ℝ)) := by
  rw [mul_pow,←Real.rpow_natCast,←Real.rpow_natCast,
    ←Real.rpow_mul hβd.le,←Real.rpow_mul hδ]
  norm_num only [Nat.cast_ofNat]
  have h1 : -((p:ℝ)⁻¹)*2=-(2/(p:ℝ)) := by rw [div_eq_mul_inv];ring
  have h2 : (p:ℝ)⁻¹*2=2/(p:ℝ) := by rw [div_eq_mul_inv];ring
  rw [h1,h2]
  ring

theorem real_ray_limsup_of_sequences {f : ℝ→ℝ} {B : ℝ} (hpos : ∀t,0≤f t)
    (hseq : ∀ (t : ℕ→ℝ),(∀n,0<t n)→Tendsto t atTop atTop→
      IsBoundedUnder (·≤·) atTop (fun n => f (t n)) ∧ limsup (fun n => f (t n)) atTop≤B) :
    IsBoundedUnder (·≤·) atTop f ∧ limsup f atTop≤B := by
  have hev (y : ℝ) (hy : B<y) : ∀ᶠt in atTop,f t<y := by
    by_contra hn
    have hbad : ∀T : ℝ,∃t : ℝ,T≤t ∧ y≤f t := by
      simpa only [eventually_atTop,not_exists,not_forall,not_lt,exists_prop] using hn
    choose t ht hft using fun n : ℕ => hbad ((n:ℝ)+1)
    have htime : Tendsto t atTop atTop := tendsto_atTop_mono ht
      (tendsto_atTop_add_const_right atTop 1
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop))
    have htp : ∀n,0<t n := fun n => lt_of_lt_of_le (by positivity) (ht n)
    have hr := hseq t htp htime
    have hyl : y≤limsup (fun n => f (t n)) atTop := by
      apply le_limsup_of_le hr.1
      intro b hb
      obtain ⟨n,hn⟩ := hb.exists
      exact (hft n).trans hn
    linarith [hr.2]
  have hBound : IsBoundedUnder (·≤·) atTop f :=
    isBoundedUnder_of_eventually_le ((hev (B+1) (by linarith)).mono fun _ h => h.le)
  exact ⟨hBound,(limsup_le_iff (isCoboundedUnder_le_of_le atTop hpos) hBound).mpr hev⟩

end SphericalAging.RemoteResponseScalarLimits
