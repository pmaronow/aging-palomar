module

public import SphericalAging.CKUniformLateEstimates

public section

/-! Stationarity of the actual translated CK correlation and multiplier,
derived from preceding Fisher increment controls and genuine translated limits. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.CKTranslatedStationarity
open Set Filter MeasureTheory CKSpecification CKUniformLateEstimates
open CKPhysicalConsequences UniformMultiplier
open scoped Topology

theorem increment_shift_tendsto_zero {a f : ℝ → ℝ} {B : ℝ}
    (han : ∀ u,0≤a u) (hi : IntegrableOn a (Ioi 0)) (hB : 0≤B)
    (hc : IncrementControl a f B) {S : ℕ → ℝ} (hS : Tendsto S atTop atTop) (θ : ℝ) :
    Tendsto (fun n => f (S n+θ)-f (S n)) atTop (𝓝 0) := by
  have hb := (bound_tendsto_zero a B |θ|).comp hS
  have hh : ∀ᶠ n in atTop,|f (S n+θ)-f (S n)|≤
      B*Real.sqrt (|θ| * tail a (S n-|θ|)) := by
    filter_upwards [hS.eventually_ge_atTop |θ|] with n hn
    exact uniform_late_shift han hi hB hc (abs_nonneg θ) hn le_rfl le_rfl
  exact squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hh)
    (by simpa only [Function.comp_def] using hb)

theorem waiting_shift_tendsto_zero {d : CKData} {a B : ℝ → ℝ}
    (han : ∀ u,0≤a u) (hi : IntegrableOn a (Ioi 0))
    (hB : ∀ L,0≤L → 0≤B L) (hc : WaitingControl d a B)
    {S : ℕ → ℝ} (hS : Tendsto S atTop atTop) {τ : ℝ} (hτ : 0≤τ) (θ : ℝ) :
    Tendsto (fun n => d.C (S n+θ+τ) (S n+θ)-d.C (S n+τ) (S n)) atTop (𝓝 0) :=
  increment_shift_tendsto_zero han hi (hB τ hτ) (hc τ hτ τ hτ le_rfl) hS θ

theorem correlation_limit_shift {p : ℕ} {β : ℝ} {d : CKData}
    (_h : CKEquations p β d) {a B : ℝ → ℝ} (han : ∀ u,0≤a u)
    (hi : IntegrableOn a (Ioi 0)) (hB : ∀ L,0≤L → 0≤B L)
    (hc : WaitingControl d a B) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    {C : ℝ×ℝ → ℝ} (hC : ∀ z : ℝ×ℝ,Tendsto
      (fun n => d.C (T n+z.1) (T n+z.2)) atTop (𝓝 (C z)))
    {x y : ℝ} (hxy : y≤x) (θ : ℝ) : C (x+θ,y+θ)=C (x,y) := by
  have ht : Tendsto (fun n => T n+y) atTop atTop := tendsto_atTop_add_const_right _ y hT
  have hh := waiting_shift_tendsto_zero han hi hB hc ht (sub_nonneg.mpr hxy) θ
  have hp := (hC (x+θ,y+θ)).sub (hC (x,y))
  have hz : Tendsto (fun n => d.C (T n+(x+θ)) (T n+(y+θ))-
      d.C (T n+x) (T n+y)) atTop (𝓝 0) := by
    convert hh using 1
    funext n
    congr 2 <;> ring
  exact sub_eq_zero.mp (tendsto_nhds_unique hp hz)

theorem correlation_limit_symmetric {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    {C : ℝ×ℝ → ℝ} (hC : ∀ z : ℝ×ℝ,Tendsto
      (fun n => d.C (T n+z.1) (T n+z.2)) atTop (𝓝 (C z))) (x y : ℝ) :
    C (x,y)=C (y,x) := by
  have he : (fun n => d.C (T n+x) (T n+y))=ᶠ[atTop]
      (fun n => d.C (T n+y) (T n+x)) := by
    filter_upwards [hT.eventually_ge_atTop (max (-x) (-y))] with n hn
    exact h.correlation_symmetric _ _ (by linarith [le_max_left (-x) (-y)])
      (by linarith [le_max_right (-x) (-y)])
  exact tendsto_nhds_unique (hC (x,y)) ((hC (y,x)).congr' he.symm)

theorem correlation_limit_profile {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a B : ℝ → ℝ} (han : ∀ u,0≤a u)
    (hi : IntegrableOn a (Ioi 0)) (hB : ∀ L,0≤L → 0≤B L)
    (hc : WaitingControl d a B) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    {C : ℝ×ℝ → ℝ} (hC : ∀ z : ℝ×ℝ,Tendsto
      (fun n => d.C (T n+z.1) (T n+z.2)) atTop (𝓝 (C z))) (x y : ℝ) :
    C (x,y)=C (|x-y|,0) := by
  rcases le_total y x with hxy | hyx
  · have hh := correlation_limit_shift h han hi hB hc hT hC hxy (-y)
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    simpa only [add_neg_cancel,sub_eq_add_neg] using hh.symm
  · rw [correlation_limit_symmetric h hT hC x y,abs_sub_comm]
    have hh := correlation_limit_shift h han hi hB hc hT hC hyx (-x)
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    simpa only [add_neg_cancel,sub_eq_add_neg] using hh.symm

theorem multiplier_limit_constant {p : ℕ} {β E : ℝ} {d : CKData}
    (h : CKEquations p β d) {a : ℝ → ℝ} (han : ∀ u,0≤a u)
    (hi : IntegrableOn a (Ioi 0)) (hE : 0≤E)
    (he : IncrementControl a (energy p β d) E)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    {L : ℝ → ℝ} (hL : ∀ x : ℝ,Tendsto (fun n => d.multiplier (T n+x)) atTop (𝓝 (L x)))
    (x : ℝ) : L x=L 0 := by
  have hz := (increment_shift_tendsto_zero han hi hE he hT x).const_mul ((p:ℝ)*β)
  have heq : (fun n => ((p:ℝ)*β)*(energy p β d (T n+x)-energy p β d (T n)))=ᶠ[atTop]
      (fun n => d.multiplier (T n+x)-d.multiplier (T n+0)) := by
    filter_upwards [hT.eventually_ge_atTop (max 0 (-x))] with n hn
    have h0 : 0≤T n := (le_max_left 0 (-x)).trans hn
    have hx : 0≤T n+x := by linarith [le_max_right 0 (-x)]
    have h₁ := multiplier_energy_identity h (T n+x) hx
    have h₂ := multiplier_energy_identity h (T n) h0
    simp only [add_zero]
    nlinarith only [h₁,h₂]
  have hp := (hL x).sub (hL 0)
  have hz' : Tendsto (fun n => d.multiplier (T n+x)-d.multiplier (T n+0)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hz.congr' heq
  exact sub_eq_zero.mp (tendsto_nhds_unique hp hz')

end SphericalAging.CKTranslatedStationarity
