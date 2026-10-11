module

public import SphericalAging.ForkFisherMomentTransfer
public import SphericalAging.FisherIntervalTransfer

public section

/-! The actual finite Fisher-clock comparison error vanishes in the
ordered dimension then late-waiting limit, uniformly for a fixed fork window. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace SphericalAging.ForkFisherWindowLimit
open Set Filter MeasureTheory FiniteModel SphereFisherHelly
open scoped Topology

@[expose] def comparisonError (B L : ℝ) {N p : ℕ} {β : ℝ}
    (E : FisherDensity N p β) (T : ℝ) : ℝ :=
  B*Real.sqrt (L*(∫w in T..(T+L),E.full w))+2*Real.exp (-(N:ℝ))

theorem comparisonError_dimension_tendsto {p : ℕ} (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j)
    (hTop : Tendsto dim atTop atTop) (E : ∀j,FisherDensity (dim j) p β)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0))
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    (B : ℝ) {L T : ℝ} (hL : 0≤L) (hT : 0≤T) :
    Tendsto (fun j => comparisonError B L (E j) T) atTop
      (𝓝 (B*Real.sqrt (L*(∫w in T..(T+L),f w)))) := by
  have hh := FisherIntervalTransfer.interval_integral_tendsto_of_L1loc
    (fun j => ((E j).full_budget (by have h:=hDim j;omega) hp hβ).1) hi hL1
    hT (by linarith : T≤T+L)
  have hd : Tendsto (fun j => (dim j:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hTop
  have he : Tendsto (fun j => Real.exp (-(dim j:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hd)
  simpa only [comparisonError,mul_zero,add_zero] using
    ((hh.const_mul L).sqrt.const_mul B).add (he.const_mul 2)

theorem interval_mass_le_tail {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0))
    (hn : ∀t,0≤f t) {T L : ℝ} (hT : 0≤T) (hL : 0≤L) :
    (∫w in T..(T+L),f w)≤∫w in Ioi T,f w := by
  rw [intervalIntegral.integral_of_le (by linarith : T≤T+L)]
  exact setIntegral_mono_set (hi.mono_set (Ioi_subset_Ioi hT)) (ae_of_all _ hn)
    (ae_of_all volume (show Ioc T (T+L)⊆Ioi T from fun _ hw => hw.1))

theorem late_window_error_tendsto {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0))
    (hn : ∀t,0≤f t) {B L : ℝ} (hB : 0≤B) (hL : 0≤L)
    (T : ℕ→ℝ) (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => B*Real.sqrt (L*(∫w in T n..(T n+L),f w))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => ∫w in Ioi (T n),f w) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero hT
  refine squeeze_zero' (g:=fun n => B*Real.sqrt (L*(∫w in Ioi (T n),f w)))
    (Eventually.of_forall (fun n => by positivity)) ?_ ?_
  · filter_upwards [hT.eventually (eventually_ge_atTop (0:ℝ))] with n hnT
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left (interval_mass_le_tail hi hn hnT hL) hL)) hB
  · simpa only [mul_zero,Real.sqrt_zero] using (ht.const_mul L).sqrt.const_mul B

theorem ordered_comparisonError_eventually {p : ℕ} (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j)
    (hTop : Tendsto dim atTop atTop) (E : ∀j,FisherDensity (dim j) p β)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    {B L : ℝ} (hB : 0≤B) (hL : 0≤L) (T : ℕ→ℝ) (hT : Tendsto T atTop atTop)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠn in atTop,∀ᶠj in atTop,comparisonError B L (E j) (T n)<ε := by
  have ho := (late_window_error_tendsto hi hn hB hL T hT).eventually (gt_mem_nhds hε)
  filter_upwards [ho,hT.eventually (eventually_ge_atTop (0:ℝ))] with n hnε hnT
  exact (comparisonError_dimension_tendsto hp hβ dim hDim hTop E hi hL1 B hL hnT).eventually
    (gt_mem_nhds hnε)

end SphericalAging.ForkFisherWindowLimit
