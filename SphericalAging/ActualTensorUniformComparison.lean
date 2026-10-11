module

public import SphericalAging.ActualTensorAnnealedComparison
public import SphericalAging.ForkFisherWindowLimit

public section

/-! Uniform fixed-window and genuine ordered dimension/late-time comparison
of the literal actual tensor products. -/
noncomputable section
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualTensorUniformComparison
open Set Filter MeasureTheory FiniteModel GaussianLandscape SphereFisherHelly
open SphereBadEventFisherMass SphereGoodEventFisherClock
open ActualSphereTensorProductCurrent ActualTensorAnnealedComparison ForkFisherWindowLimit
open scoped Topology NNReal

@[expose] def windowCoefficient (p k : ℕ) (β : ℝ≥0) (L : ℝ) : ℝ :=
  2*(k:ℝ)*Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*(2*L))

theorem actualTensorPairing_uniform_window_bound {N p k : ℕ}
    (hN : 2≤N) (hp : 2≤p) (hk : 1≤k) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (E : FisherDensity N p β)
    {T L a d : ℝ} (hT : 0≤T) (ha : a∈Icc 0 L) (hd : d∈Icc 0 L)
    (hmeas : AEStronglyMeasurable (fun J =>
      actualTensorPairing (k:=k) β R hR E J T a d a-
        actualTensorPairing (k:=k) β R hR E J T a d 0) (disorderLaw N p)) :
    |∫J,actualTensorPairing (k:=k) β R hR E J T a d a-
      actualTensorPairing (k:=k) β R hR E J T a d 0 ∂disorderLaw N p|≤
      comparisonError (windowCoefficient p k β L) L E T := by
  have hn : 0<N := by omega
  have hL : 0≤L := ha.1.trans ha.2
  have hA : 0≤cutoff p := by unfold cutoff;linarith [landscapeThreshold_pos p]
  have hcoef : 2*(k:ℝ)*Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*(a+d))≤
      windowCoefficient p k β L := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ha.2,hd.2]) (by positivity))
  have hi : IntervalIntegrable E.full volume T (T+L) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : T≤T+L)).mpr
      (((E.full_budget hn (by omega : 1≤p) β.coe_nonneg).1).mono_set
        (fun _ hw => lt_of_le_of_lt hT hw.1))
  have hmass : (∫w in T..(T+a),E.full w)≤∫w in T..(T+L),E.full w :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith [ha.1]) (by linarith [ha.2])
      (ae_of_all _ (fun w => E.full_nonneg w)) hi
  have hsqrt : Real.sqrt (a*(∫w in T..(T+a),E.full w))≤
      Real.sqrt (L*(∫w in T..(T+L),E.full w)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul ha.2 hmass
      (intervalIntegral.integral_nonneg_of_forall (by linarith [ha.1]) (fun w => E.full_nonneg w)) hL
  exact (actualTensorPairing_annealed_comparison hN hp hk β R hR hNR E hT ha.1 hd.1 hmeas).trans
    (add_le_add (mul_le_mul hcoef hsqrt (Real.sqrt_nonneg _) (by unfold windowCoefficient;positivity)) le_rfl)

theorem actualTensorPairing_ordered_uniform_comparison {p k : ℕ}
    (hp : 2≤p) (hk : 1≤k) (β : ℝ≥0) (dim : ℕ→ℕ)
    (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (R : ℕ→ℝ≥0) (hR : ∀j,0<(R j:ℝ)) (hNR : ∀j,(dim j:ℝ)<(R j:ℝ)^2)
    (E : ∀j,FisherDensity (dim j) p β)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    (T : ℕ→ℝ) (hT : ∀n,0≤T n) (hTTop : Tendsto T atTop atTop)
    {L : ℝ} (hL : 0≤L)
    (hmeas : ∀n j a d,a∈Icc 0 L→d∈Icc 0 L→AEStronglyMeasurable (fun J =>
      actualTensorPairing (k:=k) β (R j) (hR j) (E j) J (T n) a d a-
        actualTensorPairing (k:=k) β (R j) (hR j) (E j) J (T n) a d 0) (disorderLaw (dim j) p))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠn in atTop,∀ᶠj in atTop,∀a∈Icc 0 L,∀d∈Icc 0 L,
      |∫J,actualTensorPairing (k:=k) β (R j) (hR j) (E j) J (T n) a d a-
        actualTensorPairing (k:=k) β (R j) (hR j) (E j) J (T n) a d 0 ∂disorderLaw (dim j) p|<ε := by
  have hh := ordered_comparisonError_eventually (by omega : 1≤p) β.coe_nonneg dim hDim hTop E
    hi hn hL1 (show 0≤windowCoefficient p k β L by unfold windowCoefficient;positivity) hL T hTTop hε
  filter_upwards [hh] with n hnε
  filter_upwards [hnε] with j hjε
  intro a ha d hd
  exact (actualTensorPairing_uniform_window_bound (hDim j) hp hk β (R j) (hR j) (hNR j) (E j)
    (hT n) ha hd (hmeas n j a d ha hd)).trans_lt hjε

end SphericalAging.ActualTensorUniformComparison
