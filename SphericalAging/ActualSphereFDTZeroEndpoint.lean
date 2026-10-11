module

public import SphericalAging.ActualSphereForwardZeroEndpoint
public import SphericalAging.ActualSphereOnlyFDT

public section

/-! The actual quenched FDT has its genuine initial-time right derivative.
The local positive-time row equation and continuous physical current supply
the endpoint, without any off-domain extension of the evolution equation. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology NNReal InnerProductSpace
namespace SphericalAging.ActualSphereFDTZeroEndpoint
open FiniteModel HardSphereDynamics SphereInitialLaw SphereRotationGeometry
open SphereQuenchedFDT SphereFisherCurrent ActualSphereCurrent ActualSphereOnlyFDT
open ActualSphereGibbsDensity ActualSphereMeanSpatialInterface SphereOnlyFisherCurrentContinuity
variable {N p : ℕ}

theorem right_derivative_on_interval_of_continuousOn {f g : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hf : ContinuousOn f (Icc 0 b)) (hg : ContinuousOn g (Icc 0 b))
    (hd : ∀ s : ℝ, s ∈ Ioo 0 b → HasDerivAt f (g s) s) :
    HasDerivWithinAt f (g 0) (Ici 0) 0 := by
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  have hupper : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s < b :=
    nhdsWithin_le_nhds (Iio_mem_nhds hb)
  have hs : Ioo (0 : ℝ) b ∈ 𝓝[>] (0 : ℝ) := by
    filter_upwards [hpos, hupper] with s hs ht
    exact ⟨hs, ht⟩
  have he : (fun s => deriv f s) =ᶠ[𝓝[>] (0 : ℝ)] g := by
    filter_upwards [hs] with s hs
    exact (hd s hs).deriv
  have hfg : ContinuousWithinAt f (Ioo 0 b) 0 :=
    (hf 0 ⟨le_rfl, hb.le⟩).mono Ioo_subset_Icc_self
  have hgg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) := by
    apply (hg 0 ⟨le_rfl, hb.le⟩).mono_of_mem_nhdsWithin
    filter_upwards [hpos, hupper] with s hs ht
    exact ⟨hs.le, ht.le⟩
  exact hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt) hfg hs
    (hgg.congr' he.symm)

theorem right_derivative_on_interval {f g : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ s : ℝ, s ∈ Ioo 0 b → HasDerivAt f (g s) s) :
    HasDerivWithinAt f (g 0) (Ici 0) 0 := by
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  have hupper : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s < b :=
    nhdsWithin_le_nhds (Iio_mem_nhds hb)
  have hs : Ioo (0 : ℝ) b ∈ 𝓝[>] (0 : ℝ) := by
    filter_upwards [hpos, hupper] with s hs ht
    exact ⟨hs, ht⟩
  have he : (fun s => deriv f s) =ᶠ[𝓝[>] (0 : ℝ)] g := by
    filter_upwards [hs] with s hs
    exact (hd s hs).deriv
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    hf.continuousAt.continuousWithinAt hs
  exact (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm

theorem actual_quenched_fdt_hasDerivWithinAt (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ) ^ 2)
    (J : Disorder N p) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasDerivWithinAt
      (fun v => quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) t v)
      (quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) t s -
        current β R hR J t s) (Ici 0) s := by
  rcases hs.eq_or_lt with hzero | hpos
  · subst s
    exact right_derivative_on_interval hst
      (actual_quenchedCorrelation_row_continuous hN hp β R hR J t)
      ((actual_quenchedResponse_row_continuous hN hp β R hR J t).sub
        (actual_current_row_continuous hN hp β R hR hNR J t))
      (fun v hv => actual_quenched_fdt_hasDerivAt hN hp β R hR hNR J hv.1 hv.2)
  · exact (actual_quenched_fdt_hasDerivAt hN hp β R hR hNR J hpos hst).hasDerivWithinAt

theorem actual_quenched_fdt_current (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ) ^ 2)
    (J : Disorder N p) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) t s -
      derivWithin (fun v => quenchedCorrelation (forwardDensity β R hR J)
        (realMean β R hR J) t v) (Ici 0) s =
      (∫ x : Vector N, forwardDensity β R hR J s x *
        inner ℝ (realMean β R hR J (t - s) x)
          (tangentScore β J (forwardDensity β R hR J s) x) ∂sphereLaw N) / (N : ℝ) := by
  rw [(actual_quenched_fdt_hasDerivWithinAt hN hp β R hR hNR J hs hst).derivWithin
    (uniqueDiffOn_Ici (0 : ℝ) s hs), sub_sub_cancel]
  rfl

end SphericalAging.ActualSphereFDTZeroEndpoint
