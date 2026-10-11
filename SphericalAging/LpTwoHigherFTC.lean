module

public import SphericalAging.LpTwoHigherBall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

public section

/-! Actual L²-valued FTC retains a proved higher-Lp derivative bound. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal
namespace SphericalAging.LpTwoHigherFTC
open LpTwoHigherBall
set_option maxHeartbeats 480000
set_option backward.isDefEq.respectTransparency false
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure Ω}

theorem increment_eLpNorm_le (F G : ℝ→Lp E 2 μ) (hG : Continuous G)
    (hD : ∀r∈Icc (0:ℝ) 1,HasDerivAt F (G r) r)
    (p C : ℝ≥0∞) (hp : 1≤p)
    (hbound : ∀r∈Icc (0:ℝ) 1,eLpNorm (G r : Ω→E) p μ≤C) :
    eLpNorm ((F 1-F 0 : Lp E 2 μ):Ω→E) p μ≤C := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  letI : IsProbabilityMeasure ν := ⟨by simp [ν,Real.volume_Ioc]⟩
  have hi : Integrable G ν := (hG.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hh := integral_higherBall G hi p C hp (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hbound r ⟨hr.1.le,hr.2⟩)
  have hFTC : (∫r in (0:ℝ)..1,G r)=F 1-F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr => hD r (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hr))
      (hG.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] at hFTC
  change eLpNorm ((∫r in Ioc (0:ℝ) 1,G r : Lp E 2 μ):Ω→E) p μ≤C at hh
  rw [hFTC] at hh
  exact hh

end SphericalAging.LpTwoHigherFTC
