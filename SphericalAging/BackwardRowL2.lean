module

public import SphericalAging.MonotoneResponseTail

public section

/-! Actual half-line L2 classes of causal backward-derivative rows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.BackwardRowL2
open CKSpecification EarlierCovariance GreenCovariance StrongBackwardDefect EarlierSmoothing

@[expose] def rayMeasure : Measure ℝ := volume.restrict (Ioi 0)

@[expose] def earlierRow (p : ℕ) (β : ℝ) (d : CKData) (t : ℝ) : ℝ→ℝ :=
  (Ioc 0 t).indicator (fun v => clampedEarlierSlope p β d t (t-v))

@[expose] def responseRow (d : CKData) (t : ℝ) : ℝ→ℝ :=
  (Ioc 0 t).indicator (fun v => clampedResponse d t (t-v))

theorem indicator_square {f : ℝ→ℝ} (s : Set ℝ) :
    (fun v => (s.indicator f v)^2)=s.indicator (fun v => (f v)^2) := by
  funext v
  by_cases hv : v∈s <;> simp [hv]

theorem causal_indicator_memLp_two {f : ℝ→ℝ} (hf : Continuous f) (t : ℝ) :
    MemLp ((Ioc 0 t).indicator f) 2 rayMeasure := by
  have hm : Measurable ((Ioc 0 t).indicator f) := hf.measurable.indicator measurableSet_Ioc
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  rw [indicator_square]
  have hi : Integrable ((Ioc 0 t).indicator (fun v => (f v)^2)) volume :=
    ((hf.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  exact hi.integrableOn

theorem earlierRow_memLp_two {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) : MemLp (earlierRow p β d t) 2 rayMeasure := by
  exact causal_indicator_memLp_two
    ((clampedEarlierSlope_continuous h).comp
      (by fun_prop : Continuous (fun v : ℝ => (t,t-v)))) t

theorem responseRow_memLp_two {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) : MemLp (responseRow d t) 2 rayMeasure := by
  exact causal_indicator_memLp_two
    ((clampedResponse_continuous h).comp
      (by fun_prop : Continuous (fun v : ℝ => (t,t-v)))) t

/-- The actual reversed causal integral equals the original earlier-time row. -/
theorem causal_square_integral {f : ℝ→ℝ} {t : ℝ} (ht : 0≤t) :
    (∫ v : ℝ,((Ioc 0 t).indicator (fun v => f (t-v)) v)^2 ∂rayMeasure)=
      ∫ s in (0:ℝ)..t,(f s)^2 := by
  rw [indicator_square,rayMeasure,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc (0:ℝ) t⊆Ioi 0 from fun _ hx => hx.1),
    ←intervalIntegral.integral_of_le ht]
  simpa only [sub_self,sub_zero] using
    intervalIntegral.integral_comp_sub_left (fun s => (f s)^2) t (a:=0) (b:=t)

/-- Exact L2 square of the reversed backward defect. -/
theorem defect_row_square {p : ℕ} {β : ℝ} {d : CKData} {t : ℝ} (ht : 0≤t) :
    (∫ v : ℝ,(earlierRow p β d t v-responseRow d t v)^2 ∂rayMeasure)=
      backwardErrorEnergy p β d t := by
  have he : (fun v => earlierRow p β d t v-responseRow d t v)=
      (Ioc 0 t).indicator (fun v => clampedEarlierSlope p β d t (t-v)-clampedResponse d t (t-v)) := by
    funext v
    by_cases hv : v∈Ioc 0 t <;> simp [earlierRow,responseRow,hv]
  have hi : (∫ v : ℝ,(earlierRow p β d t v-responseRow d t v)^2 ∂rayMeasure)=
      ∫ v : ℝ,((Ioc 0 t).indicator (fun v => clampedEarlierSlope p β d t (t-v)-clampedResponse d t (t-v)) v)^2 ∂rayMeasure := by
    apply integral_congr_ae
    exact ae_of_all _ (fun v => congrArg (fun x : ℝ => x^2) (congrFun he v))
  rw [hi,causal_square_integral (f:=fun s => clampedEarlierSlope p β d t s-clampedResponse d t s) ht]
  unfold backwardErrorEnergy
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  simp only [backwardErrorEnergy,backwardDefect,clampedEarlierSlope_eq hs.1 hs.2,
    clampedResponse_eq hs.1 hs.2]

end SphericalAging.BackwardRowL2
