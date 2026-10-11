module

public import SphericalAging.ActualSphereCKFisherClosure
public import SphericalAging.EarlierCovariance
public import SphericalAging.CKDiagonal

public section

/-! Remark 5.4: the Fisher bound includes both one-sided row endpoints.
The initial endpoint follows from the genuine continuous earlier slope and
right continuity of the extracted actual Fisher majorant. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace SphericalAging.RemarkFisherEndpoints
open CKSpecification EarlierCovariance GreenCovariance BackwardResponse StrongBackwardDefect
open ActualSphereCKFisherClosure
set_option maxHeartbeats 1200000

/-- Noise cancellation at the covariance diagonal fixes its earlier slope. -/
theorem earlierSlope_diagonal {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0≤t) :
    earlierSlope p β d t t=1 := by
  have hfirst : β^2*(p:ℝ)*((p:ℝ)-1)*
      (∫u in (0:ℝ)..t,d.C t u^(p-2)*d.R t u*d.C t u)=
      β^2*(∫u in (0:ℝ)..t,xiDoublePrime p (d.C t u)*d.R t u*d.C u t) := by
    simp only [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp only
    rw [h.correlation_symmetric u t hu.1 ht]
    unfold xiDoublePrime
    ring
  have hsecond : β^2*(p:ℝ)*(∫u in (0:ℝ)..t,d.R t u*d.C u t^(p-1))=
      β^2*(∫u in (0:ℝ)..t,xiPrime p (d.C t u)*d.R t u) := by
    simp only [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp only
    rw [h.correlation_symmetric u t hu.1 ht]
    unfold xiPrime
    ring
  have hd := CKDiagonal.correlation_diagonal_slope h ht
  unfold correlationSlope at hd
  rw [earlierSlope_eq ht le_rfl,hfirst,hsecond,h.response_diagonal t ht]
  linarith

/-- The diagonal earlier derivative is the left derivative, equal to one. -/
theorem correlation_diagonal_left_derivative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0<t) :
    HasDerivWithinAt (fun s=>d.C t s) 1 (Iic t) t := by
  rw [←earlierSlope_diagonal h ht.le]
  apply (correlation_earlier_hasDerivWithinAt h ht.le le_rfl).mono_of_mem_nhdsWithin
  exact inter_mem (nhdsWithin_le_nhds (Ici_mem_nhds ht)) self_mem_nhdsWithin

/-- Interior Fisher domination passes to time zero by a genuine one-sided limit. -/
theorem initial_Fisher_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a : ℝ→ℝ} (ha : FisherMajorant p β d a)
    (hac : ContinuousWithinAt a (Ici 0) 0) {t : ℝ} (ht : 0<t) :
    (earlierSlope p β d t 0-d.R t 0)^2≤a 0 := by
  have hc : Continuous (fun s : ℝ =>
      (clampedEarlierSlope p β d t s-clampedResponse d t s)^2) :=
    (((clampedEarlierSlope_continuous h).comp (continuous_const.prodMk continuous_id)).sub
      ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id))).pow 2
  have hleft := hc.continuousAt.tendsto.mono_left
    (show 𝓝[Ioi (0:ℝ)] 0≤𝓝 0 from nhdsWithin_le_nhds)
  have hright := hac.tendsto.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hbound : ∀ᶠs in 𝓝[Ioi (0:ℝ)] 0,
      (clampedEarlierSlope p β d t s-clampedResponse d t s)^2≤a s := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs hst
    rw [clampedEarlierSlope_eq hs.le hst.le,clampedResponse_eq hs.le hst.le]
    exact ha.dominates t s hs hst
  have hl := le_of_tendsto_of_tendsto hleft hright hbound
  simpa only [clampedEarlierSlope_eq (p:=p) (β:=β) (d:=d) le_rfl ht.le,
    clampedResponse_eq (d:=d) le_rfl ht.le] using hl

/-- The exact source endpoint assertions, with the bound on the full closed row. -/
theorem source5_4_of_Fisher {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a : ℝ→ℝ} (ha : FisherMajorant p β d a)
    (han : ∀s,0≤a s) (hac : ContinuousWithinAt a (Ici 0) 0) {t : ℝ} (ht : 0<t) :
    HasDerivWithinAt (fun s=>d.C t s) (earlierSlope p β d t 0) (Ici 0) 0 ∧
    (earlierSlope p β d t 0-d.R t 0)^2≤a 0 ∧
    HasDerivWithinAt (fun s=>d.C t s) 1 (Iic t) t ∧
    earlierSlope p β d t t=d.R t t ∧ d.R t t=1 ∧
    ∀s : ℝ,0≤s→s≤t→(earlierSlope p β d t s-d.R t s)^2≤a s := by
  refine ⟨correlation_earlier_initial_hasDerivWithinAt h ht,initial_Fisher_bound h ha hac ht,
    correlation_diagonal_left_derivative h ht,?_,h.response_diagonal t ht.le,?_⟩
  · rw [earlierSlope_diagonal h ht.le,h.response_diagonal t ht.le]
  · intro s hs hst
    by_cases hs0 : s=0
    · subst s
      exact initial_Fisher_bound h ha hac ht
    by_cases hst0 : s=t
    · subst s
      rw [earlierSlope_diagonal h ht.le,h.response_diagonal t ht.le]
      simpa using han t
    exact ha.dominates t s (lt_of_le_of_ne hs (Ne.symm hs0))
      (lt_of_le_of_ne hst hst0)

/-- The actual finite spherical Fisher extraction supplies the majorant used
by the endpoint result; no analytic Fisher input is assumed. -/
theorem source5_4 {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) :
    ∃a : ℝ→ℝ,FisherMajorant p β d a ∧ (∀s,0≤a s) ∧
      (∀s,ContinuousWithinAt a (Ici s) s) ∧ (∫s in Ioi 0,a s)≤β^2/2 ∧
      ∀t : ℝ,0<t→
        HasDerivWithinAt (fun s=>d.C t s) (earlierSlope p β d t 0) (Ici 0) 0 ∧
        (earlierSlope p β d t 0-d.R t 0)^2≤a 0 ∧
        HasDerivWithinAt (fun s=>d.C t s) 1 (Iic t) t ∧
        earlierSlope p β d t t=d.R t t ∧ d.R t t=1 ∧
        ∀s : ℝ,0≤s→s≤t→(earlierSlope p β d t s-d.R t s)^2≤a s := by
  let b : ℝ≥0 := ⟨β,h.beta_pos.le⟩
  have h' : CKEquations p b d := h
  have hTop : Tendsto (fun n : ℕ=>n+3) atTop atTop := tendsto_add_atTop_nat 3
  obtain ⟨_,φ,a,_,hF,_⟩ := actual_Fisher_closure b h' (fun n=>n+3) (fun n=>by omega) hTop
  refine ⟨a,hF.majorant,hF.nonneg,hF.right_continuous,hF.mass,?_⟩
  intro t ht
  exact source5_4_of_Fisher h hF.majorant hF.nonneg (hF.right_continuous 0) ht

end SphericalAging.RemarkFisherEndpoints
