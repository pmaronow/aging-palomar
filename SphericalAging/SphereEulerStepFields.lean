module

public import SphericalAging.SphereEulerPredictable
public import SphericalAging.SphereEulerInterpolationAlgebra

public section

/-! Literal piecewise coefficient fields of the constructed Euler rows,
including exact single-interval evaluation and full product-measure identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped BigOperators NNReal ENNReal
namespace SphericalAging.SphereEulerStepFields
open HardSphereDynamics SphereEulerPredictable SphereEulerInterpolationAlgebra
open FourPapersCommon.FilteredBrownian
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
variable {E : Type*} [AddCommGroup E]

@[expose] def leftStep (h : ℝ≥0) (M : ℕ) (f : ℕ→Ω→E) (t : ℝ≥0) (omega : Ω) : E :=
  ∑k ∈ Finset.range M,if t∈Ioc (grid h k) (grid h (k+1)) then f k omega else 0

theorem leftStep_eq {h : ℝ≥0} {M k : ℕ} {t : ℝ≥0} (f : ℕ→Ω→E)
    (hk : k<M) (ht : t∈Ioc (grid h k) (grid h (k+1))) (omega : Ω) :
    leftStep h M f t omega=f k omega := by
  unfold leftStep
  rw [Finset.sum_eq_single k]
  · exact if_pos ht
  · intro j _ hjk
    exact if_neg (interval_disjoint h hjk ht)
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hk))

theorem leftStep_zero {h : ℝ≥0} {M : ℕ} {t : ℝ≥0} (f : ℕ→Ω→E)
    (ht : t∉Ioc (0:ℝ≥0) (grid h M)) (omega : Ω) : leftStep h M f t omega=0 := by
  apply Finset.sum_eq_zero
  intro k hk
  apply if_neg
  intro htk
  exact ht ⟨lt_of_le_of_lt (show (0:ℝ≥0)≤grid h k from bot_le) htk.1,
    htk.2.trans (grid_mono h (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))⟩

theorem leftStep_timeCut (h : ℝ≥0) (M : ℕ) (f : ℕ→Ω→ℝ) :
    (fun q : ℝ≥0×Ω => leftStep h M f q.1 q.2)=
      FourPapersCommon.continuousAdaptedTimeCut (leftStep h M f) (grid h M) := by
  funext q
  by_cases hq : q.1∈Ioc (0:ℝ≥0) (grid h M)
  · exact (if_pos hq).symm
  · rw [FourPapersCommon.continuousAdaptedTimeCut,if_neg hq,leftStep_zero f hq q.2]

section Measurable
variable [MeasurableSpace E] [MeasurableAdd₂ E]
theorem leftStep_measurable (h : ℝ≥0) (M : ℕ) (f : ℕ→Ω→E) (hf : ∀k,Measurable (f k)) :
    Measurable (fun q : ℝ≥0×Ω => leftStep h M f q.1 q.2) := by
  apply Finset.measurable_sum
  intro k _
  exact ((hf k).comp measurable_snd).ite (measurableSet_Ioc.preimage measurable_fst) measurable_const
end Measurable

theorem rows_ae (h : ℝ≥0) (M : ℕ) (Z : ∀k,lpMeas ℝ ℝ (F (grid h k)) 2 P)
    (f : ℕ→Ω→ℝ) (hf : ∀k,(Z k : Ω→ℝ)=ᵐ[P] f k) :
    ((∑k ∈ Finset.range M,elementaryPredictable F (grid h k) (grid h (k+1)) (Z k) :
      PredictableProcessL2 F P) : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => leftStep h M f q.1 q.2 := by
  have he (k : ℕ) : (elementaryPredictable F (grid h k) (grid h (k+1)) (Z k) : TimeProcessL2 P)=ᵐ[
      nonnegativeLebesgueMeasure.prod P]
      fun q => if q.1∈Ioc (grid h k) (grid h (k+1)) then f k q.2 else 0 := by
    have hz : (fun q : ℝ≥0×Ω => (Z k : Ω→ℝ) q.2)=ᵐ[nonnegativeLebesgueMeasure.prod P]
        (fun q => f k q.2) := Measure.quasiMeasurePreserving_snd.ae_eq_comp (hf k)
    filter_upwards [elementaryPredictable_coeFn F (grid h k) (grid h (k+1)) (Z k),hz] with q hh hz
    rw [hh]
    by_cases hq : q.1∈Ioc (grid h k) (grid h (k+1))
    · simp only [elementaryRepresentative,hq,ite_true,hz]
    · simp only [elementaryRepresentative,hq,ite_false]
  have hs := Lp.coeFn_fun_finsetSum (Finset.range M)
    (fun k => (elementaryPredictable F (grid h k) (grid h (k+1)) (Z k) : TimeProcessL2 P))
  simp only [Submodule.coe_sum]
  filter_upwards [hs,ae_all_iff.mpr he] with q hs he
  rw [hs]
  exact Finset.sum_congr rfl (fun k _ => he k)

variable (hN : 0<N) (D : BrownianDriver N P F) (β h : ℝ≥0)
  (J : FiniteModel.Disorder N p) (x : State N) (M : ℕ)

theorem driftRows_ae (i : Fin N) : (driftRows hN D β h J x M i : TimeProcessL2 P)=ᵐ[
    nonnegativeLebesgueMeasure.prod P]
    FourPapersCommon.continuousAdaptedTimeCut (leftStep h M (fun k => driftField D β h J x k i)) (grid h M) := by
  rw [←leftStep_timeCut]
  exact rows_ae h M (fun k => driftKnown hN D β h J x k i) _ (fun k =>
    boundedKnown_ae (P:=P) _ _ _ _ _)

theorem noiseRows_ae (i j : Fin N) : (noiseRows hN D β h J x M i j : TimeProcessL2 P)=ᵐ[
    nonnegativeLebesgueMeasure.prod P]
    FourPapersCommon.continuousAdaptedTimeCut (leftStep h M (fun k => noiseField D β h J x k i j)) (grid h M) := by
  rw [←leftStep_timeCut]
  exact rows_ae h M (fun k => noiseKnown hN D β h J x k i j) _ (fun k =>
    boundedKnown_ae (P:=P) _ _ _ _ _)
end SphericalAging.SphereEulerStepFields
