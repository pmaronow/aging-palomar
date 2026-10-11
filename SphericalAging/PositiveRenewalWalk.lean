module

public import SphericalAging.PositiveRenewalSeries
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Algebra.BigOperators.Intervals

public section

/-! The genuine iid positive renewal walk and its convolution-power laws. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace SphericalAging.PositiveRenewalWalk
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AbsorptionCutoff.Renewal

@[expose] abbrev WalkSpace := ℕ → ℝ
@[expose] def walkLaw (μ : Measure ℝ) : Measure WalkSpace := Measure.infinitePi (fun _ : ℕ => μ)
instance (μ : Measure ℝ) [IsProbabilityMeasure μ] : IsProbabilityMeasure (walkLaw μ) := by
  unfold walkLaw
  infer_instance

@[expose] def partialSum (n : ℕ) (ω : WalkSpace) : ℝ := ∑ i∈Finset.range n,ω i
@[expose] def shift (k : ℕ) (ω : WalkSpace) : WalkSpace := fun i => ω (k+i)
@[expose] def futureSum (k n : ℕ) (ω : WalkSpace) : ℝ := partialSum n (shift k ω)

theorem partialSum_zero (ω : WalkSpace) : partialSum 0 ω=0 := by simp [partialSum]
theorem partialSum_succ (n : ℕ) (ω : WalkSpace) : partialSum (n+1) ω=partialSum n ω+ω n :=
  Finset.sum_range_succ _ n

theorem partialSum_measurable (n : ℕ) : Measurable (partialSum n) := by
  exact Finset.measurable_fun_sum _ (fun i hi => measurable_pi_apply i)

theorem increments_independent (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    iIndepFun (fun n : ℕ => fun ω : WalkSpace => ω n) (walkLaw μ) := by
  exact iIndepFun_infinitePi (X:=fun _ : ℕ => (id : ℝ → ℝ)) (fun _ => measurable_id)

theorem increment_map_law (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    (walkLaw μ).map (fun ω => ω n)=μ := Measure.infinitePi_map_eval (fun _ : ℕ => μ) n

theorem partialSum_independent_next (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    IndepFun (partialSum n) (fun ω : WalkSpace => ω n) (walkLaw μ) := by
  have h := (increments_independent μ).indepFun_finsetSum_of_notMem
    (fun i : ℕ => measurable_pi_apply i) (Finset.notMem_range_self (n:=n))
  have heq : (∑ j∈Finset.range n,(fun ω : WalkSpace => ω j))=partialSum n := by
    funext ω
    exact Finset.sum_apply _ _ _
  rw [heq] at h
  exact h

theorem partialSum_map_law (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    (walkLaw μ).map (partialSum n)=convPow μ n := by
  induction n with
  | zero =>
      have heq : partialSum 0=(fun _ : WalkSpace => (0:ℝ)) := funext partialSum_zero
      rw [heq,Measure.map_const,measure_univ,one_smul,convPow_zero]
  | succ n ih =>
      have hfun : partialSum (n+1)=partialSum n+(fun ω : WalkSpace => ω n) := funext (partialSum_succ n)
      rw [hfun,(partialSum_independent_next μ n).map_add_eq_map_conv_map
        (partialSum_measurable n) (measurable_pi_apply n),ih,increment_map_law,convPow_succ]

theorem shift_map_law (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ) :
    (walkLaw μ).map (shift k)=walkLaw μ := by
  exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => Nat.add_left_cancel h)

theorem futureSum_map_law (μ : Measure ℝ) [IsProbabilityMeasure μ] (k n : ℕ) :
    (walkLaw μ).map (futureSum k n)=convPow μ n := by
  change (walkLaw μ).map (partialSum n ∘ shift k)=_
  rw [←Measure.map_map (partialSum_measurable n) (show Measurable (shift k) by
    exact measurable_pi_iff.mpr (fun i => measurable_pi_apply (k+i))),shift_map_law,partialSum_map_law]

theorem futureSum_eq_Ico (k n : ℕ) (ω : WalkSpace) :
    futureSum k n ω=∑i∈Finset.Ico k (k+n),ω i := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left,futureSum,partialSum,shift]

theorem partialSum_add (k n : ℕ) (ω : WalkSpace) :
    partialSum (k+n) ω=partialSum k ω+futureSum k n ω := by
  rw [futureSum_eq_Ico]
  exact Finset.sum_range_add_sum_Ico _ (Nat.le_add_right k n) |>.symm

theorem positive_increments_ae {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ x ∂μ,0<x) : ∀ᵐ ω ∂walkLaw μ,∀n : ℕ,0<ω n := by
  apply ae_all_iff.mpr
  intro n
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) n).quasiMeasurePreserving.ae hp

theorem partialSum_nonnegative {ω : WalkSpace} (hp : ∀n : ℕ,0<ω n) (n : ℕ) :
    0≤partialSum n ω := Finset.sum_nonneg (fun i hi => (hp i).le)

theorem partialSum_strictMono {ω : WalkSpace} (hp : ∀n : ℕ,0<ω n) :
    StrictMono (fun n => partialSum n ω) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [partialSum_succ]
  exact lt_add_of_pos_right _ (hp n)

end
end SphericalAging.PositiveRenewalWalk
