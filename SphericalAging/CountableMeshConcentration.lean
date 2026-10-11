module

public import Mathlib.MeasureTheory.Function.L2Space
public import SphericalAging.CountableCenteredSup
public import SphericalAging.BoundedMeshMeanComparison

public section

/-! Finite mesh variances and an actual sample-path good event bound the
expected square of a bounded countable centered supremum. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SphericalAging.CountableMeshConcentration
open CountableCenteredSup BoundedMeshMeanComparison
variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Countable ι] [Nonempty ι] [Fintype κ]
    {P : Measure Ω} [IsProbabilityMeasure P]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose] def meshEnergy (Z : κ→Ω→ℝ) (P : Measure Ω) (ω : Ω) : ℝ :=
  ∑k : κ,(Z k ω-∫z,Z k z ∂P)^2

theorem centeredSup_integral_square_le (Y : ι→Ω→ℝ) (Z : κ→Ω→ℝ) (π : ι→κ)
    (hY : ∀i,MemLp (Y i) 2 P) (hZ : ∀k,MemLp (Z k) 2 P)
    (hYb : ∀ᵐω ∂P,∀i,|Y i ω| ≤ 1) (hZb : ∀ᵐω ∂P,∀k,|Z k ω| ≤ 1)
    {bad : Set Ω} (hbad : MeasurableSet bad) {e : ℝ} (he : 0 ≤ e)
    (hgood : ∀ᵐω ∂P,ω ∉ bad → ∀i,|Y i ω-Z (π i) ω| ≤ e) :
    (∫ω,(centeredSup Y P ω)^2 ∂P) ≤
      2*(∑k : κ,∫ω,(Z k ω-∫z,Z k z ∂P)^2 ∂P)+
      2*(2*e+2*P.real bad)^2+4*P.real bad := by
  let G := meshEnergy Z P
  let a := 2*e+2*P.real bad
  have hG0 (ω : Ω) : 0 ≤ G ω := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hZi (k : κ) : Integrable (fun ω => (Z k ω-∫z,Z k z ∂P)^2) P :=
    ((hZ k).sub (memLp_const (∫z,Z k z ∂P))).integrable_sq
  have hGi : Integrable G P := integrable_finsetSum Finset.univ (fun k _ => hZi k)
  have hmean (i : ι) : |(∫ω,Y i ω ∂P)-(∫ω,Z (π i) ω ∂P)| ≤ e+2*P.real bad := by
    apply mean_difference_le_bad_event ((hY i).integrable (by norm_num))
      ((hZ (π i)).integrable (by norm_num)) hbad he (by norm_num)
    · filter_upwards [hYb,hZb] with ω hYω hZω
      exact (abs_sub _ _).trans (by linarith [hYω i,hZω (π i)])
    · exact hgood.mono (fun ω hω hg => hω hg i)
  have hgrid (ω : Ω) (k : κ) : |Z k ω-∫z,Z k z ∂P| ≤ Real.sqrt (G ω) := by
    apply (Real.le_sqrt (abs_nonneg _) (hG0 ω)).mpr
    rw [sq_abs]
    change (Z k ω-∫z,Z k z ∂P)^2 ≤ ∑j : κ,(Z j ω-∫z,Z j z ∂P)^2
    exact Finset.single_le_sum (f:=fun j : κ => (Z j ω-∫z,Z j z ∂P)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have hdom : ∀ᵐω ∂P,(centeredSup Y P ω)^2 ≤
      2*G ω+2*a^2+4*bad.indicator (fun _ => (1:ℝ)) ω := by
    filter_upwards [hgood,centeredSup_bounds Y hY hYb] with ω hω hsb
    by_cases h : ω ∈ bad
    · simp only [indicator_of_mem h,mul_one]
      have hh := pow_le_pow_left₀ hsb.1 hsb.2 2
      norm_num at hh
      nlinarith [hG0 ω,sq_nonneg a]
    have hs : centeredSup Y P ω ≤ Real.sqrt (G ω)+a := by
      apply ciSup_le
      intro i
      have heq : Y i ω-∫z,Y i z ∂P =
          (Y i ω-Z (π i) ω)+(Z (π i) ω-∫z,Z (π i) z ∂P)+
          ((∫z,Z (π i) z ∂P)-(∫z,Y i z ∂P)) := by ring
      rw [heq]
      have hab := (abs_add_le (Y i ω-Z (π i) ω) (Z (π i) ω-∫z,Z (π i) z ∂P))
      have hh := abs_add_le ((Y i ω-Z (π i) ω)+(Z (π i) ω-∫z,Z (π i) z ∂P))
        ((∫z,Z (π i) z ∂P)-(∫z,Y i z ∂P))
      have hm := hmean i
      rw [abs_sub_comm] at hm
      dsimp only [a]
      linarith [hω h i,hgrid ω (π i)]
    simp only [indicator_of_notMem h,mul_zero,add_zero]
    have hh := pow_le_pow_left₀ hsb.1 hs 2
    have hsqrt := Real.sq_sqrt (hG0 ω)
    nlinarith [sq_nonneg (Real.sqrt (G ω)-a)]
  have hDi : Integrable (fun ω => 2*G ω+2*a^2+4*bad.indicator (fun _ => (1:ℝ)) ω) P :=
    ((hGi.const_mul 2).add (integrable_const _)).add (((integrable_const (1:ℝ)).indicator hbad).const_mul 4)
  have hh := integral_mono_ae (centeredSup_memLp_two Y hY hYb).integrable_sq hDi hdom
  have hconst : Integrable (fun _ : Ω => 2*a^2) P := integrable_const _
  have hGa : Integrable (fun ω => 2*G ω+2*a^2) P := (hGi.const_mul 2).add hconst
  rw [integral_add hGa
      (((integrable_const (1:ℝ)).indicator hbad).const_mul 4),
    integral_add (hGi.const_mul 2) hconst,integral_const_mul,
    integral_const_mul,integral_const_mul,integral_indicator hbad] at hh
  simp only [integral_const,probReal_univ,smul_eq_mul,mul_one,one_mul,
    measureReal_def,Measure.restrict_apply MeasurableSet.univ,univ_inter,measure_univ,ENNReal.toReal_one] at hh
  have hGE : (∫ω,G ω ∂P)=∑k : κ,∫ω,(Z k ω-∫z,Z k z ∂P)^2 ∂P :=
    integral_finsetSum _ (fun k _ => hZi k)
  rw [hGE] at hh
  exact hh

end SphericalAging.CountableMeshConcentration
