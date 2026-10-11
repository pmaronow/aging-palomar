module

public import SphericalAging.FisherCost
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public section

/-! Genuine extraction of a physical cost lower limit from the sequential
obstruction, including infinite lower limits. -/
noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace SphericalAging.FisherCostLowerLimit
open FisherCost

theorem cost_liminf_of_sequential_obstruction {b q c ell : ℝ} {cost : ℝ → ℝ}
    (hb : 0≤b) (hell : 0<ell) (hmargin : 0≤margin b q c)
    (hcost : ∀ᶠs in atTop,0≤cost s)
    (hseq : ∀s : ℕ → ℝ,Tendsto s atTop atTop → ∀ε : ℝ,ε∈Icc 0 1 →
      Tendsto (fun n => Real.sqrt (cost (s n))) atTop (𝓝 ε) →
      margin b q c≤(ell+9*b)*ε+6*b*ε^2) :
    ENNReal.ofReal (fisherCost b q c ell)≤liminf (fun s => ENNReal.ofReal (cost s)) atTop := by
  let A := liminf (fun s => ENNReal.ofReal (cost s)) atTop
  have hcap : fisherCost b q c ell≤1 := min_le_left _ _
  by_cases hA : ENNReal.ofReal (1:ℝ)≤A
  · exact (ENNReal.ofReal_le_ofReal hcap).trans hA
  · have hAl : A<ENNReal.ofReal (1:ℝ) := lt_of_not_ge hA
    have hfin : A≠⊤ := ne_top_of_lt hAl
    obtain ⟨s,hsA,hs⟩ := exists_seq_tendsto_liminf
      (u := fun s : ℝ => ENNReal.ofReal (cost s)) (f := atTop)
    have hlim : Tendsto (fun n => cost (s n)) atTop (𝓝 A.toReal) := by
      have hr := (ENNReal.tendsto_toReal hfin).comp hsA
      apply hr.congr'
      filter_upwards [hs.eventually hcost] with n hn
      exact ENNReal.toReal_ofReal hn
    have hreal : A.toReal<1 := by
      have he : ENNReal.ofReal A.toReal=A := ENNReal.ofReal_toReal hfin
      rw [← he] at hAl
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : 0<(1:ℝ))).mp hAl
    have hsqrt : Real.sqrt A.toReal∈Icc 0 1 := by
      refine ⟨Real.sqrt_nonneg _,?_⟩
      exact (Real.sqrt_le_sqrt hreal.le).trans_eq (by norm_num)
    have hbound := cost_of_sequential_obstruction b q c ell (Real.sqrt A.toReal)
      hb hell hsqrt.1 hsqrt.2 hmargin (hseq s hs _ hsqrt hlim.sqrt)
    rw [Real.sq_sqrt ENNReal.toReal_nonneg] at hbound
    exact (ENNReal.ofReal_le_ofReal hbound).trans_eq (ENNReal.ofReal_toReal hfin)

end SphericalAging.FisherCostLowerLimit
