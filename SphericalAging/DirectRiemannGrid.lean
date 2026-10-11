module

public import SphericalAging.KeyRenewal
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Algebra.Order.Floor.Semiring

public section

/-! Actual Darboux grid densities and their integrals on the positive ray. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalAging.DirectRiemannGrid
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Closed cells used in the manuscript's upper and lower sums. -/
@[expose] def closedCell (h : ℝ) (n : ℕ) : Set ℝ := Icc ((n:ℝ)*h) (((n:ℝ)+1)*h)
/-- Disjoint half-open cells representing the same Darboux sums as integrals. -/
@[expose] def gridCell (h : ℝ) (n : ℕ) : Set ℝ := Ico ((n:ℝ)*h) (((n:ℝ)+1)*h)
@[expose] def upperCell (z : ℝ → ℝ≥0∞) (h : ℝ) (n : ℕ) : ℝ≥0∞ := ⨆ t ∈ closedCell h n,z t
@[expose] def lowerCell (z : ℝ → ℝ≥0∞) (h : ℝ) (n : ℕ) : ℝ≥0∞ := ⨅ t : closedCell h n,z t

@[expose] def gridDensity (b : ℕ → ℝ≥0∞) (h : ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ,(gridCell h n).indicator (fun _ => b n) x

@[expose] def upperDensity (z : ℝ → ℝ≥0∞) (h : ℝ) := gridDensity (upperCell z h) h
@[expose] def lowerDensity (z : ℝ → ℝ≥0∞) (h : ℝ) := gridDensity (lowerCell z h) h

@[expose] def upperSum (z : ℝ → ℝ≥0∞) (h : ℝ) := ENNReal.ofReal h * ∑' n,upperCell z h n
@[expose] def lowerSum (z : ℝ → ℝ≥0∞) (h : ℝ) := ENNReal.ofReal h * ∑' n,lowerCell z h n

theorem closedCell_nonempty {h : ℝ} (hh : 0<h) (n : ℕ) : (closedCell h n).Nonempty := by
  refine ⟨(n:ℝ)*h,le_rfl,?_⟩
  nlinarith

theorem le_upperCell {z : ℝ → ℝ≥0∞} {h : ℝ} {n : ℕ} {t : ℝ}
    (ht : t∈closedCell h n) : z t≤upperCell z h n := by
  exact le_iSup₂ (f:=fun t (_:t∈closedCell h n) => z t) t ht

theorem lowerCell_le {z : ℝ → ℝ≥0∞} {h : ℝ} {n : ℕ} {t : ℝ}
    (ht : t∈closedCell h n) : lowerCell z h n≤z t := by
  exact iInf_le (fun t : closedCell h n => z t) ⟨t,ht⟩

theorem lowerCell_le_upperCell {z : ℝ → ℝ≥0∞} {h : ℝ} (hh : 0<h) (n : ℕ) :
    lowerCell z h n≤upperCell z h n := by
  obtain ⟨t,ht⟩ := closedCell_nonempty hh n
  exact (lowerCell_le ht).trans (le_upperCell ht)

theorem gridCell_disjoint {h : ℝ} (hh : 0<h) : Pairwise (fun n m : ℕ => Disjoint (gridCell h n) (gridCell h m)) := by
  intro n m hnm
  have key : ∀n m : ℕ,n<m → Disjoint (gridCell h n) (gridCell h m) := by
    intro n m hnm
    apply disjoint_left.mpr
    intro x hx hy
    change (n:ℝ)*h≤x ∧ x<((n:ℝ)+1)*h at hx
    change (m:ℝ)*h≤x ∧ x<((m:ℝ)+1)*h at hy
    have hn : (n:ℝ)+1≤(m:ℝ) := by exact_mod_cast hnm
    have hnh := mul_le_mul_of_nonneg_right hn hh.le
    linarith
  rcases lt_or_gt_of_ne hnm with hn|hn
  · exact key n m hn
  · exact (key m n hn).symm

theorem gridCell_floor {h x : ℝ} (hh : 0<h) (hx : 0≤x) :
    x∈gridCell h ⌊x/h⌋₊ := by
  change (⌊x/h⌋₊:ℝ)*h≤x ∧ x<((⌊x/h⌋₊:ℝ)+1)*h
  refine ⟨?_,?_⟩
  · exact (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg hx hh.le))
  · exact (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (x/h))

theorem gridCell_nonnegative {h x : ℝ} {n : ℕ} (hh : 0<h) (hx : x∈gridCell h n) : 0≤x := by
  exact (mul_nonneg n.cast_nonneg hh.le).trans hx.1

theorem gridDensity_at {h x : ℝ} (hh : 0<h) (hx : 0≤x) (b : ℕ → ℝ≥0∞) :
    gridDensity b h x=b ⌊x/h⌋₊ := by
  have hcell := gridCell_floor hh hx
  rw [gridDensity,tsum_eq_single ⌊x/h⌋₊]
  · exact indicator_of_mem hcell _
  · intro n hn
    have hnot : x∉gridCell h n := by
      intro hx'
      exact (disjoint_left.mp (gridCell_disjoint hh hn)) hx' hcell
    exact indicator_of_notMem hnot _

theorem gridDensity_negative {h x : ℝ} (hh : 0<h) (hx : x<0) (b : ℕ → ℝ≥0∞) :
    gridDensity b h x=0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  exact indicator_of_notMem (fun hn => hx.not_ge (gridCell_nonnegative hh hn)) _

theorem gridDensity_measurable (b : ℕ → ℝ≥0∞) (h : ℝ) : Measurable (gridDensity b h) := by
  apply Measurable.ennreal_tsum
  intro n
  exact measurable_const.indicator measurableSet_Ico

theorem lintegral_gridDensity (b : ℕ → ℝ≥0∞) {h : ℝ} (hh : 0<h) :
    ∫⁻ x,gridDensity b h x=ENNReal.ofReal h * ∑' n,b n := by
  change (∫⁻ x,∑' n : ℕ,(gridCell h n).indicator (fun _ => b n) x)=_
  simp only [gridCell]
  rw [lintegral_tsum (fun n => (measurable_const.indicator measurableSet_Ico).aemeasurable)]
  simp only [lintegral_indicator measurableSet_Ico,setLIntegral_const,Real.volume_Ico]
  have heq : ∀n : ℕ,((n:ℝ)+1)*h-(n:ℝ)*h=h := by intro n;ring
  simp only [heq]
  rw [ENNReal.tsum_mul_right,mul_comm]

@[expose] def broadMajorant (z : ℝ → ℝ≥0∞) (H x : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ,(Icc ((k:ℝ)-H) ((k:ℝ)+1+H)).indicator (fun _ => upperCell z 1 k) x

theorem lintegral_broadMajorant (z : ℝ → ℝ≥0∞) {H : ℝ} (hH : 0≤H) :
    ∫⁻ x,broadMajorant z H x=ENNReal.ofReal (1+2*H)*∑' k,upperCell z 1 k := by
  change (∫⁻ x,∑' k : ℕ,(Icc ((k:ℝ)-H) ((k:ℝ)+1+H)).indicator (fun _ => upperCell z 1 k) x)=_
  rw [lintegral_tsum (fun k => (measurable_const.indicator measurableSet_Icc).aemeasurable)]
  simp only [lintegral_indicator measurableSet_Icc,setLIntegral_const,Real.volume_Icc]
  have heq : ∀k : ℕ,(k:ℝ)+1+H-((k:ℝ)-H)=1+2*H := by intro k;ring
  simp only [heq]
  rw [ENNReal.tsum_mul_right,mul_comm]

theorem upperCell_le_broadMajorant {z : ℝ → ℝ≥0∞} {h H x : ℝ} (hh : 0<h)
    (hH : h≤H) (hx : 0≤x) : upperCell z h ⌊x/h⌋₊≤broadMajorant z H x := by
  apply iSup₂_le
  intro t ht
  have hg := gridCell_floor hh hx
  change (⌊x/h⌋₊:ℝ)*h≤x ∧ x<((⌊x/h⌋₊:ℝ)+1)*h at hg
  change (⌊x/h⌋₊:ℝ)*h≤t ∧ t≤((⌊x/h⌋₊:ℝ)+1)*h at ht
  have ht0 : 0≤t := (mul_nonneg (Nat.cast_nonneg _) hh.le).trans ht.1
  let k : ℕ := ⌊t⌋₊
  have hk0 : (k:ℝ)≤t := Nat.floor_le ht0
  have hk1 : t<(k:ℝ)+1 := Nat.lt_floor_add_one t
  have htx : |t-x|≤H := by
    rw [abs_le]
    constructor <;> nlinarith
  have hmem : x∈Icc ((k:ℝ)-H) ((k:ℝ)+1+H) := by
    constructor <;> linarith [(abs_le.mp htx).1,(abs_le.mp htx).2]
  have htu : t∈closedCell 1 k := by simpa [closedCell] using And.intro hk0 hk1.le
  calc
    z t≤upperCell z 1 k := le_upperCell htu
    _=(Icc ((k:ℝ)-H) ((k:ℝ)+1+H)).indicator (fun _ => upperCell z 1 k) x := by
      rw [indicator_of_mem hmem]
    _≤broadMajorant z H x := by
      exact ENNReal.le_tsum (f:=fun k : ℕ => (Icc ((k:ℝ)-H) ((k:ℝ)+1+H)).indicator (fun _ => upperCell z 1 k) x) k

theorem upperDensity_le_broadMajorant {z : ℝ → ℝ≥0∞} {h H : ℝ} (hh : 0<h)
    (hH : h≤H) (x : ℝ) : upperDensity z h x≤broadMajorant z H x := by
  by_cases hx : 0≤x
  · rw [upperDensity,gridDensity_at hh hx]
    exact upperCell_le_broadMajorant hh hH hx
  · rw [upperDensity,gridDensity_negative hh (lt_of_not_ge hx)]
    exact bot_le

theorem upperSum_finite {z : ℝ → ℝ≥0∞} (hunit : (∑' k,upperCell z 1 k)≠∞)
    {h : ℝ} (hh : 0<h) : upperSum z h≠∞ := by
  rw [upperSum,←lintegral_gridDensity _ hh]
  apply ne_top_of_le_ne_top _ (lintegral_mono (upperDensity_le_broadMajorant hh le_rfl))
  rw [lintegral_broadMajorant z hh.le]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hunit

theorem lowerSum_finite {z : ℝ → ℝ≥0∞} (hunit : (∑' k,upperCell z 1 k)≠∞)
    {h : ℝ} (hh : 0<h) : lowerSum z h≠∞ := by
  apply ne_top_of_le_ne_top (upperSum_finite hunit hh)
  exact mul_le_mul le_rfl (ENNReal.tsum_le_tsum (lowerCell_le_upperCell hh)) bot_le bot_le

end
end SphericalAging.DirectRiemannGrid
