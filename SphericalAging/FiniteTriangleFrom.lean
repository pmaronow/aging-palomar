module

public import SphericalAging.ProjectedTreeDrift

public section

/-! Genuine triangular Fubini with arbitrary real starting time. -/
noncomputable section
open Set MeasureTheory
namespace SphericalAging.FiniteTriangleFrom

theorem shift (f : ℝ → ℝ) (s a b : ℝ) :
    (∫ u in a..b,f u)=∫ u in (a-s)..(b-s),f (s+u) := by
  rw [intervalIntegral.integral_comp_add_left]
  simp only [add_sub_cancel]

theorem triangle_integral_swap {F : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) {s t : ℝ} (hst : s≤t) :
    (∫ u in s..t,∫ v in s..u,F u v)=∫ v in s..t,∫ u in v..t,F u v := by
  have hc : Continuous (Function.uncurry (fun u v => F (s+u) (s+v))) :=
    hF.comp ((continuous_const.add continuous_fst).prodMk (continuous_const.add continuous_snd))
  have hh := TriangleUniqueness.standard_triangle_integral_swap hc (sub_nonneg.mpr hst)
  have hl : (∫ u in s..t,∫ v in s..u,F u v)=
      ∫ u in (0:ℝ)..(t-s),∫ v in (0:ℝ)..u,F (s+u) (s+v) := by
    rw [shift (fun u => ∫ v in s..u,F u v) s s t,sub_self]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [shift (F (s+u)) s s (s+u),sub_self,add_sub_cancel_left]
  have hr : (∫ v in s..t,∫ u in v..t,F u v)=
      ∫ v in (0:ℝ)..(t-s),∫ u in v..(t-s),F (s+u) (s+v) := by
    rw [shift (fun v => ∫ u in v..t,F u v) s s t,sub_self]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [shift (fun u => F u (s+v)) s (s+v) t,add_sub_cancel_left]
  exact hl.trans (hh.trans hr.symm)

end SphericalAging.FiniteTriangleFrom
