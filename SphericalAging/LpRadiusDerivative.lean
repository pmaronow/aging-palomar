module

public import SphericalAging.TerminalLinearity
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.Deriv.Mul

public section

/-! Pointwise radius differentiation in genuine L² state classes into L¹.
This detects almost-sure tangent vectors, rather than merely a zero
expected radial component. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.LpRadiusDerivative
open HardSphereDynamics
set_option maxHeartbeats 1600000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

@[expose]  def innerClass : Lp (State N) 2 P →L[ℝ] Lp (State N) 2 P →L[ℝ] Lp ℝ 1 P :=
  (innerSL ℝ (E := State N)).holderL P 2 2 1

 theorem innerClass_coe (U V : Lp (State N) 2 P) :
    innerClass U V =ᵐ[P] (fun omega => inner ℝ (U omega) (V omega)) :=
  (innerSL ℝ (E := State N)).coeFn_holder U V

 theorem innerClass_comm (U V : Lp (State N) 2 P) : innerClass U V=innerClass V U := by
  apply Lp.ext
  filter_upwards [innerClass_coe U V,innerClass_coe V U] with omega hUV hVU
  rw [hUV,hVU,real_inner_comm]

@[expose]  def radiusClass (U : Lp (State N) 2 P) : Lp ℝ 1 P := innerClass U U

 theorem radiusClass_coe (U : Lp (State N) 2 P) :
    radiusClass U =ᵐ[P] (fun omega => ‖U omega‖^2) := by
  simpa only [radiusClass,real_inner_self_eq_norm_sq] using innerClass_coe U U

 theorem radiusClass_eq_const (U : Lp (State N) 2 P) (r : ℝ)
    (hr : ∀ᵐ omega ∂P,‖U omega‖^2=r) : radiusClass U=Lp.const 1 P r := by
  apply Lp.ext
  filter_upwards [radiusClass_coe U,Lp.coeFn_const 1 P r,hr] with omega hU hc hr
  rw [hU,hc,hr]
  rfl

 theorem hasDerivAt_radiusClass {f : ℝ → Lp (State N) 2 P} {v : Lp (State N) 2 P} {x : ℝ}
    (hf : HasDerivAt f v x) : HasDerivAt (fun r => radiusClass (f r)) ((2 : ℝ) • innerClass (f x) v) x := by
  have h := (innerClass (N := N) (P := P)).hasDerivAt_of_bilinear (fun _ => hf) (fun _ => hf)
  simpa only [radiusClass,innerClass_comm,two_smul] using h

/-- Actual pointwise radius constancy forces the L² derivative to be
orthogonal to the state almost surely. -/
 theorem tangent_of_constant_radius {f : ℝ → Lp (State N) 2 P} {v : Lp (State N) 2 P} {x r : ℝ}
    (hf : HasDerivAt f v x) (hr : ∀ᶠ s in 𝓝 x,∀ᵐ omega ∂P,‖f s omega‖^2=r) :
    ∀ᵐ omega ∂P,inner ℝ (f x omega) (v omega)=0 := by
  have hevent : (fun s => radiusClass (f s)) =ᶠ[𝓝 x] (fun _ => Lp.const 1 P r) :=
    hr.mono (fun s hs => radiusClass_eq_const (f s) r hs)
  have hconst := (hasDerivAt_const x (Lp.const 1 P r)).congr_of_eventuallyEq hevent
  have hz : (2 : ℝ) • innerClass (f x) v=0 := (hasDerivAt_radiusClass hf).unique hconst
  have hinner : innerClass (f x) v=0 := (smul_eq_zero.mp hz).resolve_left (by norm_num)
  filter_upwards [innerClass_coe (f x) v,Lp.coeFn_zero ℝ 1 P] with omega hcoe hzero
  rw [hinner,hzero] at hcoe
  exact hcoe.symm
end SphericalAging.LpRadiusDerivative
