module

public import SphericalAging.SphereFisherDissipation
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

public section

/-! Genuine time/spatial derivative interchange for smooth density functions.
The mixed derivative equality is proved by Schwarz symmetry of the actual
second Fréchet derivative, rather than supplied as a hypothesis. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace SphericalAging.SphereMixedDerivatives

open FiniteModel SphericalIntegrationByParts

/-- The actual partial derivative in the time coordinate. -/
@[expose] def timeSlope {N : ℕ} (f : ℝ → Vector N → ℝ) (t : ℝ) (x : Vector N) : ℝ :=
  fderiv ℝ (Function.uncurry f) (t,x) (1,0)

theorem lieDerivative_eq_total_derivative {N : ℕ} (A : Operator N)
    {f : ℝ → Vector N → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    (t : ℝ) (x : Vector N) :
    lieDerivative A (f t) x=fderiv ℝ (Function.uncurry f) (t,x) (0,A x) := by
  have hd := (hf.differentiable (by norm_num) (t,x)).hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  change fderiv ℝ (fun y => f t y) x (A x)=_
  rw [show fderiv ℝ (fun y => f t y) x=
      (fderiv ℝ (Function.uncurry f) (t,x)).comp
        ((0 : Vector N →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vector N))) from hd.fderiv]
  simp

theorem timeSlope_hasDerivAt {N : ℕ} {f : ℝ → Vector N → ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry f)) (t : ℝ) (x : Vector N) :
    HasDerivAt (fun s => f s x) (timeSlope f t x) t := by
  have hd := (hf.differentiable (by norm_num) (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  simpa only [Function.comp_def,Function.uncurry,timeSlope,id_eq] using hd

theorem timeSlope_contDiff_order {N : ℕ} {n : ℕ} {f : ℝ → Vector N → ℝ}
    (hf : ContDiff ℝ (n+1) (Function.uncurry f)) :
    ContDiff ℝ n (Function.uncurry (timeSlope f)) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem timeSlope_contDiff_one {N : ℕ} {f : ℝ → Vector N → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) :
    ContDiff ℝ 1 (Function.uncurry (timeSlope f)) := timeSlope_contDiff_order hf

theorem joint_lieDerivative_contDiff_order {N : ℕ} {n : ℕ} (A : Operator N)
    {f : ℝ → Vector N → ℝ} (hf : ContDiff ℝ (n+1) (Function.uncurry f)) :
    ContDiff ℝ n (fun z : ℝ × Vector N => lieDerivative A (f z.1) z.2) := by
  have hpartial : ContDiff ℝ (n+1)
      (Function.uncurry (fun z : ℝ × Vector N => fun x : Vector N => f z.1 x)) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact (hpartial.fderiv contDiff_snd (by simp)).clm_apply
    (A.contDiff.comp contDiff_snd)

/-- Actual smooth time differentiation of the spatial Lie derivative. -/
theorem lieDerivative_time_hasDerivAt {N : ℕ} (A : Operator N)
    {f : ℝ → Vector N → ℝ} (hf : ContDiff ℝ 2 (Function.uncurry f))
    (t : ℝ) (x : Vector N) :
    HasDerivAt (fun s => lieDerivative A (f s) x)
      (lieDerivative A (timeSlope f t) x) t := by
  have hf₁ : ContDiff ℝ 1 (Function.uncurry f) := hf.of_le (by norm_num)
  have hFD : ContDiff ℝ 1 (fderiv ℝ (Function.uncurry f)) :=
    hf.fderiv_right (by norm_num)
  have ht := (hFD.differentiable (by norm_num) (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have happ := ht.clm_apply (hasDerivAt_const t (0,A x))
  have hspace := lieDerivative_eq_total_derivative A (timeSlope_contDiff_one hf) t x
  have hslope : lieDerivative A (timeSlope f t) x=
      fderiv ℝ (fderiv ℝ (Function.uncurry f)) (t,x) (1,0) (0,A x) := by
    rw [hspace]
    have hd := (hFD.differentiable (by norm_num) (t,x)).hasFDerivAt.clm_apply
      (hasFDerivAt_const (1,0) (t,x))
    change fderiv ℝ (fun z : ℝ × Vector N =>
      fderiv ℝ (Function.uncurry f) z (1,0)) (t,x) (0,A x)=_
    rw [hd.fderiv]
    simp only [add_apply,ContinuousLinearMap.comp_apply,zero_apply,
      ContinuousLinearMap.flip_apply,map_zero,zero_add]
    exact ((hf.contDiffAt (x := (t,x))).isSymmSndFDerivAt (by simp)).eq (0,A x) (1,0)
  rw [hslope]
  convert happ using 1
  · funext s
    exact lieDerivative_eq_total_derivative A hf₁ s x
  · simp

end SphericalAging.SphereMixedDerivatives
