module

public import SphericalAging.L2ObservableFamilyC2
public import SphericalAging.FlowTerminalThirdJetContinuity

public section

/-! Literal third spatial derivative of a scalar expectation in terms
of the first three state jets and first two L² gradient jets. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace ContDiff
namespace SphericalAging.L2ObservableThirdJet
open HardSphereDynamics C2ObservableDerivative L2ObservableFamilyC2
open FlowTerminalThirdJetContinuity
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
local instance : NormedAddCommGroup (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] Lp (State N) 2 P) := inferInstance

theorem third_jet_of_hessian {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (F : V→ℝ) (X G : V→H)
    (hF : ContDiff ℝ 3 F) (hX : ContDiff ℝ 3 X) (hG : ContDiff ℝ 2 G)
    (hess : ∀x u v,fderiv ℝ (fderiv ℝ F) x u v=
      ⟪fderiv ℝ G x u,fderiv ℝ X x v⟫_ℝ+
      ⟪G x,fderiv ℝ (fderiv ℝ X) x u v⟫_ℝ) (x w u v : V) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ F)) x w u v=
      ⟪fderiv ℝ (fderiv ℝ G) x w u,fderiv ℝ X x v⟫_ℝ+
      ⟪fderiv ℝ G x u,fderiv ℝ (fderiv ℝ X) x w v⟫_ℝ+
      (⟪fderiv ℝ G x w,fderiv ℝ (fderiv ℝ X) x u v⟫_ℝ+
      ⟪G x,fderiv ℝ (fderiv ℝ (fderiv ℝ X)) x w u v⟫_ℝ) := by
  have hDG : DifferentiableAt ℝ (fderiv ℝ G) x :=
    ((hG.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)) x
  have hDX : DifferentiableAt ℝ (fderiv ℝ X) x :=
    ((hX.fderiv_right (m:=2) (by norm_num)).differentiable (by norm_num)) x
  have hDDX : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ X)) x :=
    (((hX.fderiv_right (m:=2) (by norm_num)).fderiv_right (m:=1)
      (by norm_num)).differentiable (by norm_num)) x
  have hDDF : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ F)) x :=
    (((hF.fderiv_right (m:=2) (by norm_num)).fderiv_right (m:=1)
      (by norm_num)).differentiable (by norm_num)) x
  have hGe : DifferentiableAt ℝ (fun y => fderiv ℝ G y u) x :=
    hDG.clm_apply (differentiableAt_const u)
  have hXe : DifferentiableAt ℝ (fun y => fderiv ℝ X y v) x :=
    hDX.clm_apply (differentiableAt_const v)
  have hXXe : DifferentiableAt ℝ (fun y => fderiv ℝ (fderiv ℝ X) y u v) x :=
    (hDDX.clm_apply (differentiableAt_const u)).clm_apply (differentiableAt_const v)
  have hfe : fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ F) y u v) x w=
      fderiv ℝ (fderiv ℝ (fderiv ℝ F)) x w u v := by
    rw [fderiv_apply_const (hDDF.clm_apply (differentiableAt_const u)) w v,
      fderiv_apply_const hDDF w u]
  rw [←hfe]
  have he : (fun y => fderiv ℝ (fderiv ℝ F) y u v)=
      (fun y => ⟪fderiv ℝ G y u,fderiv ℝ X y v⟫_ℝ+
        ⟪G y,fderiv ℝ (fderiv ℝ X) y u v⟫_ℝ) := funext fun y => hess y u v
  have hadd := congrArg (fun A : V→L[ℝ] ℝ => A w)
    (fderiv_add (hGe.inner ℝ hXe) (((hG.differentiable (by norm_num)) x).inner ℝ hXXe))
  simp only [Pi.add_def,ContinuousLinearMap.add_apply] at hadd
  rw [he,hadd]
  rw [fderiv_inner_apply ℝ hGe hXe w,
    fderiv_inner_apply ℝ ((hG.differentiable (by norm_num)) x) hXXe w,
    fderiv_apply_const hDG w u,fderiv_apply_const hDX w v,
    fderiv_apply_const (hDDX.clm_apply (differentiableAt_const u)) w v,
    fderiv_apply_const hDDX w u]
  ring

section Family
variable (f : State N→ℝ) (hf : ContDiff ℝ 2 f) (C K L : ℝ≥0)
  (hC : ∀x,‖f x‖≤C) (hK : ∀x,‖fderiv ℝ f x‖≤K)
  (hL : LipschitzWith L (fderiv ℝ f)) (X : State N→Lp (State N) 2 P)
  (hX : ContDiff ℝ 3 X)
  (hG : ContDiff ℝ 2 (fun x => gradientClass f hf K hK (X x)))
  (hF : ContDiff ℝ 3 (fun x => observable f (X x)))
include hC hK hL hX hG hF

theorem hessian_of_gradient (x u v : State N) :
    fderiv ℝ (fderiv ℝ (fun y => observable f (X y))) x u v=
      ⟪fderiv ℝ (fun y => gradientClass f hf K hK (X y)) x u,fderiv ℝ X x v⟫_ℝ+
      ⟪gradientClass f hf K hK (X x),fderiv ℝ (fderiv ℝ X) x u v⟫_ℝ := by
  let G := fun y => gradientClass f hf K hK (X y)
  have hdG := ((hG.differentiable (by norm_num)) x).hasFDerivAt
  have hdX := (ContinuousLinearMap.apply ℝ (Lp (State N) 2 P) v).hasFDerivAt.comp x
    (((hX.fderiv_right (m:=2) (by norm_num)).differentiable (by norm_num)) x).hasFDerivAt
  have hh := hdG.inner ℝ hdX
  simp only [Function.comp_def,ContinuousLinearMap.apply_apply] at hh
  have he : (fun y => ⟪G y,fderiv ℝ X y v⟫_ℝ)=
      fun y => fderiv ℝ (fun z => observable f (X z)) y v :=
    funext (fun y => (observable_family_fderiv f hf C K L hC hK hL X
      (hX.differentiable (by norm_num)) y v).symm)
  change HasFDerivAt (fun y => ⟪G y,fderiv ℝ X y v⟫_ℝ) _ x at hh
  rw [he] at hh
  have hd := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x
    (((hF.fderiv_right (m:=2) (by norm_num)).differentiable (by norm_num)) x).hasFDerivAt
  have heq := congrArg (fun A : State N→L[ℝ] ℝ => A u) (hd.unique hh)
  simp only [G,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply,ContinuousLinearMap.apply_apply] at heq
  simpa only [add_comm] using heq

theorem third_jet_apply (x w u v : State N) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => observable f (X y)))) x w u v=
      ⟪fderiv ℝ (fderiv ℝ (fun y => gradientClass f hf K hK (X y))) x w u,fderiv ℝ X x v⟫_ℝ+
      ⟪fderiv ℝ (fun y => gradientClass f hf K hK (X y)) x u,fderiv ℝ (fderiv ℝ X) x w v⟫_ℝ+
      (⟪fderiv ℝ (fun y => gradientClass f hf K hK (X y)) x w,fderiv ℝ (fderiv ℝ X) x u v⟫_ℝ+
      ⟪gradientClass f hf K hK (X x),fderiv ℝ (fderiv ℝ (fderiv ℝ X)) x w u v⟫_ℝ) := by
  exact third_jet_of_hessian (fun y => observable f (X y)) X
    (fun y => gradientClass f hf K hK (X y)) hF hX hG
    (hessian_of_gradient f hf C K L hC hK hL X hX hG hF) x w u v
end Family
end SphericalAging.L2ObservableThirdJet
