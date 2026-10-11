module

public import SphericalAging.SphereSpatialGeneratorRegularity

public section

/-! Genuine C¹ spatial regularity and joint first derivative of the
spherical generator from the first three spatial jets of its argument. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereSpatialGeneratorC1Regularity
open FiniteModel SphericalIntegrationByParts SphereGeneratorIntegrationByParts SphereGamma2Algebra
open SphereSpatialGeneratorRegularity
open SphereGeneratorRegularity
open SphereEntropyDissipation
open scoped BigOperators ContDiff
local instance {N : ℕ} : NormedAddCommGroup (Vector N→L[ℝ] ℝ) := inferInstance
local instance {N : ℕ} : NormedSpace ℝ (Vector N→L[ℝ] ℝ) := inferInstance
local instance {N : ℕ} : NormedAddCommGroup (Vector N→L[ℝ] Vector N→L[ℝ] ℝ) := inferInstance
local instance {N : ℕ} : NormedSpace ℝ (Vector N→L[ℝ] Vector N→L[ℝ] ℝ) := inferInstance

theorem lie_contDiff_order {N n : ℕ} (A : Operator N) {m : Vector N→ℝ}
    (hm : ContDiff ℝ (n+1) m) : ContDiff ℝ n (lieDerivative A m) :=
  (hm.fderiv_right (m:=n) (by simp)).clm_apply A.contDiff

theorem rotationGenerator_contDiff_one {N p : ℕ} {ι : Type*} [Fintype ι]
    (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N) {m : Vector N→ℝ}
    (hm : ContDiff ℝ 3 m) : ContDiff ℝ 1 (rotationGenerator κ β J A m) := by
  classical
  unfold rotationGenerator
  apply contDiff_const.mul
  apply ContDiff.sum
  intro i hi
  exact (lie_contDiff_order (A i) (lie_contDiff_order (A i) hm)).add
    ((contDiff_const.mul (lieDerivative_contDiff (A i) ((Hamiltonian_contDiff J).of_le (by norm_num)))).mul
      (lieDerivative_contDiff (A i) (hm.of_le (by norm_num))))

theorem lieDerivative_fderiv_apply {N : ℕ} (A : Operator N) {m : Vector N→ℝ}
    (hm : ContDiff ℝ 2 m) (x u : Vector N) :
    fderiv ℝ (lieDerivative A m) x u=
      fderiv ℝ (fderiv ℝ m) x u (A x)+fderiv ℝ m x (A u) := by
  have hd := (((hm.fderiv_right (m:=1) (by norm_num)).differentiable
    (by norm_num)) x).hasFDerivAt.clm_apply (A.hasFDerivAt)
  change HasFDerivAt (lieDerivative A m) _ x at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,add_comm]

theorem lieDerivative_twice_first_apply {N : ℕ} (A : Operator N) {m : Vector N→ℝ}
    (hm : ContDiff ℝ 3 m) (x u : Vector N) :
    fderiv ℝ (lieDerivative A (lieDerivative A m)) x u=
      fderiv ℝ (fderiv ℝ (fderiv ℝ m)) x u (A x) (A x)+
      fderiv ℝ (fderiv ℝ m) x (A u) (A x)+
      fderiv ℝ (fderiv ℝ m) x (A x) (A u)+
      (fderiv ℝ (fderiv ℝ m) x u (A (A x))+fderiv ℝ m x (A (A u))) := by
  have hdD := (((hm.fderiv_right (m:=2) (by norm_num)).differentiable
    (by norm_num)) x).hasFDerivAt
  have hdDD := ((((hm.fderiv_right (m:=2) (by norm_num)).fderiv_right (m:=1)
    (by norm_num)).differentiable (by norm_num)) x).hasFDerivAt
  have hh := ((hdDD.clm_apply A.hasFDerivAt).clm_apply A.hasFDerivAt).add
    (hdD.clm_apply (A.hasFDerivAt.comp x A.hasFDerivAt))
  have he : (fun y => fderiv ℝ (fderiv ℝ m) y (A y) (A y)+fderiv ℝ m y (A (A y)))=
      lieDerivative A (lieDerivative A m) :=
    funext (fun y => (lieDerivative_twice_fderiv A A (hm.of_le (by norm_num)) y).symm)
  change HasFDerivAt (fun y => fderiv ℝ (fderiv ℝ m) y (A y) (A y)+fderiv ℝ m y (A (A y))) _ x at hh
  rw [he] at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,Function.comp_apply]
  ring

theorem joint_first_lieDerivative_continuous {N : ℕ} {m : ℝ→Vector N→ℝ} (A : Operator N)
    (hs : ∀t,ContDiff ℝ 2 (m t))
    (hfirst : Continuous (fun z : ℝ×Vector N => fderiv ℝ (m z.1) z.2))
    (hsecond : Continuous (fun z : ℝ×Vector N => fderiv ℝ (fderiv ℝ (m z.1)) z.2)) :
    Continuous (fun z : ℝ×Vector N => fderiv ℝ (lieDerivative A (m z.1)) z.2) := by
  apply continuous_clm_apply.mpr
  intro u
  exact (((hsecond.clm_apply (continuous_const (y:=u))).clm_apply
    (A.continuous.comp continuous_snd)).add
      (hfirst.clm_apply (continuous_const (y:=A u)))).congr
        (fun z => (lieDerivative_fderiv_apply A (hs z.1) z.2 u).symm)

theorem joint_first_twice_lieDerivative_continuous {N : ℕ} {m : ℝ→Vector N→ℝ} (A : Operator N)
    (hs : ∀t,ContDiff ℝ 3 (m t))
    (hfirst : Continuous (fun z : ℝ×Vector N => fderiv ℝ (m z.1) z.2))
    (hsecond : Continuous (fun z : ℝ×Vector N => fderiv ℝ (fderiv ℝ (m z.1)) z.2))
    (hthird : Continuous (fun z : ℝ×Vector N => fderiv ℝ (fderiv ℝ (fderiv ℝ (m z.1))) z.2)) :
    Continuous (fun z : ℝ×Vector N => fderiv ℝ (lieDerivative A (lieDerivative A (m z.1))) z.2) := by
  apply continuous_clm_apply.mpr
  intro u
  have hA := A.continuous.comp (continuous_snd : Continuous (fun z : ℝ×Vector N => z.2))
  have h1 := (((hthird.clm_apply (continuous_const (y:=u))).clm_apply hA).clm_apply hA)
  have h2 := (hsecond.clm_apply (continuous_const (y:=A u))).clm_apply hA
  have h3 := (hsecond.clm_apply hA).clm_apply (continuous_const (y:=A u))
  have h4 := (hsecond.clm_apply (continuous_const (y:=u))).clm_apply (A.continuous.comp hA)
  have h5 := hfirst.clm_apply (continuous_const (y:=A (A u)))
  exact (((h1.add h2).add h3).add (h4.add h5)).congr
    (fun z => (lieDerivative_twice_first_apply A (hs z.1) z.2 u).symm)

theorem joint_first_rotationGenerator_continuous {N p : ℕ} {ι : Type*} [Fintype ι]
    (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N) {m : ℝ→Vector N→ℝ}
    (hs : ∀t,ContDiff ℝ 3 (m t))
    (hfirst : Continuous (fun z : ℝ×Vector N => fderiv ℝ (m z.1) z.2))
    (hsecond : Continuous (fun z : ℝ×Vector N => fderiv ℝ (fderiv ℝ (m z.1)) z.2))
    (hthird : Continuous (fun z : ℝ×Vector N => fderiv ℝ (fderiv ℝ (fderiv ℝ (m z.1))) z.2)) :
    Continuous (fun z : ℝ×Vector N => fderiv ℝ (rotationGenerator κ β J A (m z.1)) z.2) := by
  classical
  have hval i : Continuous (fun z : ℝ×Vector N => lieDerivative (A i) (m z.1) z.2) :=
    joint_lieDerivative_continuous (A i) hfirst
  have hd i := joint_first_lieDerivative_continuous (A i) (fun t => (hs t).of_le (by norm_num)) hfirst hsecond
  have htw i := joint_first_twice_lieDerivative_continuous (A i) hs hfirst hsecond hthird
  have hH i : ContDiff ℝ 1 (lieDerivative (A i) (Hamiltonian N p J)) :=
    lieDerivative_contDiff (A i) ((Hamiltonian_contDiff J).of_le (by norm_num))
  have hprod i : Continuous (fun z : ℝ×Vector N => fderiv ℝ (fun y =>
      β*lieDerivative (A i) (Hamiltonian N p J) y*lieDerivative (A i) (m z.1) y) z.2) := by
    apply continuous_clm_apply.mpr
    intro u
    have hh := ((((continuous_const (y:=β)).mul (hH i).continuous).comp continuous_snd).mul
      ((hd i).clm_apply (continuous_const (y:=u)))).add
      ((hval i).mul ((continuous_const (y:=β)).mul
        (((hH i).continuous_fderiv (by norm_num)).comp continuous_snd |>.clm_apply (continuous_const (y:=u)))))
    apply hh.congr
    intro z
    have hder := ((((hH i).differentiable (by norm_num)) z.2).hasFDerivAt.const_mul β |>.mul
        ((((lieDerivative_contDiff (A i) ((hs z.1).of_le (by norm_num))).differentiable
          (by norm_num)) z.2).hasFDerivAt))
    change HasFDerivAt (fun y => β*lieDerivative (A i) (Hamiltonian N p J) y*
      lieDerivative (A i) (m z.1) y) _ z.2 at hder
    rw [hder.fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
      Pi.mul_apply,Pi.add_apply,Function.comp_apply]
  have hh : Continuous (fun z : ℝ×Vector N => κ • ∑i, (
      fderiv ℝ (lieDerivative (A i) (lieDerivative (A i) (m z.1))) z.2+
      fderiv ℝ (fun y => β*lieDerivative (A i) (Hamiltonian N p J) y*lieDerivative (A i) (m z.1) y) z.2)) := by
    apply continuous_clm_apply.mpr
    intro u
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,smul_eq_mul]
    exact (continuous_const (y:=κ)).mul (continuous_finsetSum Finset.univ
      (fun i _ => ((htw i).clm_apply (continuous_const (y:=u))).add
        ((hprod i).clm_apply (continuous_const (y:=u)))))
  apply hh.congr
  intro z
  unfold rotationGenerator
  rw [fderiv_const_mul, fderiv_fun_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact (fderiv_fun_add
      ((lie_contDiff_order (A i) (lie_contDiff_order (A i) (hs z.1))).differentiable (by norm_num) z.2)
      (((((hH i).differentiable (by norm_num)) z.2).const_mul β).mul
        ((lieDerivative_contDiff (A i) ((hs z.1).of_le (by norm_num))).differentiable (by norm_num) z.2))).symm
  · intro i hi
    exact ((lie_contDiff_order (A i) (lie_contDiff_order (A i) (hs z.1))).differentiable (by norm_num) z.2).add
      (((((hH i).differentiable (by norm_num)) z.2).const_mul β).mul
        ((lieDerivative_contDiff (A i) ((hs z.1).of_le (by norm_num))).differentiable (by norm_num) z.2))
  · apply DifferentiableAt.fun_sum
    intro i hi
    exact ((lie_contDiff_order (A i) (lie_contDiff_order (A i) (hs z.1))).differentiable (by norm_num) z.2).add
      (((((hH i).differentiable (by norm_num)) z.2).const_mul β).mul
        ((lieDerivative_contDiff (A i) ((hs z.1).of_le (by norm_num))).differentiable (by norm_num) z.2))

end SphericalAging.SphereSpatialGeneratorC1Regularity
