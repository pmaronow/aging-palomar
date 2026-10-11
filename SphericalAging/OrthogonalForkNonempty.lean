module

public import SphericalAging.GaussianFixedBaseForkConcentration
public import SphericalAging.PredictableHouseholder

public section

/-! Explicit coordinate forks, transported by an actual equal-norm
reflection, discharge the deterministic fork-domain nonemptiness. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.OrthogonalForkNonempty
open FiniteModel GaussianOrthogonalForkCovariance GaussianFixedBaseForkConcentration
open MeasureTheory
open scoped InnerProductSpace
variable {N K : ℕ}

private theorem fork_isometry (O : Vector N≃ₗᵢ[ℝ]Vector N)
    {x : Vector N} {y : Fin K→Vector N} {r q : ℝ} (h : OrthogonalFork x y r q) :
    OrthogonalFork (O x) (fun i => O (y i)) r q := by
  constructor
  · rw [O.norm_map];exact h.base_norm
  · intro i;rw [O.norm_map];exact h.leaf_norm i
  · intro i;rw [←map_sub,O.inner_map_map];exact h.increment_base i
  · intro i j hij;rw [←map_sub,←map_sub,O.inner_map_map];exact h.increment_orthogonal i j hij

theorem exists_coordinate_fork (hKN : K<N) (r q : ℝ) (hr : 0≤r) (hrq : r≤q) :
    ∃x : Vector N,∃y : Fin K→Vector N,OrthogonalFork x y r q := by
  classical
  have hN : 0<N := by omega
  let e := EuclideanSpace.basisFun (Fin N) ℝ
  let i0 : Fin N := ⟨0,hN⟩
  let lift : Fin K→Fin N := fun i => ⟨i.val+1,by omega⟩
  let x : Vector N := Real.sqrt ((N:ℝ)*r) • e i0
  let v : Fin K→Vector N := fun i => Real.sqrt ((N:ℝ)*(q-r)) • e (lift i)
  have hzero (i : Fin K) : i0≠lift i := by
    intro hh
    have hh' := congrArg Fin.val hh
    dsimp only [i0,lift] at hh'
    omega
  have hinj : Function.Injective lift := by
    intro i j hij
    apply Fin.ext
    have hh := congrArg Fin.val hij
    dsimp only [lift] at hh
    omega
  have hx : ‖x‖^2=(N:ℝ)*r := by
    simp only [x,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),e.norm_eq_one,mul_one]
    exact Real.sq_sqrt (by positivity)
  have hv (i : Fin K) : ‖v i‖^2=(N:ℝ)*(q-r) := by
    simp only [v,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),e.norm_eq_one,mul_one]
    exact Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hrq))
  have hix (i : Fin K) : ⟪v i,x⟫_ℝ=0 := by
    simp only [v,x,real_inner_smul_left,real_inner_smul_right,e.inner_eq_ite,
      if_neg (Ne.symm (hzero i)),mul_zero]
  have hij (i j : Fin K) (hij : i≠j) : ⟪v i,v j⟫_ℝ=0 := by
    simp only [v,real_inner_smul_left,real_inner_smul_right,e.inner_eq_ite,
      if_neg (fun hh => hij (hinj hh)),mul_zero]
  refine ⟨x,fun i => x+v i,⟨hx,?_,?_,?_⟩⟩
  · intro i
    rw [norm_add_sq_real,hx,hv,real_inner_comm,hix]
    ring
  · intro i
    rw [add_sub_cancel_left,hix]
  · intro i j h
    rw [add_sub_cancel_left,add_sub_cancel_left]
    exact hij i j h

theorem leafDomain_nonempty (hKN : K<N) (x : Vector N) (r q : ℝ)
    (hr : 0≤r) (hrq : r≤q) (hx : ‖x‖^2=(N:ℝ)*r) :
    Nonempty (LeafDomain N K x r q) := by
  obtain ⟨z,y,hfork⟩ := exists_coordinate_fork hKN r q hr hrq
  have he : ‖z‖=‖x‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (hfork.base_norm.trans hx.symm)
  let O := PredictableHouseholder.update z x
  have hO : O z=x := PredictableHouseholder.update_equal_norm he
  have hh := fork_isometry O hfork
  rw [hO] at hh
  exact ⟨⟨fun i => O (y i),hh⟩⟩

theorem actual_fixedBaseFork_absolute_tail {p : ℕ} (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (a b r q : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hrq : r≤q) (hq1 : q≤1) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*r)
    (ε : ℝ) (hε : 0≤ε) :
    (forkLaw N p K).real {J | ε≤|GaussianFixedBaseForkConcentration.supremum a b r q x J-
      ∫J',GaussianFixedBaseForkConcentration.supremum a b r q x J' ∂forkLaw N p K|}≤
      2*Real.exp (-((K:ℝ)*N)*ε^2/(2*(Real.pi/2)^2)) := by
  letI := leafDomain_nonempty hKN x r q hr hrq hx
  exact supremum_centered_absolute_tail (by omega) hp hK a b r q ha hab hb hr
    (hr.trans hrq) hq1 x ε hε

end SphericalAging.OrthogonalForkNonempty
