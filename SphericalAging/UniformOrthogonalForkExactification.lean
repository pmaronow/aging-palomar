module

public import SphericalAging.GramForkExactification
public import SphericalAging.ExactOrthogonalIncrements

public section

/-! Uniform fixed-branching exactification of actual approximate fork Gram
entries. The error tends to zero independently of the ambient dimension,
including vanishing increment norms. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.UniformOrthogonalForkExactification
open FiniteModel GramForkExactification ExactOrthogonalIncrements
open scoped InnerProductSpace Topology
variable {N K : ℕ}

@[expose] def error (K : ℕ) (ε : ℝ) : ℝ :=
  (4*Real.sqrt ((K+1:ℕ):ℝ)+1)*Real.sqrt ε+2*Real.sqrt (Real.sqrt ε)

private theorem large_error_bound (K : ℕ) (ε : ℝ) (hε : 0<ε)
    (hsmall : 4*((K+1:ℕ):ℝ)*Real.sqrt ε≤1) :
    2*Real.sqrt (((K+1:ℕ):ℝ)*ε^2/(Real.sqrt ε/2-((K+1:ℕ):ℝ)*ε))+Real.sqrt ε≤error K ε := by
  let c : ℝ := ((K+1:ℕ):ℝ)
  let s := Real.sqrt ε
  have hc : 1≤c := by dsimp [c];norm_cast;omega
  have hs : 0<s := Real.sqrt_pos.mpr hε
  have hsq : s^2=ε := Real.sq_sqrt hε.le
  have hcs : 4*c*s≤1 := hsmall
  have hs1 : s≤1 := by nlinarith
  have hep : ε≤s := by nlinarith
  have hmult := mul_le_mul_of_nonneg_right hcs hs.le
  have hgap : s/4≤s/2-c*ε := by nlinarith
  have hgpos : 0<s/2-c*ε := (by positivity : 0<s/4).trans_le hgap
  have hprod := mul_le_mul_of_nonneg_left hep (by positivity : 0≤c*ε)
  have hgapmul := mul_le_mul_of_nonneg_left hgap (by positivity : 0≤4*c*ε)
  have hratio : c*ε^2/(s/2-c*ε)≤4*c*ε := by
    apply (div_le_iff₀ hgpos).mpr
    nlinarith
  have hr : Real.sqrt (c*ε^2/(s/2-c*ε))≤2*Real.sqrt c*s := by
    have hh := Real.sqrt_le_sqrt hratio
    have he : Real.sqrt (4*c*ε)=2*Real.sqrt c*s := by
      rw [Real.sqrt_mul (by positivity : 0≤4*c),Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
      rw [show Real.sqrt (4:ℝ)=2 by norm_num]
    exact hh.trans_eq he
  change 2*Real.sqrt (c*ε^2/(s/2-c*ε))+s≤(4*Real.sqrt c+1)*s+2*Real.sqrt s
  nlinarith [Real.sqrt_nonneg s]

theorem actual_uniform_exactification (hKN : K<N) (x : Vector N) (y : Fin K→Vector N)
    (q0 q q' ε : ℝ) (hq0 : 0<q0) (hqq0 : q0≤q) (hq' : 0≤q')
    (hε : 0≤ε) (hbaseSmall : Real.sqrt ε≤q0)
    (hsmall : 4*((K+1:ℕ):ℝ)*Real.sqrt ε≤1)
    (hx : ‖x‖^2=q) (hy : ∀i,|‖y i‖^2-q'|≤ε)
    (hxy : ∀i,|⟪x,y i⟫_ℝ|≤ε) (hyy : ∀i j,i≠j→|⟪y i,y j⟫_ℝ|≤ε) :
    ∃z : Fin K→Vector N,(∀i,‖z i‖^2=q') ∧ (∀i,⟪x,z i⟫_ℝ=0) ∧
      (∀i j,i≠j→⟪z i,z j⟫_ℝ=0) ∧ (∀i,‖z i-y i‖≤error K ε) := by
  have hq : 0<q := hq0.trans_le hqq0
  by_cases hezero : ε=0
  · subst ε
    refine ⟨y,?_,?_,?_,?_⟩
    · intro i;exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (hy i) (abs_nonneg _)))
    · intro i;exact abs_eq_zero.mp (le_antisymm (hxy i) (abs_nonneg _))
    · intro i j hij;exact abs_eq_zero.mp (le_antisymm (hyy i j hij) (abs_nonneg _))
    · intro i;simp [error]
  have hep : 0<ε := lt_of_le_of_ne hε (Ne.symm hezero)
  by_cases hqsmall : q'≤Real.sqrt ε
  · obtain ⟨z,hzn,hzx,hzz,hd⟩ := small_increment_exactification hKN x y q q' ε hq.le hq' hε hx hy
    refine ⟨z,hzn,hzx,hzz,?_⟩
    intro i
    have hh := Real.sqrt_le_sqrt hqsmall
    have hroot := Real.sqrt_nonneg ε
    have hc := Real.sqrt_nonneg ((K+1:ℕ):ℝ)
    exact (hd i).trans (by dsimp [error];nlinarith)
  have hlarge : Real.sqrt ε≤q' := (lt_of_not_ge hqsmall).le
  let γ := Real.sqrt ε/2
  have hc : 1≤((K+1:ℕ):ℝ) := by norm_cast;omega
  have hs : 0<Real.sqrt ε := Real.sqrt_pos.mpr hep
  have hsq := Real.sq_sqrt hε
  have hsquarter : Real.sqrt ε≤1/4 := by nlinarith
  have hehalf : ε≤Real.sqrt ε/2 := by nlinarith
  have hmult := mul_le_mul_of_nonneg_right hsmall hs.le
  have hgap : 0<γ-((K+1:ℕ):ℝ)*ε := by dsimp [γ];nlinarith
  have hdiag : ∀i : Fin (K+1),γ≤‖Fin.cons (α := fun _ : Fin (K+1) => Vector N) x y i‖^2 := by
    intro i;refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero,hx];dsimp [γ];linarith
    · simp only [Fin.cons_succ]
      have hh := (abs_le.mp (hy j)).1
      dsimp [γ];linarith
  have hcross : ∀i j : Fin (K+1),i≠j→
      |⟪Fin.cons (α := fun _ : Fin (K+1) => Vector N) x y i,
        Fin.cons (α := fun _ : Fin (K+1) => Vector N) x y j⟫_ℝ|≤ε := by
    intro i;refine Fin.cases ?_ (fun a => ?_) i
    · intro j;refine Fin.cases ?_ (fun b => ?_) j
      · intro h;exact False.elim (h rfl)
      · intro _;simpa only [Fin.cons_zero,Fin.cons_succ] using hxy b
    · intro j;refine Fin.cases ?_ (fun b => ?_) j
      · intro _;simpa only [Fin.cons_zero,Fin.cons_succ,real_inner_comm] using hxy a
      · intro h;simpa only [Fin.cons_succ] using hyy a b (fun hh => h (congrArg Fin.succ hh))
  obtain ⟨z,hzn,hzx,hzz,hd⟩ := actual_base_preserving_exactification x y q q' γ ε hq hq' hε hgap hx hdiag hcross hy
  exact ⟨z,hzn,hzx,hzz,fun i => (hd i).trans (large_error_bound K ε hep hsmall)⟩

theorem error_tendsto_zero (K : ℕ) : Filter.Tendsto (error K) (nhdsWithin 0 (Set.Ici 0)) (𝓝 0) := by
  have ht : Filter.Tendsto (fun ε : ℝ => Real.sqrt ε) (nhdsWithin 0 (Set.Ici 0)) (𝓝 0) := by
    have hh : ContinuousAt Real.sqrt (0:ℝ) := Real.continuous_sqrt.continuousAt
    simpa only [Real.sqrt_zero] using hh.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ici (0:ℝ)))
  have ht2 := ht.sqrt
  change Filter.Tendsto (fun ε : ℝ => (4*Real.sqrt ((K+1:ℕ):ℝ)+1)*Real.sqrt ε+2*Real.sqrt (Real.sqrt ε)) _ _
  simpa only [Real.sqrt_zero,mul_zero,add_zero] using
    (ht.const_mul (4*Real.sqrt ((K+1:ℕ):ℝ)+1)).add (ht2.const_mul 2)

end SphericalAging.UniformOrthogonalForkExactification
