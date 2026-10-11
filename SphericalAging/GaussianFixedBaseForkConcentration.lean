module

public import SphericalAging.GaussianOrthogonalForkSupremum

public section

/-! The fixed-base orthogonal-fork supremum in Huang--Sellke (3.5),
under the literal original disorder product law. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianFixedBaseForkConcentration
open Set MeasureTheory ProbabilityTheory FiniteModel
open GaussianOrthogonalForkCovariance GaussianOrthogonalForkSupremum GaussianSmoothConcentration
open scoped NNReal
variable {N p K : ℕ}

@[expose] abbrev LeafDomain (N K : ℕ) (x : Vector N) (r q : ℝ) :=
  {y : Fin K→Vector N // OrthogonalFork x y r q}

@[expose] def supremum (a b r q : ℝ) (x : Vector N) (J : ForkDisorder N p K) : ℝ :=
  sSup (Set.range (fun y : LeafDomain N K x r q => averagedIncrement a b x y.1 J))

theorem supremum_centered_hasSubgaussianMGF (hN : 0<N) (hp : 1≤p) (hK : 0<K)
    (a b r q : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hq : 0≤q) (hq1 : q≤1) (x : Vector N) [Nonempty (LeafDomain N K x r q)] :
    HasSubgaussianMGF (fun J => supremum (p:=p) a b r q x J-
      ∫J',supremum a b r q x J' ∂forkLaw N p K) (forkConstant N K) (forkLaw N p K) := by
  let A : LeafDomain N K x r q→(ForkTensor N p K→L[ℝ] ℝ) :=
    fun y => forkDual a b x y.1
  have hA : ∀y,‖A y‖≤(⟨Real.sqrt (1/((K:ℝ)*N)),Real.sqrt_nonneg _⟩:ℝ≥0) :=
    fun y => orthogonal_forkDual_norm_le hN hp hK a b ha hab hb x y.1 r q hr hq hq1 y.2
  have hG := GaussianDualSupConcentration.supremum_centered_hasSubgaussianMGF A hA
  rw [fork_constant_eq] at hG
  have hLip := GaussianDualSupConcentration.supremum_lipschitz A hA
  have hEq (J : ForkDisorder N p K) :
      GaussianDualSupConcentration.supremum A (tensorInputs J)=supremum a b r q x J := by
    unfold GaussianDualSupConcentration.supremum supremum
    change sSup (Set.range (fun y : LeafDomain N K x r q => forkDual a b x y.1 (tensorInputs J)))=_
    simp_rw [forkDual_tensorInputs]
  have hMean := tensorInputs_hasLaw.integral_comp
    hLip.continuous.stronglyMeasurable.aestronglyMeasurable
  simp only [Function.comp_def] at hMean
  simp_rw [hEq] at hMean
  rw [←tensorInputs_hasLaw.map_eq] at hG
  have hh := HasSubgaussianMGF.of_map tensorInputs_hasLaw.aemeasurable hG
  rw [tensorInputs_hasLaw.map_eq] at hh
  simp only [Function.comp_def,hEq,←hMean] at hh
  exact hh

theorem supremum_centered_absolute_tail (hN : 0<N) (hp : 1≤p) (hK : 0<K)
    (a b r q : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hq : 0≤q) (hq1 : q≤1) (x : Vector N) [Nonempty (LeafDomain N K x r q)]
    (ε : ℝ) (hε : 0≤ε) :
    (forkLaw N p K).real {J | ε≤|supremum a b r q x J-∫J',supremum a b r q x J' ∂forkLaw N p K|}≤
      2*Real.exp (-((K:ℝ)*N)*ε^2/(2*(Real.pi/2)^2)) := by
  let X := fun J => supremum (N:=N) (p:=p) (K:=K) a b r q x J-
    ∫J',supremum a b r q x J' ∂forkLaw N p K
  have hG := supremum_centered_hasSubgaussianMGF hN hp hK a b r q ha hab hb hr hq hq1 x
  have hs : {J | ε≤|X J|}={J | ε≤X J}∪{J | ε≤-X J} := by
    ext J
    change ε≤|X J| ↔ ε≤X J ∨ ε≤-X J
    exact le_abs
  have hTail : (forkLaw N p K).real {J | ε≤|X J|}≤
      2*Real.exp (-ε^2/(2*(forkConstant N K:ℝ))) := by
    rw [hs]
    exact (measureReal_union_le _ _).trans
      (by simpa only [two_mul,Pi.neg_apply] using add_le_add (hG.measure_ge_le hε) (hG.neg.measure_ge_le hε))
  apply hTail.trans_eq
  congr 2
  change -ε^2/(2*((Real.pi/2)^2/((K:ℝ)*N))) = -((K:ℝ)*N)*ε^2/(2*(Real.pi/2)^2)
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hk : (K:ℝ)≠0 := by exact_mod_cast hK.ne'
  have hpi := Real.pi_ne_zero
  field_simp

end SphericalAging.GaussianFixedBaseForkConcentration
