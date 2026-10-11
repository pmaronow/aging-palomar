module

public import SphericalAging.UniformOrthogonalForkExactification

public section

/-! The actual recursive fork-correction modulus and its uniform finite-depth
zero-error limit. All small-error conditions hold eventually. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.TreeExactificationError
open UniformOrthogonalForkExactification Filter
open scoped Topology

@[expose] def correctionError (K : ℕ) (η : ℝ) : ℕ→ℝ
  | 0 => Real.sqrt η
  | d+1 => error K (3*η+2*correctionError K η d)

theorem correctionError_nonneg (K : ℕ) (η : ℝ) (d : ℕ) : 0≤correctionError K η d := by
  cases d with
  | zero => exact Real.sqrt_nonneg _
  | succ d => dsimp [correctionError,error];positivity

theorem correctionError_tendsto_zero (K d : ℕ) :
    Tendsto (fun η : ℝ => correctionError K η d) (nhdsWithin 0 (Set.Ici 0)) (𝓝 0) := by
  have ht : Tendsto (fun η : ℝ => η) (nhdsWithin 0 (Set.Ici 0)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  induction d with
  | zero => simpa only [correctionError,Real.sqrt_zero] using ht.sqrt
  | succ d ih =>
    have hδ : Tendsto (fun η : ℝ => 3*η+2*correctionError K η d)
        (nhdsWithin 0 (Set.Ici 0)) (𝓝 0) := by
      simpa only [mul_zero,add_zero] using (ht.const_mul 3).add (ih.const_mul 2)
    have hs := hδ.sqrt
    have hss := hs.sqrt
    change Tendsto (fun η : ℝ => (4*Real.sqrt ((K+1:ℕ):ℝ)+1)*
      Real.sqrt (3*η+2*correctionError K η d)+
      2*Real.sqrt (Real.sqrt (3*η+2*correctionError K η d))) _ _
    simpa only [Real.sqrt_zero,mul_zero,add_zero] using
      (hs.const_mul (4*Real.sqrt ((K+1:ℕ):ℝ)+1)).add (hss.const_mul 2)

@[expose] def SmallConditions (K D : ℕ) (qmin η : ℝ) : Prop :=
  0≤η ∧ η<qmin ∧ ∀l,l<D→
    Real.sqrt (3*η+2*correctionError K η l)≤qmin ∧
    4*((K+1:ℕ):ℝ)*Real.sqrt (3*η+2*correctionError K η l)≤1

theorem eventually_smallConditions (K D : ℕ) (qmin : ℝ) (hmin : 0<qmin) :
    ∀ᶠη : ℝ in nhdsWithin 0 (Set.Ici 0),SmallConditions K D qmin η := by
  have ht : Tendsto (fun η : ℝ => η) (nhdsWithin 0 (Set.Ici 0)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlt : ∀ᶠη : ℝ in nhdsWithin 0 (Set.Ici 0),η<qmin :=
    ht.eventually (eventually_lt_nhds hmin)
  have hnon : ∀ᶠη : ℝ in nhdsWithin 0 (Set.Ici 0),0≤η := self_mem_nhdsWithin
  have hall : ∀D : ℕ,∀ᶠη : ℝ in nhdsWithin 0 (Set.Ici 0),∀l,l<D→
      Real.sqrt (3*η+2*correctionError K η l)≤qmin ∧
      4*((K+1:ℕ):ℝ)*Real.sqrt (3*η+2*correctionError K η l)≤1 := by
    intro D
    induction D with
    | zero => exact Eventually.of_forall (by intro η l hl;omega)
    | succ D ih =>
      have hδ : Tendsto (fun η : ℝ => 3*η+2*correctionError K η D)
          (nhdsWithin 0 (Set.Ici 0)) (𝓝 0) := by
        simpa only [mul_zero,add_zero] using
          (ht.const_mul 3).add ((correctionError_tendsto_zero K D).const_mul 2)
      have hs : Tendsto (fun η : ℝ => Real.sqrt (3*η+2*correctionError K η D))
          (nhdsWithin 0 (Set.Ici 0)) (𝓝 0) := by simpa only [Real.sqrt_zero] using hδ.sqrt
      have hsb := hs.eventually (eventually_lt_nhds hmin)
      have hsc : Tendsto (fun η : ℝ => 4*((K+1:ℕ):ℝ)*Real.sqrt (3*η+2*correctionError K η D))
          (nhdsWithin 0 (Set.Ici 0)) (𝓝 0) := by simpa only [mul_zero] using hs.const_mul (4*((K+1:ℕ):ℝ))
      have hscb := hsc.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
      filter_upwards [ih,hsb,hscb] with η hη hb hc
      intro l hl
      by_cases heq : l=D
      · subst l;exact ⟨hb.le,hc.le⟩
      · exact hη l (by omega)
  filter_upwards [hnon,hlt,hall D] with η hη hlt hall
  exact ⟨hη,hlt,hall⟩

end SphericalAging.TreeExactificationError
