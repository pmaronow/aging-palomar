module

public import SphericalAging.AdaptiveResidualEnergyLoss
public import SphericalAging.SeedAlgorithmEnergyBounds
public import SphericalAging.AlgorithmEnergyDeficit

public section

/-! Source10.7 Step2 at the dimension limit. The finite loss, all uniform
energy/projection bounds, and the residual lower limit are derived from
the literal original Gaussian model and the actual ball-valued algorithm. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace SphericalAging.AdaptiveResidualEnergyLimit
open FiniteModel GaussianLandscape GaussianLandscapeMoments
open AdaptiveResidualEnergyLoss SeedAlgorithmEnergyBounds AsymptoticErrorTransfer AlgorithmEnergyDeficit

@[expose] def residual {N p : ℕ} {S : Type} (W : S×Disorder N p→Submodule ℝ (Vector N))
    (A : S×Disorder N p→Vector N) (z : S×Disorder N p) : Vector N :=
  (W z)ᗮ.starProjection (A z)

@[expose] def meanEnergy {N p : ℕ} {S : Type} [MeasurableSpace S] (ν : Measure S)
    (A : S×Disorder N p→Vector N) : ℝ :=
  (∫z,Hamiltonian N p z.2 (A z) ∂ν.prod (disorderLaw N p))/(N:ℝ)

@[expose] def projectionEnergy {N p : ℕ} {S : Type} [MeasurableSpace S] (ν : Measure S)
    (W : S×Disorder N p→Submodule ℝ (Vector N)) (A : S×Disorder N p→Vector N) : ℝ :=
  ∫z,‖(W z).starProjection (A z)‖^2/(N:ℝ) ∂ν.prod (disorderLaw N p)

theorem residual_measurable {N p : ℕ} {S : Type} [MeasurableSpace S]
    (W : S×Disorder N p→Submodule ℝ (Vector N)) (A : S×Disorder N p→Vector N)
    (hA : Measurable A) (hP : Measurable (fun z => (W z).starProjection (A z))) :
    Measurable (residual W A) := by
  have he : residual W A=A-(fun z => (W z).starProjection (A z)) := by
    funext z
    exact Submodule.starProjection_orthogonal_val _
  rw [he]
  exact hA.sub hP

theorem residual_ball {N p : ℕ} {S : Type}
    (W : S×Disorder N p→Submodule ℝ (Vector N)) (A : S×Disorder N p→Vector N)
    (hball : ∀z,‖A z‖≤Real.sqrt N) (z : S×Disorder N p) :
    ‖residual W A z‖≤Real.sqrt N :=
  ((W z)ᗮ.norm_starProjection_apply_le (A z)).trans (hball z)

theorem meanEnergy_abs_bound {N p : ℕ} (hN : 0<N) (hp : 0<p)
    {S : Type} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (A : S×Disorder N p→Vector N) (hA : Measurable A)
    (hball : ∀z,‖A z‖≤Real.sqrt N) : |meanEnergy ν A|≤momentCeiling p 1 := by
  have hh := energy_integrable_bound hN (by omega : 1≤p) ν hA
    (ae_of_all _ (fun s J => hball (s,J)))
  simpa only [meanEnergy,energy,integral_div] using hh.2

theorem projectionEnergy_bounds {N p : ℕ} (hN : 0<N)
    {S : Type} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (W : S×Disorder N p→Submodule ℝ (Vector N)) (A : S×Disorder N p→Vector N)
    (hP : Measurable (fun z => (W z).starProjection (A z)))
    (hball : ∀z,‖A z‖≤Real.sqrt N) :
    0≤projectionEnergy ν W A ∧ projectionEnergy ν W A≤1 := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hpb (z : S×Disorder N p) : ‖(W z).starProjection (A z)‖≤Real.sqrt N :=
    ((W z).norm_starProjection_apply_le (A z)).trans (hball z)
  have hm : MemLp (fun z => (W z).starProjection (A z)) 2 (ν.prod (disorderLaw N p)) :=
    MemLp.of_bound hP.aestronglyMeasurable (Real.sqrt N) (ae_of_all _ hpb)
  have hi : Integrable (fun z => ‖(W z).starProjection (A z)‖^2/(N:ℝ))
      (ν.prod (disorderLaw N p)) :=
    ((memLp_two_iff_integrable_sq hm.norm.aestronglyMeasurable).mp hm.norm).div_const (N:ℝ)
  refine ⟨integral_nonneg (fun z => div_nonneg (sq_nonneg _) hNr.le),?_⟩
  calc
    _≤∫z : S×Disorder N p,(1:ℝ) ∂ν.prod (disorderLaw N p) := by
      apply integral_mono hi (integrable_const 1)
      intro z
      apply (div_le_one hNr).mpr
      have hh := pow_le_pow_left₀ (norm_nonneg _) (hpb z) 2
      simpa only [Real.sq_sqrt hNr.le] using hh
    _=1 := by simp

/-- The printed residual-energy lower limit, including its literal deficit.
Only actual algorithm measurability and the deterministic ball constraint
are inputs; finite losses and limit boundedness are established internally. -/
theorem actual_residual_energy_liminf {p : ℕ} (hp : 0<p)
    {dim : ℕ→ℕ} (hDim : ∀n,0<dim n)
    {S : ℕ→Type} [∀n,MeasurableSpace (S n)] (ν : ∀n,Measure (S n))
    [∀n,IsProbabilityMeasure (ν n)]
    (W : ∀n,S n×Disorder (dim n) p→Submodule ℝ (Vector (dim n)))
    (A : ∀n,S n×Disorder (dim n) p→Vector (dim n))
    (hA : ∀n,Measurable (A n))
    (hP : ∀n,Measurable (fun z => (W n z).starProjection (A n z)))
    (hball : ∀n z,‖A n z‖≤Real.sqrt (dim n)) (E : ℝ) :
    E-deficit E (fun n => meanEnergy (ν n) (A n))-
      (p:ℝ)*Real.sqrt (momentCeiling p 2)*
        Real.sqrt (limsup (fun n => projectionEnergy (ν n) (W n) (A n)) atTop)≤
      liminf (fun n => meanEnergy (ν n) (residual (W n) (A n))) atTop := by
  let a n := meanEnergy (ν n) (A n)
  let b n := meanEnergy (ν n) (residual (W n) (A n))
  let m n := projectionEnergy (ν n) (W n) (A n)
  let C : ℝ := (p:ℝ)*Real.sqrt (momentCeiling p 2)
  have hC : 0≤C := by dsimp only [C];positivity
  have hAB n : |a n|≤momentCeiling p 1 := meanEnergy_abs_bound (hDim n) hp (ν n) (A n) (hA n) (hball n)
  have hBB n : |b n|≤momentCeiling p 1 := meanEnergy_abs_bound (hDim n) hp (ν n)
    (residual (W n) (A n)) (residual_measurable (W n) (A n) (hA n) (hP n))
    (residual_ball (W n) (A n) (hball n))
  have hMB n : 0≤m n ∧ m n≤1 := projectionEnergy_bounds (hDim n) (ν n) (W n) (A n) (hP n) (hball n)
  have haBelow : IsBoundedUnder (·≥·) atTop a := isBoundedUnder_of_eventually_ge
    (Eventually.of_forall fun n => show -momentCeiling p 1≤a n from by
      linarith [hAB n,neg_abs_le (a n)])
  have hbAbove : IsBoundedUnder (·≤·) atTop b := isBoundedUnder_of_eventually_le
    (Eventually.of_forall fun n => (le_abs_self (b n)).trans (hBB n))
  have hmAbove : IsBoundedUnder (·≤·) atTop m :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => (hMB n).2)
  have hsAbove : IsBoundedUnder (·≤·) atTop (fun n => Real.sqrt (m n)) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => show Real.sqrt (m n)≤1 from
      (Real.sqrt_le_sqrt (hMB n).2).trans_eq (by norm_num))
  have hpoint n : a n-C*Real.sqrt (m n)≤b n := by
    exact actual_seed_residual_energy_lower (hDim n) hp (ν n) (W n) (A n)
      (hA n).aestronglyMeasurable (hP n).aestronglyMeasurable (ae_of_all _ (hball n))
  have hLower := AlgorithmEnergyDeficit.energy_lower E a
  change E-deficit E a-C*Real.sqrt (limsup m atTop)≤liminf b atTop
  apply le_of_forall_pos_le_add
  intro η hη
  let ξ : ℝ := η/(C+1)
  have hden : 0<C+1 := by positivity
  have hξ : 0<ξ := div_pos hη hden
  have hAE := eventually_lt_of_lt_liminf
    (show E-deficit E a-ξ<liminf a atTop by linarith) haBelow
  have hSE := eventually_lt_of_limsup_lt
    (show limsup (fun n => Real.sqrt (m n)) atTop<Real.sqrt (limsup m atTop)+ξ by
      rw [limsup_sqrt_eq hmAbove (fun n => (hMB n).1)]
      linarith) hsAbove
  have hp' : ∀ᶠn in atTop,E-deficit E a-C*Real.sqrt (limsup m atTop)-(C+1)*ξ≤b n := by
    filter_upwards [hAE,hSE] with n hn hs
    have hh := mul_le_mul_of_nonneg_left hs.le hC
    linarith [hpoint n]
  have hh := le_liminf_of_le hbAbove.isCoboundedUnder_ge hp'
  have hξeq : (C+1)*ξ=η := by dsimp only [ξ];field_simp
  linarith

end SphericalAging.AdaptiveResidualEnergyLimit
