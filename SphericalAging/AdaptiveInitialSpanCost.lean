module

public import SphericalAging.SeedSpanProjectionIdentity
public import SphericalAging.AdaptiveMomentComparison
public import SphericalAging.ExternalFieldCostLimsup
public import SphericalAging.AdaptiveResidualEnergyLimit

public section

/-! The initial-span field cost for the literal independent seed and
original disorder. Zero frame columns use a fixed unit direction for the
preceding external-field theorem; their actual contribution is zero. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AdaptiveInitialSpanCost
open Set Filter MeasureTheory FiniteModel SeedSpanOrthonormalFrame SeedSpanProjectionIdentity
open ExternalFieldUniformCost ExternalFieldSeededCost ExternalFieldCostLimsup
open ExternalFieldElementaryPenalty ExternalFieldSharpScalar AdaptiveResidualEnergyLimit
open scoped BigOperators InnerProductSpace Topology NNReal
variable {N p k : ℕ} {S : Type} [MeasurableSpace S]

@[expose] def direction (hN : 0<N) (W : Submodule ℝ (Vector N)) (i : Fin k) : Vector N :=
  Real.sqrt N • (if frame W k i=0 then HardSphereDynamics.basisVector ⟨0,hN⟩ else frame W k i)

theorem direction_norm (hN : 0<N) (W : Submodule ℝ (Vector N)) (i : Fin k) :
    ‖direction hN W i‖=Real.sqrt N := by
  unfold direction
  rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  by_cases hz : frame W k i=0
  · simp only [if_pos hz,HardSphereDynamics.basisVector,EuclideanSpace.norm_single,norm_one,mul_one]
  · simp only [if_neg hz]
    rw [(frame_zero_or_unit W k i).resolve_left hz,mul_one]

theorem direction_measurable (hN : 0<N) (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2)) (i : Fin k) :
    Measurable (fun s => direction hN (W s) i) := by
  have hf := frame_measurable W hW k i
  exact (measurable_const : Measurable (fun _ : S => Real.sqrt (N:ℝ))).smul (Measurable.ite
    (hf.stronglyMeasurable.measurableSet_eq_fun stronglyMeasurable_const)
    measurable_const hf)

@[expose] def pairing (W : S→Submodule ℝ (Vector N)) (A : S×Disorder N p→Vector N)
    (i : Fin k) (z : S×Disorder N p) : ℝ := ⟪frame (W z.1) k i,A z⟫_ℝ/Real.sqrt N

theorem pairing_measurable (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2))
    (A : S×Disorder N p→Vector N) (hA : Measurable A) (i : Fin k) :
    Measurable (pairing W A i) :=
  ((frame_measurable W hW k i).comp measurable_fst |>.inner hA).div_const _

theorem pairing_abs_le_one (hN : 0<N) (W : S→Submodule ℝ (Vector N))
    (A : S×Disorder N p→Vector N) (hball : ∀z,‖A z‖≤Real.sqrt N) (i : Fin k)
    (z : S×Disorder N p) : |pairing W A i z|≤1 := by
  have hn : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hf : ‖frame (W z.1) k i‖≤1 := by
    rcases frame_zero_or_unit (W z.1) k i with hz | hz
    · simp only [hz,norm_zero];norm_num
    · exact hz.le
  unfold pairing
  rw [abs_div,abs_of_pos hn]
  apply (div_le_one hn).mpr
  exact (abs_real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_right hf (norm_nonneg _)).trans (by simpa only [one_mul] using hball z))

theorem pairing_power_integrable (hN : 0<N) (ν : Measure S) [IsProbabilityMeasure ν]
    (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2))
    (A : S×Disorder N p→Vector N) (hA : Measurable A)
    (hball : ∀z,‖A z‖≤Real.sqrt N) (i : Fin k) (m : ℕ) :
    Integrable (fun z => |pairing W A i z|^m) (ν.prod (disorderLaw N p)) := by
  apply (integrable_const (1:ℝ)).mono'
    ((continuous_abs.measurable.comp (pairing_measurable W hW A hA i)).pow_const m).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact pow_le_one₀ (abs_nonneg _) (pairing_abs_le_one hN W A hball i z))

theorem pairing_direction_power (hN : 0<N) (W : S→Submodule ℝ (Vector N))
    (A : S×Disorder N p→Vector N) (i : Fin k) (z : S×Disorder N p) :
    |pairing W A i z|^p≤seededOverlapPower (p := p) (fun s => direction hN (W s) i) A z := by
  by_cases hz : frame (W z.1) k i=0
  · unfold pairing
    simp only [hz,inner_zero_left,zero_div,abs_zero]
    exact pow_le_pow_left₀ (by norm_num : (0:ℝ)≤0) (abs_nonneg _) _
  · have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
    have hs : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
    unfold seededOverlapPower direction pairing
    simp only [if_neg hz,real_inner_smul_left]
    have he : Real.sqrt (N:ℝ)*⟪frame (W z.1) k i,A z⟫_ℝ/N=
        ⟪frame (W z.1) k i,A z⟫_ℝ/Real.sqrt N := by
      field_simp
      rw [Real.sq_sqrt (Nat.cast_nonneg N)]
      ring
    rw [he]

theorem projectionEnergy_eq_pairing_sum (hN : 0<N) (ν : Measure S) [IsProbabilityMeasure ν]
    (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2))
    (hRank : ∀s,Module.finrank ℝ (W s)≤k)
    (A : S×Disorder N p→Vector N) (hA : Measurable A)
    (hball : ∀z,‖A z‖≤Real.sqrt N) :
    projectionEnergy ν (fun z : S×Disorder N p => W z.1) A=
      ∑i : Fin k,∫z,|pairing W A i z|^2 ∂ν.prod (disorderLaw N p) := by
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  unfold projectionEnergy
  have he : (fun z : S×Disorder N p => ‖(W z.1).starProjection (A z)‖^2/(N:ℝ))=
      (fun z => ∑i : Fin k,|pairing W A i z|^2) := by
    funext z
    rw [projection_norm_sq_eq_frame_sum (W z.1) (hRank z.1),Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    unfold pairing
    rw [sq_abs,div_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [he,integral_finsetSum _ (fun i _ => pairing_power_integrable hN ν W hW A hA hball i 2)]

/-- Finite algebraic consequence of actual directional costs. The source
theorem below derives every directional cost from the preceding threshold. -/
theorem projectionEnergy_le_of_direction_cost (hN : 0<N) (hp : 3≤p)
    (ν : Measure S) [IsProbabilityMeasure ν]
    (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2))
    (hRank : ∀s,Module.finrank ℝ (W s)≤k)
    (A : S×Disorder N p→Vector N) (hA : Measurable A)
    (hball : ∀z,‖A z‖≤Real.sqrt N) (ε : ℝ)
    (hcost : ∀i : Fin k, (∫z,seededCost (p := p)
      (fun s => direction hN (W s) i) A z ∂ν.prod (disorderLaw N p))≤thresholdEnergy p+ε) :
    projectionEnergy ν (fun z : S×Disorder N p => W z.1) A≤
      (k:ℝ)*(max 0 (thresholdEnergy p+ε-meanEnergy ν A)/betaD p)^(2/(p:ℝ)) := by
  have hβ : 0<betaD p := betaD_positive hp
  have hpow : 0≤2/(p:ℝ) := by positivity
  let C : ℝ := max 0 (thresholdEnergy p+ε-meanEnergy ν A)/betaD p
  have hC : 0≤C := div_nonneg (le_max_left _ _) hβ.le
  have hi (i : Fin k) : (∫z,|pairing W A i z|^2 ∂ν.prod (disorderLaw N p))≤C^(2/(p:ℝ)) := by
    let w : S→Vector N := fun s => direction hN (W s) i
    have hw : Measurable w := direction_measurable hN W hW i
    have hg : ∀ᵐs ∂ν,(∀J,‖A (s,J)‖≤Real.sqrt N) ∧ ‖w s‖=Real.sqrt N :=
      ae_of_all _ (fun s => ⟨fun J => hball (s,J),direction_norm hN (W s) i⟩)
    have hspi := seededOverlapPower_integrable (by omega : 1≤N) ν hw hA hg
    have hcmp : (∫z,|pairing W A i z|^p ∂ν.prod (disorderLaw N p))≤
        ∫z,seededOverlapPower (p := p) w A z ∂ν.prod (disorderLaw N p) :=
      integral_mono (pairing_power_integrable hN ν W hW A hA hball i p) hspi
        (pairing_direction_power hN W A i)
    have hsplit := seededCost_integral_split (by omega : 1≤N) hp ν hw hA hg
    have he : (∫z,Hamiltonian N p z.2 (A z)/(N:ℝ) ∂ν.prod (disorderLaw N p))=meanEnergy ν A := by
      rw [integral_div];rfl
    rw [he] at hsplit
    have hc := hcost i
    change (∫z,seededCost (p := p) w A z ∂ν.prod (disorderLaw N p))≤_ at hc
    rw [hsplit] at hc
    have hpc : (∫z,|pairing W A i z|^p ∂ν.prod (disorderLaw N p))≤C := by
      apply (le_div_iff₀ hβ).mpr
      have hm := mul_le_mul_of_nonneg_left hcmp hβ.le
      have hmax := le_max_right (0:ℝ) (thresholdEnergy p+ε-meanEnergy ν A)
      change _≤max 0 (thresholdEnergy p+ε-meanEnergy ν A)
      nlinarith
    exact (AdaptiveMomentComparison.square_le_power_mean (ν.prod (disorderLaw N p))
      (by omega : 2≤p) (pairing W A i) (pairing_measurable W hW A hA i)
      (pairing_abs_le_one hN W A hball i)).trans
        (Real.rpow_le_rpow (integral_nonneg (fun z => pow_nonneg (abs_nonneg _) _)) hpc hpow)
  rw [projectionEnergy_eq_pairing_sum hN ν W hW hRank A hA hball]
  calc
    _≤∑_i : Fin k,C^(2/(p:ℝ)) := Finset.sum_le_sum (fun i _ => hi i)
    _=(k:ℝ)*C^(2/(p:ℝ)) := by simp

/-- Actual initial-span cost at finite dimension, with no field-cost or
projection-penalty input. Only the explicitly preceding research theorem
10.1 is external. -/
theorem initial_span_cost_eventually {p k : ℕ} (hp : 3≤p) {L : ℝ≥0}
    (H : PublishedFieldThreshold p L) (dim : ℕ→ℕ)
    (hDim : ∀n,0<dim n) (hTop : Tendsto dim atTop atTop)
    {S : ℕ→Type} [∀n,MeasurableSpace (S n)] (ν : ∀n,Measure (S n))
    [∀n,IsProbabilityMeasure (ν n)]
    (W : ∀n,S n→Submodule ℝ (Vector (dim n)))
    (hW : ∀n,Measurable (fun z : S n×Vector (dim n) => (W n z.1).starProjection z.2))
    (hRank : ∀n s,Module.finrank ℝ (W n s)≤k)
    (A : ∀n,S n×Disorder (dim n) p→Vector (dim n))
    (hA : ∀n,Measurable (A n)) (hball : ∀n z,‖A n z‖≤Real.sqrt (dim n))
    (hLip : ∀n,∀ᵐs ∂ν n,LipschitzWith L
      (fun J : EuclideanSpace ℝ (TensorIndex (dim n) p) => A n (s,J.ofLp))) :
    ∀ε>0,∀ᶠn in atTop,
      projectionEnergy (ν n) (fun z : S n×Disorder (dim n) p => W n z.1) (A n)≤
        (k:ℝ)*(max 0 (thresholdEnergy p+ε-meanEnergy (ν n) (A n))/betaD p)^(2/(p:ℝ)) := by
  intro ε hε
  have hc (i : Fin k) := seeded_cost_eventually hp H dim (fun n => hDim n)
    hTop ν (fun n s => direction (hDim n) (W n s) i) A
    (fun n => direction_measurable (hDim n) (W n) (hW n) i) hA
    (fun n => (hLip n).mono (fun s hs =>
      ⟨hs,fun J => hball n (s,J),direction_norm (hDim n) (W n s) i⟩)) ε hε
  filter_upwards [Filter.eventually_all.mpr hc] with n hn
  exact projectionEnergy_le_of_direction_cost (hDim n) hp (ν n) (W n) (hW n)
    (hRank n) (A n) (hA n) (hball n) ε hn

end SphericalAging.AdaptiveInitialSpanCost
