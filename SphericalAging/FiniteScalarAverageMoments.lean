module

public import SphericalAging.FiniteForkCenterConcentration

public section

/-! Finite scalar averages retain a common centered second-moment bound.
The summands can be arbitrarily dependent. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteScalarAverageMoments
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem average_centered_square_le (hK : 0<K) (a : Fin K→ℝ) (c : ℝ) :
    ((K:ℝ)⁻¹*∑b,a b-c)^2≤(K:ℝ)⁻¹*∑b,(a b-c)^2 := by
  have hK0 : (K:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hK)
  have he : (K:ℝ)⁻¹*∑b,a b-c=(K:ℝ)⁻¹*∑b,(a b-c) := by
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin K))
    (fun _ => (1:ℝ)) (fun b => a b-c)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
  rw [he,mul_pow]
  calc
    _≤(K:ℝ)⁻¹^2*((K:ℝ)*∑b,(a b-c)^2) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _=_ := by field_simp

theorem average_centered_secondMoment_le (hK : 0<K) [IsProbabilityMeasure P]
    (a : Fin K→Ω→ℝ) (c B : ℝ)
    (ha : ∀b,MemLp (a b) 2 P)
    (hB : ∀b,(∫ω,(a b ω-c)^2 ∂P)≤B) :
    MemLp (fun ω => (K:ℝ)⁻¹*∑b,a b ω) 2 P ∧
    (∫ω,((K:ℝ)⁻¹*∑b,a b ω-c)^2 ∂P)≤B := by
  have hm : MemLp (fun ω => (K:ℝ)⁻¹*∑b,a b ω) 2 P :=
    (memLp_finsetSum Finset.univ (fun b _ => ha b)).const_mul (K:ℝ)⁻¹
  have hc (b : Fin K) : Integrable (fun ω => (a b ω-c)^2) P :=
    ((ha b).sub (memLp_const c)).integrable_sq
  refine ⟨hm,?_⟩
  calc
    _≤∫ω,(K:ℝ)⁻¹*∑b,(a b ω-c)^2 ∂P :=
      integral_mono_ae ((hm.sub (memLp_const c)).integrable_sq)
        ((integrable_finsetSum Finset.univ (fun b _ => hc b)).const_mul (K:ℝ)⁻¹)
        (.of_forall fun ω => average_centered_square_le hK (fun b => a b ω) c)
    _=(K:ℝ)⁻¹*∑b,∫ω,(a b ω-c)^2 ∂P := by
      rw [integral_const_mul,integral_finsetSum Finset.univ (fun b _ => hc b)]
    _≤(K:ℝ)⁻¹*∑_b : Fin K,B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => hB b) (by positivity)
    _=B := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp [ne_of_gt (Nat.cast_pos.mpr hK : (0:ℝ)<K)]

end SphericalAging.FiniteScalarAverageMoments
