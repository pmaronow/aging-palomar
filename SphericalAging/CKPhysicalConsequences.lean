module

public import SphericalAging.CKGlobalExistence

public section

/-!
# Physical consequences of the equations alone

Uniqueness identifies arbitrary CK data with the constructed physical solution.
Thus positivity, the unit covariance bound and Gram positivity do not have to
be inserted as independent assumptions in later global results.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace SphericalAging.CKPhysicalConsequences
open CKSpecification CKGlobalExistence CKLocalExistence CKPositivity

theorem physical_bounds_of_equations {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : PhysicalBounds d := by
  obtain ⟨e,he,hphys,_,_⟩ := ck_global_wellposedness h.spin_ge_three h.beta_pos
  have hh := CKWellposedness.ck_equations_unique he h
  constructor
  · intro t s ht hs
    rw [← hh.1 t s ht hs]
    exact hphys.1 t s ht hs
  · intro t s hs hst
    rw [← hh.2.1 t s hs hst]
    exact hphys.2 t s hs hst

theorem correlation_psd_of_equations {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : PositiveSemidefiniteCorrelation d := by
  obtain ⟨e,he,_,hpsd,_⟩ := ck_global_wellposedness h.spin_ge_three h.beta_pos
  have hh := CKWellposedness.ck_equations_unique he h
  intro n times weights htimes
  have heq : ∀ i j, e.C (times i) (times j)=d.C (times i) (times j) :=
    fun i j => hh.1 _ _ (htimes i) (htimes j)
  simpa only [heq] using hpsd n times weights htimes

theorem finite_compatibility {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKEquations p β d) (hT : 0 < T) :
    ∃ e : CKData, CKOnHorizon p β T e ∧
      (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, d.C t s=e.C t s) ∧
      (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, d.R t s=e.R t s) ∧
      (∀ t ∈ Icc 0 T, d.multiplier t=e.multiplier t) := by
  let f := actualFamily h.spin_ge_three h.beta_pos
  have hh := CKWellposedness.ck_equations_unique h (assembled_ck_equations f)
  have hf := assembled_fields_eq_on_square f hT
  refine ⟨f.data T,f.equations T hT,?_,?_,?_⟩
  · intro t ht s hs
    exact (hh.1 t s ht.1 hs.1).trans (hf.1 t ht s hs)
  · intro t ht s hs
    exact (hh.2.1 t s hs.1 hs.2).trans (hf.2.1 t ht s hs)
  · intro t ht
    exact (hh.2.2 t ht.1).trans (hf.2.2 t ht)

theorem correlation_strictly_positive {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) : 0 < d.C t s := by
  let T := max t s+1
  have hT : 0 < T := by dsimp only [T]; linarith [le_max_left t s]
  obtain ⟨e,he,hC,_,_⟩ := finite_compatibility h hT
  have htT : t ∈ Icc 0 T := ⟨ht,by dsimp only [T]; linarith [le_max_left t s]⟩
  have hsT : s ∈ Icc 0 T := ⟨hs,by dsimp only [T]; linarith [le_max_right t s]⟩
  rw [hC t htT s hsT]
  exact (ck_horizon_strictly_positive he).1 t htT s hsT

theorem response_strictly_positive {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : 0 < d.R t s := by
  have ht := hs.trans hst
  have hT : 0 < t+1 := by linarith
  obtain ⟨e,he,_,hR,_⟩ := finite_compatibility h hT
  rw [hR t ⟨ht,by linarith⟩ s ⟨hs,hst⟩]
  exact (ck_horizon_strictly_positive he).2 t ⟨ht,by linarith⟩ s ⟨hs,hst⟩

theorem response_le_correlation {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : d.R t s ≤ d.C t s := by
  have ht := hs.trans hst
  have hT : 0 < t+1 := by linarith
  obtain ⟨e,he,hC,hR,_⟩ := finite_compatibility h hT
  rw [hR t ⟨ht,by linarith⟩ s ⟨hs,hst⟩,hC t ⟨ht,by linarith⟩ s ⟨hs,by linarith⟩]
  exact FiniteResponseComparison.response_le_correlation he (ck_horizon_nonnegative he)
    ⟨ht,by linarith⟩ ⟨hs,hst⟩

theorem response_exponential_lower_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.exp (-(∫ u in s..t, d.multiplier u)) ≤ d.R t s := by
  have ht := hs.trans hst
  have hT : 0 < t+1 := by linarith
  obtain ⟨e,he,_,hR,hLambda⟩ := finite_compatibility h hT
  have hi : (∫ u in s..t, d.multiplier u)=∫ u in s..t, e.multiplier u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hst] at hu
    exact hLambda u ⟨hs.trans hu.1,by linarith [hu.2]⟩
  rw [hi,hR t ⟨ht,by linarith⟩ s ⟨hs,hst⟩]
  exact CKPositivity.response_exponential_lower_bound he (ck_horizon_nonnegative he)
    ⟨ht,by linarith⟩ ⟨hs,hst⟩

theorem multiplier_ge_one {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) : 1 ≤ d.multiplier t := by
  have hb := physical_bounds_of_equations h
  have hm : 0 ≤ memoryMass p d t := by
    apply intervalIntegral.integral_nonneg ht
    intro u hu
    exact mul_nonneg (pow_nonneg (hb.1 t u ht hu.1).1 _) (hb.2 t u hu.1 hu.2)
  rw [h.multiplier_eq t ht]
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (sq_nonneg β) (sq_nonneg (p : ℝ))) hm)

end SphericalAging.CKPhysicalConsequences
