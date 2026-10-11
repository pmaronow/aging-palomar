module

public import SphericalAging.CKFiniteUniqueness
public import SphericalAging.BackwardResponse

public section

/-! Stability of approximate integral CK equations. Approximate correlations
may be semimartingales: no derivative of an approximate row is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalAging.CKStability
open CKSpecification CKLocalExistence TriangleUniqueness CKFiniteUniqueness

structure RegularData (d : CKData) : Prop where
  correlation_continuous : Continuous (Function.uncurry d.C)
  response_continuous : Continuous (Function.uncurry d.R)
  multiplier_continuous : Continuous d.multiplier
  correlation_symmetric : ∀ t s : ℝ,0 ≤ t → 0 ≤ s → d.C t s=d.C s t

theorem regularData_of_equations {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) : RegularData d :=
  ⟨h.correlation_continuous,h.response_continuous,h.multiplier_continuous,
    fun t s _ _ => h.correlation_symmetric t s⟩

@[expose] def symmetricCorrelation (d : CKData) (t s : ℝ) : ℝ :=
  d.C (max 0 t) (max 0 s)

@[expose] def symmetricResponse (d : CKData) (t s : ℝ) : ℝ :=
  d.R (max (max 0 t) (max 0 s)) (min (max 0 t) (max 0 s))

theorem symmetricCorrelation_continuous {d : CKData}
    (h : RegularData d) : Continuous (Function.uncurry (symmetricCorrelation d)) :=
  h.correlation_continuous.comp
    (show Continuous (fun z : ℝ × ℝ => (max 0 z.1,max 0 z.2)) by fun_prop)

theorem symmetricResponse_continuous {d : CKData}
    (h : RegularData d) : Continuous (Function.uncurry (symmetricResponse d)) :=
  h.response_continuous.comp
    (show Continuous (fun z : ℝ × ℝ =>
      (max (max 0 z.1) (max 0 z.2), min (max 0 z.1) (max 0 z.2))) by fun_prop)

theorem symmetricCorrelation_eq {d : CKData} {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    symmetricCorrelation d t s = d.C t s := by
  simp [symmetricCorrelation,max_eq_right ht,max_eq_right hs]

theorem symmetricResponse_eq {d : CKData} {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    symmetricResponse d t s = d.R t s := by
  simp [symmetricResponse,max_eq_right (hs.trans hst),max_eq_right hs,
    max_eq_left hst,min_eq_right hst]

theorem symmetricResponse_symmetric (d : CKData) (t s : ℝ) :
    symmetricResponse d t s = symmetricResponse d s t := by
  simp only [symmetricResponse,max_comm,min_comm]

@[expose] def comparisonSize (d e : CKData) (t s : ℝ) : ℝ :=
  max |symmetricCorrelation d t s - symmetricCorrelation e t s|
    |symmetricResponse d t s - symmetricResponse e t s|

@[expose] def comparisonNorm (d e : CKData) (t : ℝ) : ℝ := runningNorm (comparisonSize d e) t

theorem comparisonSize_continuous {d e : CKData}
    (hd : RegularData d) (he : RegularData e) :
    Continuous (Function.uncurry (comparisonSize d e)) :=
  ((symmetricCorrelation_continuous hd).sub (symmetricCorrelation_continuous he)).abs.max
    (((symmetricResponse_continuous hd).sub (symmetricResponse_continuous he)).abs)

theorem comparisonSize_nonneg (d e : CKData) (t s : ℝ) : 0 ≤ comparisonSize d e t s :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem comparisonNorm_continuous {d e : CKData}
    (hd : RegularData d) (he : RegularData e) : Continuous (comparisonNorm d e) :=
  runningNorm_continuous (comparisonSize_continuous hd he)

theorem comparisonNorm_nonneg {d e : CKData}
    (hd : RegularData d) (he : RegularData e) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ comparisonNorm d e t := runningNorm_nonneg (comparisonSize_continuous hd he) ht

theorem correlation_difference_le {d e : CKData}
    (hd : RegularData d) (he : RegularData e) {t u v : ℝ}
    (ht : 0 ≤ t) (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 t) :
    |d.C u v - e.C u v| ≤ comparisonNorm d e t := by
  have hh := runningNorm_dominate (comparisonSize_continuous hd he) ht hu hv
  rw [abs_of_nonneg (comparisonSize_nonneg d e u v)] at hh
  have hleft := (le_max_left _ _).trans hh
  simpa only [comparisonNorm,comparisonSize,symmetricCorrelation,max_eq_right hu.1,max_eq_right hv.1]
    using hleft

theorem response_difference_le {d e : CKData}
    (hd : RegularData d) (he : RegularData e) {t u v : ℝ}
    (ht : 0 ≤ t) (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 u) :
    |d.R u v - e.R u v| ≤ comparisonNorm d e t := by
  have hh := runningNorm_dominate (comparisonSize_continuous hd he) ht hu
    (show v ∈ Icc 0 t from ⟨hv.1,hv.2.trans hu.2⟩)
  rw [abs_of_nonneg (comparisonSize_nonneg d e u v)] at hh
  have hright := (le_max_right _ _).trans hh
  simpa only [comparisonNorm,comparisonSize,symmetricResponse,max_eq_right hu.1,max_eq_right hv.1,
    max_eq_left hv.2,min_eq_right hv.2] using hright


theorem power_response_integrable {d : CKData} (h : RegularData d) (n : ℕ) {a t : ℝ}
    (_ha : 0 ≤ a) (_hat : a ≤ t) :
    IntervalIntegrable (fun u => d.C t u^n*d.R t u) volume a t :=
  (((h.correlation_continuous.comp (continuous_const.prodMk continuous_id)).pow n).mul
    (h.response_continuous.comp (continuous_const.prodMk continuous_id))).intervalIntegrable a t

theorem response_memory_integrable {d : CKData} (h : RegularData d) (n : ℕ) {s t : ℝ}
    (_hs : 0 ≤ s) (_hst : s ≤ t) :
    IntervalIntegrable (fun u => d.C t u^n*d.R t u*d.R u s) volume s t :=
  ((((h.correlation_continuous.comp (continuous_const.prodMk continuous_id)).pow n).mul
    (h.response_continuous.comp (continuous_const.prodMk continuous_id))).mul
    (h.response_continuous.comp (continuous_id.prodMk continuous_const))).intervalIntegrable s t

theorem correlation_memory_integrable {d : CKData} (h : RegularData d) (n : ℕ) {s t : ℝ}
    (_hs : 0 ≤ s) (_ht : 0 ≤ t) :
    IntervalIntegrable (fun u => d.C t u^n*d.R t u*d.C u s) volume 0 t :=
  ((((h.correlation_continuous.comp (continuous_const.prodMk continuous_id)).pow n).mul
    (h.response_continuous.comp (continuous_const.prodMk continuous_id))).mul
    (h.correlation_continuous.comp (continuous_id.prodMk continuous_const))).intervalIntegrable 0 t

theorem forcing_memory_integrable {d : CKData} (h : RegularData d) (n : ℕ) {s t : ℝ}
    (_hs : 0 ≤ s) (_ht : 0 ≤ t) :
    IntervalIntegrable (fun u => d.C t u^n*d.R s u) volume 0 s :=
  (((h.correlation_continuous.comp (continuous_const.prodMk continuous_id)).pow n).mul
    (h.response_continuous.comp (continuous_const.prodMk continuous_id))).intervalIntegrable 0 s

theorem memoryMass_difference_le {p : ℕ} {d e : CKData}
    (hd : RegularData d) (he : RegularData e) {T M t : ℝ}
    (hM : CompactBounds d e T M) (ht : t ∈ Icc 0 T) :
    |memoryMass p d t-memoryMass p e t| ≤
      T*pairLip M (p-1)*comparisonNorm d e t := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.one_le
  have hδ := comparisonNorm_nonneg hd he ht.1
  have hi := interval_integral_difference_le ht.1
    (power_response_integrable hd (p-1) (le_refl 0) ht.1)
    (power_response_integrable he (p-1) (le_refl 0) ht.1)
    (fun u hu => power_product_difference_le hM0 hδ
      (hM.correlation_d t ht u ⟨hu.1,hu.2.trans ht.2⟩)
      (hM.correlation_e t ht u ⟨hu.1,hu.2.trans ht.2⟩)
      (hM.response_d t ht u hu) (hM.response_e t ht u hu)
      (correlation_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ hu)
      (response_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ hu) (p-1))
  change |memoryMass p d t-memoryMass p e t| ≤ (t-0)*(pairLip M (p-1)*comparisonNorm d e t) at hi
  exact hi.trans (by
    rw [sub_zero,mul_assoc]
    exact mul_le_mul_of_nonneg_right ht.2
      (mul_nonneg (pairLip_nonneg hM0 _) hδ))

theorem responseMemory_difference_le {d e : CKData}
    (hd : RegularData d) (he : RegularData e) {T M t s : ℝ}
    (hM : CompactBounds d e T M) (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) (n : ℕ) :
    |responseMemory n d t s-responseMemory n e t s| ≤
      T*tripleLip M n*comparisonNorm d e t := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.one_le
  have hδ := comparisonNorm_nonneg hd he ht.1
  have hi := interval_integral_difference_le hs.2
    (response_memory_integrable hd n hs.1 hs.2) (response_memory_integrable he n hs.1 hs.2)
    (fun u hu => power_triple_difference_le hM0 hδ
      (hM.correlation_d t ht u ⟨hs.1.trans hu.1,hu.2.trans ht.2⟩)
      (hM.correlation_e t ht u ⟨hs.1.trans hu.1,hu.2.trans ht.2⟩)
      (hM.response_d t ht u ⟨hs.1.trans hu.1,hu.2⟩)
      (hM.response_e t ht u ⟨hs.1.trans hu.1,hu.2⟩)
      (hM.response_d u ⟨hs.1.trans hu.1,hu.2.trans ht.2⟩ s ⟨hs.1,hu.1⟩)
      (hM.response_e u ⟨hs.1.trans hu.1,hu.2.trans ht.2⟩ s ⟨hs.1,hu.1⟩)
      (correlation_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ ⟨hs.1.trans hu.1,hu.2⟩)
      (response_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ ⟨hs.1.trans hu.1,hu.2⟩)
      (response_difference_le hd he ht.1 ⟨hs.1.trans hu.1,hu.2⟩ ⟨hs.1,hu.1⟩) n)
  change |responseMemory n d t s-responseMemory n e t s| ≤
    (t-s)*(tripleLip M n*comparisonNorm d e t) at hi
  exact hi.trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith [ht.2,hs.1])
      (mul_nonneg (tripleLip_nonneg hM0 _) hδ))

theorem correlationMemory_difference_le {d e : CKData}
    (hd : RegularData d) (he : RegularData e) {T M t s : ℝ}
    (hM : CompactBounds d e T M) (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) (n : ℕ) :
    |correlationMemory n d t s-correlationMemory n e t s| ≤
      T*tripleLip M n*comparisonNorm d e t := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.one_le
  have hδ := comparisonNorm_nonneg hd he ht.1
  have hi := interval_integral_difference_le ht.1
    (correlation_memory_integrable hd n hs.1 ht.1) (correlation_memory_integrable he n hs.1 ht.1)
    (fun u hu => power_triple_difference_le hM0 hδ
      (hM.correlation_d t ht u ⟨hu.1,hu.2.trans ht.2⟩)
      (hM.correlation_e t ht u ⟨hu.1,hu.2.trans ht.2⟩)
      (hM.response_d t ht u hu) (hM.response_e t ht u hu)
      (hM.correlation_d u ⟨hu.1,hu.2.trans ht.2⟩ s ⟨hs.1,hs.2.trans ht.2⟩)
      (hM.correlation_e u ⟨hu.1,hu.2.trans ht.2⟩ s ⟨hs.1,hs.2.trans ht.2⟩)
      (correlation_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ hu)
      (response_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ hu)
      (correlation_difference_le hd he ht.1 hu hs) n)
  change |correlationMemory n d t s-correlationMemory n e t s| ≤
    (t-0)*(tripleLip M n*comparisonNorm d e t) at hi
  exact hi.trans (by
    rw [sub_zero,mul_assoc]
    exact mul_le_mul_of_nonneg_right ht.2 (mul_nonneg (tripleLip_nonneg hM0 _) hδ))

theorem forcingMemory_difference_le {d e : CKData}
    (hd : RegularData d) (he : RegularData e) {T M t s : ℝ}
    (hM : CompactBounds d e T M) (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) (n : ℕ) :
    |forcingMemory n d t s-forcingMemory n e t s| ≤
      T*pairLip M n*comparisonNorm d e t := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.one_le
  have hδ := comparisonNorm_nonneg hd he ht.1
  have hi := interval_integral_difference_le hs.1
    (forcing_memory_integrable hd n hs.1 ht.1) (forcing_memory_integrable he n hs.1 ht.1)
    (fun u hu => power_product_difference_le hM0 hδ
      (hM.correlation_d t ht u ⟨hu.1,hu.2.trans (hs.2.trans ht.2)⟩)
      (hM.correlation_e t ht u ⟨hu.1,hu.2.trans (hs.2.trans ht.2)⟩)
      (hM.response_d s ⟨hs.1,hs.2.trans ht.2⟩ u hu)
      (hM.response_e s ⟨hs.1,hs.2.trans ht.2⟩ u hu)
      (correlation_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ ⟨hu.1,hu.2.trans hs.2⟩)
      (response_difference_le hd he ht.1 hs hu) n)
  change |forcingMemory n d t s-forcingMemory n e t s| ≤
    (s-0)*(pairLip M n*comparisonNorm d e t) at hi
  exact hi.trans (by
    rw [sub_zero,mul_assoc]
    exact mul_le_mul_of_nonneg_right (hs.2.trans ht.2) (mul_nonneg (pairLip_nonneg hM0 _) hδ))


/-- The actual integral defects, not derivatives of an approximate process. -/
@[expose] def correlationDefect (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) :=
  d.C t s-d.C s s-∫ u in s..t,correlationSlope p β d u s

@[expose] def responseDefect (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) :=
  d.R t s-d.R s s-∫ u in s..t,responseSlope p β d u s

@[expose] def multiplierDefect (p : ℕ) (β : ℝ) (d : CKData) (t : ℝ) :=
  d.multiplier t-(1+β^2*(p : ℝ)^2*memoryMass p d t)

structure ResidualBounds (p : ℕ) (β T : ℝ) (d : CKData) (ε : ℝ) : Prop where
  error_nonnegative : 0 ≤ ε
  correlation_diagonal : ∀ s ∈ Icc 0 T,|d.C s s-1| ≤ ε
  response_diagonal : ∀ s ∈ Icc 0 T,|d.R s s-1| ≤ ε
  correlation_integral : ∀ t ∈ Icc 0 T,∀ s ∈ Icc 0 t,|correlationDefect p β d t s| ≤ ε
  response_integral : ∀ t ∈ Icc 0 T,∀ s ∈ Icc 0 t,|responseDefect p β d t s| ≤ ε
  multiplier_integral : ∀ t ∈ Icc 0 T,|multiplierDefect p β d t| ≤ ε

@[expose] def stabilitySlopeConstant (p : ℕ) (β T M : ℝ) :=
  M+(β^2*(p : ℝ)^2*T*pairLip M (p-1))*M+
    (β^2*((p : ℝ)*((p : ℝ)-1)))*T*tripleLip M (p-2)+
    (β^2*(p : ℝ))*T*pairLip M (p-1)

theorem multiplier_difference_le {p : ℕ} {β T M εd εe : ℝ} {d e : CKData}
    (hd : RegularData d) (he : RegularData e) (hM : CompactBounds d e T M)
    (hFd : ResidualBounds p β T d εd) (hFe : ResidualBounds p β T e εe)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    |d.multiplier t-e.multiplier t| ≤ εd+εe+
      (β^2*(p : ℝ)^2*T*pairLip M (p-1))*comparisonNorm d e t := by
  have heq : d.multiplier t-e.multiplier t=
      (multiplierDefect p β d t-multiplierDefect p β e t)+
        (β^2*(p : ℝ)^2)*(memoryMass p d t-memoryMass p e t) := by
    unfold multiplierDefect
    ring
  have hres : |multiplierDefect p β d t-multiplierDefect p β e t| ≤ εd+εe :=
    (abs_sub _ _).trans (add_le_add (hFd.multiplier_integral t ht) (hFe.multiplier_integral t ht))
  have hmem := mul_le_mul_of_nonneg_left (memoryMass_difference_le (p := p) hd he hM ht)
    (mul_nonneg (sq_nonneg β) (sq_nonneg (p : ℝ)))
  rw [heq]
  have htriangle := abs_add_le (multiplierDefect p β d t-multiplierDefect p β e t)
    ((β^2*(p : ℝ)^2)*(memoryMass p d t-memoryMass p e t))
  rw [abs_mul,abs_of_nonneg (mul_nonneg (sq_nonneg β) (sq_nonneg (p : ℝ)))] at htriangle
  nlinarith only [hres,hmem,htriangle]

theorem damping_difference_le {M L δ η lam mu a b : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hlam : |lam| ≤ M) (hb : |b| ≤ M)
    (hab : |a-b| ≤ δ) (hlammu : |lam-mu| ≤ η+L*δ) :
    |(-lam*a)-(-mu*b)| ≤ M*η+(M+L*M)*δ := by
  have heq : (-lam*a)-(-mu*b) = -lam*(a-b)-(lam-mu)*b := by ring
  rw [heq]
  calc
    _ ≤ |-lam*(a-b)|+|(lam-mu)*b| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (-lam*(a-b)) ((lam-mu)*b)
    _ ≤ M*δ+(η+L*δ)*M := by
      simp only [abs_mul,abs_neg]
      exact add_le_add (mul_le_mul hlam hab (abs_nonneg _) hM)
        (mul_le_mul hlammu hb (abs_nonneg _) (add_nonneg hη (mul_nonneg hL hδ)))
    _ = _ := by ring

/-- True nonlinear slope stability, with explicit additive multiplier defect. -/
theorem slope_difference_bounds {p : ℕ} {β T M εd εe : ℝ} {d e : CKData}
    (hd : RegularData d) (he : RegularData e) (hp : 3 ≤ p) (hT : 0 ≤ T)
    (hM : CompactBounds d e T M)
    (hFd : ResidualBounds p β T d εd) (hFe : ResidualBounds p β T e εe) :
    0 ≤ stabilitySlopeConstant p β T M ∧
      (∀ t ∈ Icc 0 T,∀ s ∈ Icc 0 t,
        |correlationSlope p β d t s-correlationSlope p β e t s| ≤
          M*(εd+εe)+stabilitySlopeConstant p β T M*comparisonNorm d e t) ∧
      (∀ t ∈ Icc 0 T,∀ s ∈ Icc 0 t,
        |responseSlope p β d t s-responseSlope p β e t s| ≤
          M*(εd+εe)+stabilitySlopeConstant p β T M*comparisonNorm d e t) := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.one_le
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hp1 : (1 : ℝ) ≤ p := by
    have hp := hp
    exact_mod_cast (show 1 ≤ p by omega)
  let L : ℝ := β ^ 2*(p : ℝ)^2*T*pairLip M (p-1)
  let A : ℝ := M+L*M
  let c : ℝ := β ^ 2*((p : ℝ)*((p : ℝ)-1))
  let k : ℝ := β ^ 2*(p : ℝ)
  let U : ℝ := c*T*tripleLip M (p-2)
  let V : ℝ := k*T*pairLip M (p-1)
  let B : ℝ := A+U+V
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg
    (mul_nonneg (sq_nonneg β) (sq_nonneg (p : ℝ))) hT) (pairLip_nonneg hM0 _)
  have hA : 0 ≤ A := add_nonneg hM0 (mul_nonneg hL hM0)
  have hc : 0 ≤ c := mul_nonneg (sq_nonneg β) (mul_nonneg hp0 (sub_nonneg.mpr hp1))
  have hk : 0 ≤ k := mul_nonneg (sq_nonneg β) hp0
  have hU : 0 ≤ U := mul_nonneg (mul_nonneg hc hT) (tripleLip_nonneg hM0 _)
  have hV : 0 ≤ V := mul_nonneg (mul_nonneg hk hT) (pairLip_nonneg hM0 _)
  have hdampC {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
      |(-d.multiplier t*d.C t s)-(-e.multiplier t*e.C t s)| ≤ M*(εd+εe)+A*comparisonNorm d e t :=
    damping_difference_le hM0 hL (comparisonNorm_nonneg hd he ht.1)
      (add_nonneg hFd.error_nonnegative hFe.error_nonnegative)
      (hM.multiplier_d t ht) (hM.correlation_e t ht s ⟨hs.1,hs.2.trans ht.2⟩)
      (correlation_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ hs)
      (multiplier_difference_le hd he hM hFd hFe ht)
  have hdampR {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
      |(-d.multiplier t*d.R t s)-(-e.multiplier t*e.R t s)| ≤ M*(εd+εe)+A*comparisonNorm d e t :=
    damping_difference_le hM0 hL (comparisonNorm_nonneg hd he ht.1)
      (add_nonneg hFd.error_nonnegative hFe.error_nonnegative)
      (hM.multiplier_d t ht) (hM.response_e t ht s hs)
      (response_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ hs)
      (multiplier_difference_le hd he hM hFd hFe ht)
  have hmemC {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
      |c*(correlationMemory (p-2) d t s-correlationMemory (p-2) e t s)| ≤
        U*comparisonNorm d e t := by
    rw [abs_mul,abs_of_nonneg hc]
    have hh := mul_le_mul_of_nonneg_left (correlationMemory_difference_le hd he hM ht hs (p-2)) hc
    simpa only [U,mul_assoc] using hh
  have hmemR {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
      |c*(responseMemory (p-2) d t s-responseMemory (p-2) e t s)| ≤
        U*comparisonNorm d e t := by
    rw [abs_mul,abs_of_nonneg hc]
    have hh := mul_le_mul_of_nonneg_left (responseMemory_difference_le hd he hM ht hs (p-2)) hc
    simpa only [U,mul_assoc] using hh
  have hforce {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
      |k*(forcingMemory (p-1) d t s-forcingMemory (p-1) e t s)| ≤
        V*comparisonNorm d e t := by
    rw [abs_mul,abs_of_nonneg hk]
    have hh := mul_le_mul_of_nonneg_left (forcingMemory_difference_le hd he hM ht hs (p-1)) hk
    simpa only [V,mul_assoc] using hh
  change 0 ≤ B ∧ _
  refine ⟨add_nonneg (add_nonneg hA hU) hV,?_,?_⟩
  · intro t ht s hs
    have heq : correlationSlope p β d t s-correlationSlope p β e t s =
        ((-d.multiplier t*d.C t s)-(-e.multiplier t*e.C t s))+
        c*(correlationMemory (p-2) d t s-correlationMemory (p-2) e t s)+
        k*(forcingMemory (p-1) d t s-forcingMemory (p-1) e t s) := by
      rw [correlationSlope_normalized,correlationSlope_normalized]
      dsimp only [c,k]
      ring
    rw [heq]
    calc
      _ ≤ |(-d.multiplier t*d.C t s)-(-e.multiplier t*e.C t s)|+
          |c*(correlationMemory (p-2) d t s-correlationMemory (p-2) e t s)|+
          |k*(forcingMemory (p-1) d t s-forcingMemory (p-1) e t s)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ M*(εd+εe)+A*comparisonNorm d e t+U*comparisonNorm d e t+V*comparisonNorm d e t :=
        add_le_add (add_le_add (hdampC ht hs) (hmemC ht hs)) (hforce ht hs)
      _ = M*(εd+εe)+B*comparisonNorm d e t := by dsimp only [B]; ring
  · intro t ht s hs
    have heq : responseSlope p β d t s-responseSlope p β e t s =
        ((-d.multiplier t*d.R t s)-(-e.multiplier t*e.R t s))+
        c*(responseMemory (p-2) d t s-responseMemory (p-2) e t s) := by
      rw [responseSlope_normalized,responseSlope_normalized]
      dsimp only [c]
      ring
    rw [heq]
    calc
      _ ≤ |(-d.multiplier t*d.R t s)-(-e.multiplier t*e.R t s)|+
          |c*(responseMemory (p-2) d t s-responseMemory (p-2) e t s)| := abs_add_le _ _
      _ ≤ M*(εd+εe)+A*comparisonNorm d e t+U*comparisonNorm d e t :=
        add_le_add (hdampR ht hs) (hmemR ht hs)
      _ ≤ M*(εd+εe)+B*comparisonNorm d e t := by
        have hh := mul_nonneg hV (comparisonNorm_nonneg hd he ht.1)
        dsimp only [B]
        nlinarith only [hh]


theorem responseSlope_continuous {d : CKData} (h : RegularData d) (p : ℕ) (β : ℝ) :
    Continuous (Function.uncurry (responseSlope p β d)) := by
  have hmem : Continuous (Function.uncurry (responseMemory (p-2) d)) := by
    apply BackwardResponse.continuous_integral_endpoints
    · exact ((((h.correlation_continuous.comp (continuous_fst.fst.prodMk continuous_snd)).pow (p-2)).mul
        (h.response_continuous.comp (continuous_fst.fst.prodMk continuous_snd))).mul
        (h.response_continuous.comp (continuous_snd.prodMk continuous_fst.snd)))
    · exact continuous_snd
    · exact continuous_fst
  change Continuous (fun z : ℝ × ℝ => responseSlope p β d z.1 z.2)
  simp_rw [responseSlope_normalized]
  exact ((h.multiplier_continuous.comp continuous_fst).neg.mul h.response_continuous).add
    (hmem.const_mul (β^2*((p : ℝ)*((p : ℝ)-1))))

theorem correlationSlope_continuous {d : CKData} (h : RegularData d) (p : ℕ) (β : ℝ) :
    Continuous (Function.uncurry (correlationSlope p β d)) := by
  have hmem : Continuous (Function.uncurry (correlationMemory (p-2) d)) := by
    apply BackwardResponse.continuous_integral_endpoints
    · exact ((((h.correlation_continuous.comp (continuous_fst.fst.prodMk continuous_snd)).pow (p-2)).mul
        (h.response_continuous.comp (continuous_fst.fst.prodMk continuous_snd))).mul
        (h.correlation_continuous.comp (continuous_snd.prodMk continuous_fst.snd)))
    · exact continuous_const
    · exact continuous_fst
  have hforce : Continuous (Function.uncurry (forcingMemory (p-1) d)) := by
    apply BackwardResponse.continuous_integral_endpoints
    · exact (((h.correlation_continuous.comp (continuous_fst.fst.prodMk continuous_snd)).pow (p-1)).mul
        (h.response_continuous.comp (continuous_fst.snd.prodMk continuous_snd)))
    · exact continuous_const
    · exact continuous_snd
  change Continuous (fun z : ℝ × ℝ => correlationSlope p β d z.1 z.2)
  simp_rw [correlationSlope_normalized]
  exact (((h.multiplier_continuous.comp continuous_fst).neg.mul h.correlation_continuous).add
    (hmem.const_mul (β^2*((p : ℝ)*((p : ℝ)-1))))).add (hforce.const_mul (β^2*(p : ℝ)))

/-- Actual finite-horizon CK equations have zero integral defects, including
closed horizon endpoints, by the genuine fundamental theorem of calculus. -/
theorem residualBounds_of_equations {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) : ResidualBounds p β T d 0 := by
  refine ⟨le_refl 0,?_,?_,?_,?_,?_⟩
  · intro s hs
    rw [h.correlation_diagonal s hs]
    simp
  · intro s hs
    rw [h.response_diagonal s hs]
    simp
  · intro t ht s hs
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.2
      ((h.correlation_continuous.comp (continuous_id.prodMk continuous_const)).continuousOn)
      (f' := fun u => correlationSlope p β d u s)
      (fun u hu => (h.correlation_derivative u ⟨hs.1.trans hu.1.le,hu.2.le.trans ht.2⟩
        s ⟨hs.1,hu.1.le⟩).hasDerivAt (Icc_mem_nhds hu.1 (hu.2.trans_le ht.2)))
      ((h.correlation_slope_continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable s t)
    change (∫ u in s..t,correlationSlope p β d u s)=d.C t s-d.C s s at hi
    simp only [correlationDefect,hi,sub_self,abs_zero]
    exact le_refl 0
  · intro t ht s hs
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.2
      ((h.response_continuous.comp (continuous_id.prodMk continuous_const)).continuousOn)
      (f' := fun u => responseSlope p β d u s)
      (fun u hu => (h.response_derivative u ⟨hs.1.trans hu.1.le,hu.2.le.trans ht.2⟩
        s ⟨hs.1,hu.1.le⟩).hasDerivAt (Icc_mem_nhds hu.1 (hu.2.trans_le ht.2)))
      ((h.response_slope_continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable s t)
    change (∫ u in s..t,responseSlope p β d u s)=d.R t s-d.R s s at hi
    simp only [responseDefect,hi,sub_self,abs_zero]
    exact le_refl 0
  · intro t ht
    simp only [multiplierDefect,h.multiplier_eq t ht,sub_self,abs_zero]
    exact le_refl 0

/-- Nonzero-source integral Gronwall, proved from an actual primitive. -/
theorem continuous_integral_gronwall {w : ℝ → ℝ} {T A B : ℝ}
    (hw : Continuous w) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc 0 T,w t ≤ A+B*∫ u in (0 : ℝ)..t,w u) :
    ∀ t ∈ Icc 0 T,w t ≤ A*Real.exp (B*t) := by
  let F : ℝ → ℝ := fun t => A+B*∫ u in (0 : ℝ)..t,w u
  have hderiv (t : ℝ) : HasDerivAt F (B*w t) t := by
    simpa only [mul_comm] using
      (intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable (μ := volume) 0 t)
        hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt).const_mul B |>.const_add A
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun t => (hderiv t).continuousAt)
  have hg := le_gronwallBound_of_liminf_deriv_right_le (f := F) (f' := fun t => B*w t)
    (δ := A) (K := B) (ε := 0) hc.continuousOn
    (fun t _ r hr => (hderiv t).hasDerivWithinAt.liminf_right_slope_le hr)
    (show F 0 ≤ A by simp [F])
    (fun t ht => by
      simpa only [add_zero] using mul_le_mul_of_nonneg_left (hbound t ⟨ht.1,ht.2.le⟩) hB)
  intro t ht
  have hh := hg t ht
  rw [gronwallBound_ε0,sub_zero] at hh
  exact (hbound t ht).trans hh

theorem integral_difference_variable_bound {f g b : ℝ → ℝ} {a t : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hb : Continuous b) (hat : a ≤ t)
    (hbound : ∀ u ∈ Icc a t,|f u-g u| ≤ b u) :
    |(∫ u in a..t,f u)-(∫ u in a..t,g u)| ≤ ∫ u in a..t,b u := by
  rw [←intervalIntegral.integral_sub (hf.intervalIntegrable a t) (hg.intervalIntegrable a t)]
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun u => f u-g u) hat
  have hm := intervalIntegral.integral_mono_on hat
    ((hf.sub hg).norm.intervalIntegrable (μ := volume) a t) (hb.intervalIntegrable a t)
    (fun u hu => by simpa only [Real.norm_eq_abs,Pi.sub_apply] using hbound u hu)
  simpa only [Real.norm_eq_abs] using hn.trans hm

/-- An integral row with small diagonal and equation defects remains close
without requiring differentiability of either approximate row. -/
theorem row_difference_bound {f g fd gd w : ℝ → ℝ} {T M B η t s : ℝ}
    (hfd : Continuous fd) (hgd : Continuous gd) (hw : Continuous w)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (hwn : ∀ u,0 ≤ u → 0 ≤ w u)
    (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t)
    (hdiag : |f s-g s| ≤ η)
    (hdef : |(f t-f s-∫ u in s..t,fd u)-(g t-g s-∫ u in s..t,gd u)| ≤ η)
    (hslopes : ∀ u ∈ Icc s t,|fd u-gd u| ≤ M*η+B*w u) :
    |f t-g t| ≤ (2+M*T)*η+B*∫ u in (0 : ℝ)..t,w u := by
  have hi := integral_difference_variable_bound hfd hgd
    (continuous_const.add (hw.const_mul B)) hs.2 hslopes
  change |(∫ u in s..t,fd u)-(∫ u in s..t,gd u)| ≤ ∫ u in s..t,M*η+B*w u at hi
  have heq : f t-g t=(f s-g s)+
      ((∫ u in s..t,fd u)-(∫ u in s..t,gd u))+
      ((f t-f s-∫ u in s..t,fd u)-(g t-g s-∫ u in s..t,gd u)) := by ring
  have htriangle := (abs_add_le
    ((f s-g s)+((∫ u in s..t,fd u)-(∫ u in s..t,gd u)))
    ((f t-f s-∫ u in s..t,fd u)-(g t-g s-∫ u in s..t,gd u))).trans
      (add_le_add (abs_add_le (f s-g s) ((∫ u in s..t,fd u)-(∫ u in s..t,gd u))) le_rfl)
  rw [←heq] at htriangle
  have hbound : |f t-g t| ≤ 2*η+∫ u in s..t,M*η+B*w u := by linarith only [htriangle,hdiag,hdef,hi]
  have hint : (∫ u in s..t,M*η+B*w u)=(t-s)*(M*η)+B*∫ u in s..t,w u := by
    rw [intervalIntegral.integral_add (f := fun _ => M*η) (g := fun u => B*w u)
      (intervalIntegrable_const) ((hw.const_mul B).intervalIntegrable s t),
      intervalIntegral.integral_const,smul_eq_mul,intervalIntegral.integral_const_mul]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hw.intervalIntegrable (μ := volume) 0 s) (hw.intervalIntegrable s t)
  have hnon : 0 ≤ ∫ u in (0 : ℝ)..s,w u :=
    intervalIntegral.integral_nonneg hs.1 (fun u hu => hwn u hu.1)
  have hinc : (∫ u in s..t,w u) ≤ ∫ u in (0 : ℝ)..t,w u := by linarith only [hsplit,hnon]
  have htime : (t-s)*(M*η) ≤ T*(M*η) :=
    mul_le_mul_of_nonneg_right (by linarith [ht.2,hs.1]) (mul_nonneg hM hη)
  have hiB := mul_le_mul_of_nonneg_left hinc hB
  rw [hint] at hbound
  nlinarith only [hbound,htime,hiB]

theorem causal_row_bounds {p : ℕ} {β T M εd εe : ℝ} {d e : CKData}
    (hd : RegularData d) (he : RegularData e) (hp : 3 ≤ p) (hT : 0 ≤ T)
    (hM : CompactBounds d e T M)
    (hFd : ResidualBounds p β T d εd) (hFe : ResidualBounds p β T e εe) :
    (∀ t ∈ Icc 0 T,∀ s ∈ Icc 0 t,
      |d.C t s-e.C t s| ≤ (2+M*T)*(εd+εe)+
        stabilitySlopeConstant p β T M*∫ u in (0 : ℝ)..t,comparisonNorm d e u) ∧
    (∀ t ∈ Icc 0 T,∀ s ∈ Icc 0 t,
      |d.R t s-e.R t s| ≤ (2+M*T)*(εd+εe)+
        stabilitySlopeConstant p β T M*∫ u in (0 : ℝ)..t,comparisonNorm d e u) := by
  obtain ⟨hB,hC,hR⟩ := slope_difference_bounds hd he hp hT hM hFd hFe
  have hM0 : 0 ≤ M := zero_le_one.trans hM.one_le
  have hη := add_nonneg hFd.error_nonnegative hFe.error_nonnegative
  have hw := comparisonNorm_continuous hd he
  have hwn : ∀ u : ℝ,0 ≤ u → 0 ≤ comparisonNorm d e u :=
    fun _ hu => comparisonNorm_nonneg hd he hu
  constructor
  · intro t ht s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
    apply row_difference_bound
      ((correlationSlope_continuous hd p β).comp (continuous_id.prodMk continuous_const))
      ((correlationSlope_continuous he p β).comp (continuous_id.prodMk continuous_const))
      hw hM0 hB hη hwn ht hs
    · have heq : d.C s s-e.C s s=(d.C s s-1)-(e.C s s-1) := by ring
      rw [heq]
      exact (abs_sub _ _).trans
        (add_le_add (hFd.correlation_diagonal s hsT) (hFe.correlation_diagonal s hsT))
    · change |correlationDefect p β d t s-correlationDefect p β e t s| ≤ εd+εe
      exact (abs_sub _ _).trans
        (add_le_add (hFd.correlation_integral t ht s hs) (hFe.correlation_integral t ht s hs))
    · intro u hu
      exact hC u ⟨hs.1.trans hu.1,hu.2.trans ht.2⟩ s ⟨hs.1,hu.1⟩
  · intro t ht s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
    apply row_difference_bound
      ((responseSlope_continuous hd p β).comp (continuous_id.prodMk continuous_const))
      ((responseSlope_continuous he p β).comp (continuous_id.prodMk continuous_const))
      hw hM0 hB hη hwn ht hs
    · have heq : d.R s s-e.R s s=(d.R s s-1)-(e.R s s-1) := by ring
      rw [heq]
      exact (abs_sub _ _).trans
        (add_le_add (hFd.response_diagonal s hsT) (hFe.response_diagonal s hsT))
    · change |responseDefect p β d t s-responseDefect p β e t s| ≤ εd+εe
      exact (abs_sub _ _).trans
        (add_le_add (hFd.response_integral t ht s hs) (hFe.response_integral t ht s hs))
    · intro u hu
      exact hR u ⟨hs.1.trans hu.1,hu.2.trans ht.2⟩ s ⟨hs.1,hu.1⟩

theorem comparisonNorm_integral_bound {p : ℕ} {β T M εd εe : ℝ} {d e : CKData}
    (hd : RegularData d) (he : RegularData e) (hp : 3 ≤ p) (hT : 0 ≤ T)
    (hM : CompactBounds d e T M)
    (hFd : ResidualBounds p β T d εd) (hFe : ResidualBounds p β T e εe) :
    ∀ t ∈ Icc 0 T,comparisonNorm d e t ≤ (2+M*T)*(εd+εe)+
      stabilitySlopeConstant p β T M*∫ u in (0 : ℝ)..t,comparisonNorm d e u := by
  obtain ⟨hC,hR⟩ := causal_row_bounds hd he hp hT hM hFd hFe
  have hB := (slope_difference_bounds hd he hp hT hM hFd hFe).1
  have hw := comparisonNorm_continuous hd he
  have hinc {t r : ℝ} (ht : t ∈ Icc 0 T) (hr : r ∈ Icc 0 t) :
      stabilitySlopeConstant p β T M*(∫ u in (0 : ℝ)..r,comparisonNorm d e u) ≤
        stabilitySlopeConstant p β T M*∫ u in (0 : ℝ)..t,comparisonNorm d e u := by
    apply mul_le_mul_of_nonneg_left _ hB
    have hspl := intervalIntegral.integral_add_adjacent_intervals
      (hw.intervalIntegrable (μ := volume) 0 r) (hw.intervalIntegrable r t)
    have hn := intervalIntegral.integral_nonneg (μ := volume) hr.2
      (fun u hu => comparisonNorm_nonneg hd he (hr.1.trans hu.1))
    linarith only [hspl,hn]
  have hpair {t u v : ℝ} (ht : t ∈ Icc 0 T)
      (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 t) :
      comparisonSize d e u v ≤ (2+M*T)*(εd+εe)+
        stabilitySlopeConstant p β T M*∫ x in (0 : ℝ)..t,comparisonNorm d e x := by
    unfold comparisonSize
    rw [symmetricCorrelation_eq hu.1 hv.1,symmetricCorrelation_eq hu.1 hv.1]
    by_cases huv : v ≤ u
    · rw [symmetricResponse_eq hv.1 huv,symmetricResponse_eq hv.1 huv]
      exact max_le ((hC u ⟨hu.1,hu.2.trans ht.2⟩ v ⟨hv.1,huv⟩).trans
        (add_le_add le_rfl (hinc ht hu)))
        ((hR u ⟨hu.1,hu.2.trans ht.2⟩ v ⟨hv.1,huv⟩).trans
          (add_le_add le_rfl (hinc ht hu)))
    · have huv' : u ≤ v := le_of_not_ge huv
      rw [hd.correlation_symmetric u v hu.1 hv.1,he.correlation_symmetric u v hu.1 hv.1,
        symmetricResponse_symmetric d u v,symmetricResponse_symmetric e u v,
        symmetricResponse_eq hu.1 huv',symmetricResponse_eq hu.1 huv']
      exact max_le ((hC v ⟨hv.1,hv.2.trans ht.2⟩ u ⟨hu.1,huv'⟩).trans
        (add_le_add le_rfl (hinc ht hv)))
        ((hR v ⟨hv.1,hv.2.trans ht.2⟩ u ⟨hu.1,huv'⟩).trans
          (add_le_add le_rfl (hinc ht hv)))
  intro t ht
  apply csSup_le (unitSquare_nonempty.image _)
  rintro _ ⟨z,hz,rfl⟩
  dsimp only
  rw [abs_of_nonneg (comparisonSize_nonneg d e _ _)]
  exact hpair ht ⟨mul_nonneg ht.1 hz.1.1,
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.1.2 ht.1⟩
    ⟨mul_nonneg ht.1 hz.2.1,
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2.2 ht.1⟩

/-- Explicit uniform amplification of equation and diagonal defects. -/
@[expose] def stabilityFactor (p : ℕ) (β T M : ℝ) :=
  (2+M*T)*Real.exp (stabilitySlopeConstant p β T M*T)

@[expose] def multiplierStabilityFactor (p : ℕ) (β T M : ℝ) :=
  1+(β^2*(p : ℝ)^2*T*pairLip M (p-1))*stabilityFactor p β T M

/-- Uniform stability for two approximate integral CK systems. -/
theorem approximate_ck_stability {p : ℕ} {β T M εd εe : ℝ} {d e : CKData}
    (hd : RegularData d) (he : RegularData e) (hp : 3 ≤ p) (hT : 0 ≤ T)
    (hM : CompactBounds d e T M)
    (hFd : ResidualBounds p β T d εd) (hFe : ResidualBounds p β T e εe) :
    (∀ t ∈ Icc 0 T,∀ s ∈ Icc 0 T,
      |d.C t s-e.C t s| ≤ stabilityFactor p β T M*(εd+εe)) ∧
    (∀ t ∈ Icc 0 T,∀ s ∈ Icc 0 t,
      |d.R t s-e.R t s| ≤ stabilityFactor p β T M*(εd+εe)) ∧
    (∀ t ∈ Icc 0 T,
      |d.multiplier t-e.multiplier t| ≤ multiplierStabilityFactor p β T M*(εd+εe)) := by
  have hB := (slope_difference_bounds hd he hp hT hM hFd hFe).1
  have hn := continuous_integral_gronwall (comparisonNorm_continuous hd he) hB
    (comparisonNorm_integral_bound hd he hp hT hM hFd hFe)
  have hnorm : comparisonNorm d e T ≤ stabilityFactor p β T M*(εd+εe) := by
    have hh := hn T ⟨hT,le_refl T⟩
    dsimp only [stabilityFactor]
    nlinarith only [hh]
  have hL : 0 ≤ β^2*(p : ℝ)^2*T*pairLip M (p-1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg β) (sq_nonneg (p : ℝ))) hT)
      (pairLip_nonneg (zero_le_one.trans hM.one_le) _)
  refine ⟨?_,?_,?_⟩
  · intro t ht s hs
    exact (correlation_difference_le hd he hT ht hs).trans hnorm
  · intro t ht s hs
    exact (response_difference_le hd he hT ht hs).trans hnorm
  · intro t ht
    have hnt : comparisonNorm d e t ≤ comparisonNorm d e T := by
      apply csSup_le (unitSquare_nonempty.image _)
      rintro _ ⟨z,hz,rfl⟩
      dsimp only
      exact runningNorm_dominate (comparisonSize_continuous hd he) hT
        ⟨mul_nonneg ht.1 hz.1.1, (by
          have hh := mul_le_mul_of_nonneg_left hz.1.2 ht.1
          simp only [mul_one] at hh
          exact hh.trans ht.2)⟩
        ⟨mul_nonneg ht.1 hz.2.1, (by
          have hh := mul_le_mul_of_nonneg_left hz.2.2 ht.1
          simp only [mul_one] at hh
          exact hh.trans ht.2)⟩
    have hh := (multiplier_difference_le hd he hM hFd hFe ht).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hnt.trans hnorm) hL))
    dsimp only [multiplierStabilityFactor]
    nlinarith only [hh]

/-- Approximate integral systems converge quantitatively to the actual CK
solution once their actual defects are bounded. -/
theorem approximate_ck_error_bound {p : ℕ} {β T M ε : ℝ} {d e : CKData}
    (hd : RegularData d) (he : CKOnHorizon p β T e)
    (hM : CompactBounds d e T M) (hFd : ResidualBounds p β T d ε) :
    (∀ t ∈ Icc 0 T,∀ s ∈ Icc 0 T,|d.C t s-e.C t s| ≤ stabilityFactor p β T M*ε) ∧
    (∀ t ∈ Icc 0 T,∀ s ∈ Icc 0 t,|d.R t s-e.R t s| ≤ stabilityFactor p β T M*ε) ∧
    (∀ t ∈ Icc 0 T,|d.multiplier t-e.multiplier t| ≤ multiplierStabilityFactor p β T M*ε) := by
  simpa only [add_zero] using approximate_ck_stability hd (regularData_of_equations he)
    he.spin_ge_three he.horizon_pos.le hM hFd (residualBounds_of_equations he)

theorem stabilityFactor_positive {p : ℕ} {β T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) :
    0 < stabilityFactor p β T M := by
  unfold stabilityFactor
  have hh := mul_nonneg hM hT
  exact mul_pos (by linarith) (Real.exp_pos _)

theorem multiplierStabilityFactor_positive {p : ℕ} {β T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) :
    0 < multiplierStabilityFactor p β T M := by
  have hL : 0 ≤ β^2*(p : ℝ)^2*T*pairLip M (p-1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg β) (sq_nonneg (p : ℝ))) hT) (pairLip_nonneg hM _)
  have hh := mul_nonneg hL (stabilityFactor_positive (p := p) (β := β) hT hM).le
  unfold multiplierStabilityFactor
  linarith

theorem uniform_convergence_of_error_bound {X : Type} {f : ℕ → X → ℝ} {g : X → ℝ}
    {s : Set X} {ε : ℕ → ℝ} {K : ℝ} (hK : 0 < K)
    (hε : Tendsto ε atTop (nhds 0))
    (hbound : ∀ n : ℕ,∀ x ∈ s,|f n x-g x| ≤ K*ε n) :
    TendstoUniformlyOn f g atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hevent := hε.eventually (Iio_mem_nhds (div_pos hδ hK))
  filter_upwards [hevent] with n hn x hx
  have hm : K*ε n < δ := by
    have hh := (lt_div_iff₀ hK).mp hn
    nlinarith only [hh]
  rw [Real.dist_eq,abs_sub_comm]
  exact (hbound n x hx).trans_lt hm

/-- Actual uniform finite-horizon convergence of continuous approximate
systems follows from vanishing integral defects and a common compact bound. -/
theorem approximate_ck_converges {p : ℕ} {β T M : ℝ} {d : ℕ → CKData} {e : CKData}
    {ε : ℕ → ℝ} (he : CKOnHorizon p β T e)
    (hd : ∀ n,RegularData (d n)) (hM : ∀ n,CompactBounds (d n) e T M)
    (hFd : ∀ n,ResidualBounds p β T (d n) (ε n)) (hε : Tendsto ε atTop (nhds 0)) :
    TendstoUniformlyOn (fun n => Function.uncurry (d n).C) (Function.uncurry e.C)
      atTop (Icc 0 T ×ˢ Icc 0 T) ∧
    TendstoUniformlyOn (fun n => Function.uncurry (d n).R) (Function.uncurry e.R)
      atTop {z : ℝ × ℝ | z.1 ∈ Icc 0 T ∧ z.2 ∈ Icc 0 z.1} ∧
    TendstoUniformlyOn (fun n => (d n).multiplier) e.multiplier atTop (Icc 0 T) := by
  have hM0 := zero_le_one.trans (hM 0).one_le
  have hK := stabilityFactor_positive (p := p) (β := β) he.horizon_pos.le hM0
  have hLamK := multiplierStabilityFactor_positive (p := p) (β := β) he.horizon_pos.le hM0
  have hbounds (n : ℕ) := approximate_ck_error_bound (hd n) he (hM n) (hFd n)
  refine ⟨?_,?_,?_⟩
  · apply uniform_convergence_of_error_bound hK hε
    intro n z hz
    exact (hbounds n).1 z.1 hz.1 z.2 hz.2
  · apply uniform_convergence_of_error_bound hK hε
    intro n z hz
    exact (hbounds n).2.1 z.1 hz.1 z.2 hz.2
  · apply uniform_convergence_of_error_bound hLamK hε
    intro n t ht
    exact (hbounds n).2.2 t ht

end SphericalAging.CKStability
