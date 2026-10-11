module

public import SphericalAging.CKFiniteUniqueness
public import SphericalAging.CKPositivity
public import SphericalAging.CKTruncation
public import SphericalAging.CKClampRemoval
public import SphericalAging.CovariancePSD

public section

/-!
# Compatible finite CK solutions and their global limit

Finite uniqueness identifies solutions on overlapping horizons. The assembled
functions are locally equal to one fixed finite solution; continuity and
one-sided differentiability therefore follow from genuine finite equations.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology BigOperators

namespace SphericalAging.CKGlobalExistence
open CKSpecification CKLocalExistence CKPositivity CKFiniteUniqueness CKTruncation

structure FiniteFamily (p : ℕ) (β : ℝ) where
  data : ℝ → CKData
  equations : ∀ T, 0 < T → CKOnHorizon p β T (data T)

theorem overlap_equivalence {p : ℕ} {β A B : ℝ} (f : FiniteFamily p β)
    (hA : 0 < A) (hB : 0 < B) :
    (∀ t ∈ Icc 0 (min A B), ∀ s ∈ Icc 0 (min A B), (f.data A).C t s=(f.data B).C t s) ∧
    (∀ t ∈ Icc 0 (min A B), ∀ s ∈ Icc 0 t, (f.data A).R t s=(f.data B).R t s) ∧
    (∀ t ∈ Icc 0 (min A B), (f.data A).multiplier t=(f.data B).multiplier t) := by
  exact ck_on_horizon_unique
    (CKOnHorizon.restrict (f.equations A hA) (lt_min hA hB) (min_le_left _ _))
    (CKOnHorizon.restrict (f.equations B hB) (lt_min hA hB) (min_le_right _ _))

@[expose] def chosenHorizon (t s : ℝ) : ℝ := max 0 (max t s)+1

theorem chosenHorizon_pos (t s : ℝ) : 0 < chosenHorizon t s := by
  have hh := le_max_left (0 : ℝ) (max t s)
  unfold chosenHorizon
  linarith

@[expose] def assembledData {p : ℕ} {β : ℝ} (f : FiniteFamily p β) : CKData where
  C := fun t s => (f.data (chosenHorizon t s)).C (max 0 t) (max 0 s)
  R := fun t s => (f.data (chosenHorizon t s)).R (max (max 0 t) (max 0 s)) (min (max 0 t) (max 0 s))
  multiplier := fun t => (f.data (max 0 t+1)).multiplier (max 0 t)

theorem assembled_correlation_eq {p : ℕ} {β : ℝ} (f : FiniteFamily p β)
    {H t s : ℝ} (hH : 0 < H) (ht : max 0 t ≤ H) (hs : max 0 s ≤ H) :
    (assembledData f).C t s=(f.data H).C (max 0 t) (max 0 s) := by
  have ht' : max 0 t ≤ chosenHorizon t s := by
    unfold chosenHorizon
    have hh : max 0 t ≤ max 0 (max t s) := max_le_max_left 0 (le_max_left _ _)
    linarith
  have hs' : max 0 s ≤ chosenHorizon t s := by
    unfold chosenHorizon
    have hh : max 0 s ≤ max 0 (max t s) := max_le_max_left 0 (le_max_right _ _)
    linarith
  exact (overlap_equivalence f (chosenHorizon_pos t s) hH).1 _
    ⟨le_max_left _ _,le_min ht' ht⟩ _ ⟨le_max_left _ _,le_min hs' hs⟩

theorem assembled_response_eq {p : ℕ} {β : ℝ} (f : FiniteFamily p β)
    {H t s : ℝ} (hH : 0 < H) (ht : max 0 t ≤ H) (hs : max 0 s ≤ H) :
    (assembledData f).R t s=
      (f.data H).R (max (max 0 t) (max 0 s)) (min (max 0 t) (max 0 s)) := by
  have hmax : max (max 0 t) (max 0 s) ≤ chosenHorizon t s := by
    unfold chosenHorizon
    have hh : max (max 0 t) (max 0 s)=max 0 (max t s) := by simp [max_assoc,max_left_comm]
    rw [hh]
    linarith
  exact (overlap_equivalence f (chosenHorizon_pos t s) hH).2.1 _
    ⟨(le_max_left 0 t).trans (le_max_left _ _),le_min hmax (max_le ht hs)⟩ _
    ⟨le_min (le_max_left _ _) (le_max_left _ _),min_le_max⟩

theorem assembled_multiplier_eq {p : ℕ} {β : ℝ} (f : FiniteFamily p β)
    {H t : ℝ} (hH : 0 < H) (ht : max 0 t ≤ H) :
    (assembledData f).multiplier t=(f.data H).multiplier (max 0 t) := by
  have hA : 0 < max 0 t+1 := by linarith [le_max_left (0 : ℝ) t]
  exact (overlap_equivalence f hA hH).2.2 _
    ⟨le_max_left _ _,le_min (by linarith) ht⟩

theorem assembled_fields_eq_on_square {p : ℕ} {β : ℝ} (f : FiniteFamily p β)
    {H : ℝ} (hH : 0 < H) :
    (∀ t ∈ Icc 0 H, ∀ s ∈ Icc 0 H, (assembledData f).C t s=(f.data H).C t s) ∧
    (∀ t ∈ Icc 0 H, ∀ s ∈ Icc 0 t, (assembledData f).R t s=(f.data H).R t s) ∧
    (∀ t ∈ Icc 0 H, (assembledData f).multiplier t=(f.data H).multiplier t) := by
  constructor
  · intro t ht s hs
    simpa only [max_eq_right ht.1,max_eq_right hs.1] using
      assembled_correlation_eq f (t := t) (s := s) hH (by simpa only [max_eq_right ht.1] using ht.2)
        (by simpa only [max_eq_right hs.1] using hs.2)
  constructor
  · intro t ht s hs
    simpa only [max_eq_right ht.1,max_eq_right hs.1,max_eq_left hs.2,min_eq_right hs.2] using
      assembled_response_eq f (t := t) (s := s) hH (by simpa only [max_eq_right ht.1] using ht.2)
        (by simpa only [max_eq_right hs.1] using hs.2.trans ht.2)
  · intro t ht
    simpa only [max_eq_right ht.1] using assembled_multiplier_eq f (t := t) hH
      (by simpa only [max_eq_right ht.1] using ht.2)

theorem assembled_correlation_continuous {p : ℕ} {β : ℝ} (f : FiniteFamily p β) :
    Continuous (Function.uncurry (assembledData f).C) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let H := chosenHorizon z.1 z.2
  have hH := chosenHorizon_pos z.1 z.2
  have htH : max 0 z.1 < H := by
    dsimp only [H,chosenHorizon]
    have hh := max_le_max_left (0 : ℝ) (le_max_left z.1 z.2)
    linarith
  have hsH : max 0 z.2 < H := by
    dsimp only [H,chosenHorizon]
    have hh := max_le_max_left (0 : ℝ) (le_max_right z.1 z.2)
    linarith
  have ht : ∀ᶠ x : ℝ × ℝ in 𝓝 z, max 0 x.1 < H :=
    (show Continuous (fun x : ℝ × ℝ => max 0 x.1) by fun_prop).continuousAt.eventually
      (Iio_mem_nhds htH)
  have hs : ∀ᶠ x : ℝ × ℝ in 𝓝 z, max 0 x.2 < H :=
    (show Continuous (fun x : ℝ × ℝ => max 0 x.2) by fun_prop).continuousAt.eventually
      (Iio_mem_nhds hsH)
  have hc : Continuous (fun x : ℝ × ℝ => (f.data H).C (max 0 x.1) (max 0 x.2)) :=
    (f.equations H hH).correlation_continuous.comp
      (show Continuous (fun x : ℝ × ℝ => (max 0 x.1,max 0 x.2)) by fun_prop)
  apply hc.continuousAt.congr
  filter_upwards [ht,hs] with x hx hy
  exact (assembled_correlation_eq f hH hx.le hy.le).symm

theorem assembled_response_continuous {p : ℕ} {β : ℝ} (f : FiniteFamily p β) :
    Continuous (Function.uncurry (assembledData f).R) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let H := chosenHorizon z.1 z.2
  have hH := chosenHorizon_pos z.1 z.2
  have htH : max 0 z.1 < H := by
    dsimp only [H,chosenHorizon]
    have hh := max_le_max_left (0 : ℝ) (le_max_left z.1 z.2)
    linarith
  have hsH : max 0 z.2 < H := by
    dsimp only [H,chosenHorizon]
    have hh := max_le_max_left (0 : ℝ) (le_max_right z.1 z.2)
    linarith
  have ht : ∀ᶠ x : ℝ × ℝ in 𝓝 z, max 0 x.1 < H :=
    (show Continuous (fun x : ℝ × ℝ => max 0 x.1) by fun_prop).continuousAt.eventually
      (Iio_mem_nhds htH)
  have hs : ∀ᶠ x : ℝ × ℝ in 𝓝 z, max 0 x.2 < H :=
    (show Continuous (fun x : ℝ × ℝ => max 0 x.2) by fun_prop).continuousAt.eventually
      (Iio_mem_nhds hsH)
  have hc : Continuous (fun x : ℝ × ℝ => (f.data H).R
      (max (max 0 x.1) (max 0 x.2)) (min (max 0 x.1) (max 0 x.2))) :=
    (f.equations H hH).response_continuous.comp
      (show Continuous (fun x : ℝ × ℝ =>
        (max (max 0 x.1) (max 0 x.2),min (max 0 x.1) (max 0 x.2))) by fun_prop)
  apply hc.continuousAt.congr
  filter_upwards [ht,hs] with x hx hy
  exact (assembled_response_eq f hH hx.le hy.le).symm

theorem assembled_multiplier_continuous {p : ℕ} {β : ℝ} (f : FiniteFamily p β) :
    Continuous (assembledData f).multiplier := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let H := max 0 t+1
  have hH : 0 < H := by dsimp only [H]; linarith [le_max_left (0 : ℝ) t]
  have htH : max 0 t < H := by dsimp only [H]; linarith
  have ht : ∀ᶠ x : ℝ in 𝓝 t, max 0 x < H :=
    (show Continuous (fun x : ℝ => max 0 x) by fun_prop).continuousAt.eventually
      (Iio_mem_nhds htH)
  have hc : Continuous (fun x : ℝ => (f.data H).multiplier (max 0 x)) :=
    (f.equations H hH).multiplier_continuous.comp (by fun_prop)
  apply hc.continuousAt.congr
  filter_upwards [ht] with x hx
  exact (assembled_multiplier_eq f hH hx.le).symm



theorem data_slopes_congr_on_causal_square {p : ℕ} {β T : ℝ} {d e : CKData}
    (hC : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, d.C t s=e.C t s)
    (hR : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, d.R t s=e.R t s)
    (hLambda : ∀ t ∈ Icc 0 T, d.multiplier t=e.multiplier t)
    {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
    correlationSlope p β d t s=correlationSlope p β e t s ∧
      responseSlope p β d t s=responseSlope p β e t s := by
  have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
  have hrmem : (∫ u in s..t, xiDoublePrime p (d.C t u)*d.R t u*d.R u s)=
      ∫ u in s..t, xiDoublePrime p (e.C t u)*e.R t u*e.R u s := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hs.2] at hu
    have huT : u ∈ Icc 0 T := ⟨hs.1.trans hu.1,hu.2.trans ht.2⟩
    dsimp only
    rw [hC t ht u huT,hR t ht u ⟨huT.1,hu.2⟩,hR u huT s ⟨hs.1,hu.1⟩]
  have hcmem : (∫ u in (0 : ℝ)..t, xiDoublePrime p (d.C t u)*d.R t u*d.C u s)=
      ∫ u in (0 : ℝ)..t, xiDoublePrime p (e.C t u)*e.R t u*e.C u s := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    have huT : u ∈ Icc 0 T := ⟨hu.1,hu.2.trans ht.2⟩
    dsimp only
    rw [hC t ht u huT,hR t ht u ⟨hu.1,hu.2⟩,hC u huT s hsT]
  have hfmem : (∫ u in (0 : ℝ)..s, xiPrime p (d.C t u)*d.R s u)=
      ∫ u in (0 : ℝ)..s, xiPrime p (e.C t u)*e.R s u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hs.1] at hu
    have huT : u ∈ Icc 0 T := ⟨hu.1,hu.2.trans hsT.2⟩
    dsimp only
    rw [hC t ht u huT,hR s hsT u ⟨hu.1,hu.2⟩]
  constructor
  · simp only [correlationSlope,hLambda t ht,hC t ht s hsT,hcmem,hfmem]
  · simp only [responseSlope,hLambda t ht,hR t ht s hs,hrmem]

theorem assembled_slopes_eq {p : ℕ} {β H t s : ℝ} (f : FiniteFamily p β)
    (hH : 0 < H) (ht : t ∈ Icc 0 H) (hs : s ∈ Icc 0 t) :
    correlationSlope p β (assembledData f) t s=correlationSlope p β (f.data H) t s ∧
      responseSlope p β (assembledData f) t s=responseSlope p β (f.data H) t s := by
  have he := assembled_fields_eq_on_square f hH
  exact data_slopes_congr_on_causal_square he.1 he.2.1 he.2.2 ht hs

/-- A finite upper endpoint beyond the point does not restrict its right derivative. -/
theorem finite_hasDerivWithinAt_right {F : ℝ → ℝ} {s t H a : ℝ}
    (h : HasDerivWithinAt F a (Icc s H) t) (htH : t < H) :
    HasDerivWithinAt F a (Ici s) t := by
  apply h.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htH)] with u hu huH
  exact ⟨hu,huH.le⟩

theorem assembled_row_derivatives {p : ℕ} {β t s : ℝ} (f : FiniteFamily p β)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    HasDerivWithinAt (fun u => (assembledData f).C u s)
      (correlationSlope p β (assembledData f) t s) (Ici s) t ∧
    HasDerivWithinAt (fun u => (assembledData f).R u s)
      (responseSlope p β (assembledData f) t s) (Ici s) t := by
  let H := t+1
  have ht : 0 ≤ t := hs.trans hst
  have hH : 0 < H := by dsimp only [H]; linarith
  have htH : t < H := by dsimp only [H]; linarith
  have hfields := assembled_fields_eq_on_square f hH
  have hslopes := assembled_slopes_eq f hH (show t ∈ Icc 0 H from ⟨ht,htH.le⟩) ⟨hs,hst⟩
  have hloc := f.equations H hH
  have heC : (fun u => (assembledData f).C u s) =ᶠ[𝓝[Ici s] t] (fun u => (f.data H).C u s) := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htH)] with u hu huH
    exact hfields.1 u ⟨hs.trans hu,huH.le⟩ s ⟨hs,hst.trans htH.le⟩
  have heR : (fun u => (assembledData f).R u s) =ᶠ[𝓝[Ici s] t] (fun u => (f.data H).R u s) := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htH)] with u hu huH
    exact hfields.2.1 u ⟨hs.trans hu,huH.le⟩ s ⟨hs,hu⟩
  constructor
  · rw [hslopes.1]
    exact (finite_hasDerivWithinAt_right (hloc.correlation_derivative t ⟨ht,htH.le⟩ s ⟨hs,hst⟩) htH).congr_of_eventuallyEq heC (hfields.1 t ⟨ht,htH.le⟩ s ⟨hs,hst.trans htH.le⟩)
  · rw [hslopes.2]
    exact (finite_hasDerivWithinAt_right (hloc.response_derivative t ⟨ht,htH.le⟩ s ⟨hs,hst⟩) htH).congr_of_eventuallyEq heR (hfields.2.1 t ⟨ht,htH.le⟩ s ⟨hs,hst⟩)

theorem assembled_ck_equations {p : ℕ} {β : ℝ} (f : FiniteFamily p β) :
    CKEquations p β (assembledData f) := by
  have h1 := f.equations 1 (by norm_num)
  have hslopes := continuous_data_slopes p β (assembled_correlation_continuous f)
    (assembled_response_continuous f) (assembled_multiplier_continuous f)
  refine ⟨h1.spin_ge_three,h1.beta_pos,(assembled_correlation_continuous f).continuousOn,
    (assembled_response_continuous f).continuousOn,(assembled_multiplier_continuous f).continuousOn,
    ?_,?_,?_,?_,?_,?_,hslopes.2.continuousOn,hslopes.1.continuousOn⟩
  · intro t s _ _
    dsimp only [assembledData,chosenHorizon]
    rw [max_comm t s]
    exact (f.equations (chosenHorizon s t) (chosenHorizon_pos s t)).correlation_symmetric _ _
  · intro t ht
    have hH : 0 < t+1 := by linarith
    rw [(assembled_fields_eq_on_square f hH).1 t ⟨ht,by linarith⟩ t ⟨ht,by linarith⟩]
    exact (f.equations (t+1) hH).correlation_diagonal t ⟨ht,by linarith⟩
  · intro t ht
    have hH : 0 < t+1 := by linarith
    rw [(assembled_fields_eq_on_square f hH).2.1 t ⟨ht,by linarith⟩ t ⟨ht,le_refl t⟩]
    exact (f.equations (t+1) hH).response_diagonal t ⟨ht,by linarith⟩
  · intro t ht
    have hH : 0 < t+1 := by linarith
    have hfields := assembled_fields_eq_on_square f hH
    have heq : memoryMass p (assembledData f) t=memoryMass p (f.data (t+1)) t := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht] at hu
      dsimp only
      rw [hfields.1 t ⟨ht,by linarith⟩ u ⟨hu.1,by linarith [hu.2]⟩,
        hfields.2.1 t ⟨ht,by linarith⟩ u hu]
    rw [hfields.2.2 t ⟨ht,by linarith⟩,heq]
    exact (f.equations (t+1) hH).multiplier_eq t ⟨ht,by linarith⟩
  · intro t s hs hst
    exact (assembled_row_derivatives f hs hst).2
  · intro t s hs hst
    exact (assembled_row_derivatives f hs hst).1



theorem assembled_physical_bounds {p : ℕ} {β : ℝ} (f : FiniteFamily p β) :
    PhysicalBounds (assembledData f) := by
  constructor
  · intro t s ht hs
    let H := chosenHorizon t s
    have hH := chosenHorizon_pos t s
    have htH : t ≤ H := by dsimp only [H,chosenHorizon]; linarith [le_max_right 0 (max t s),le_max_left t s]
    have hsH : s ≤ H := by dsimp only [H,chosenHorizon]; linarith [le_max_right 0 (max t s),le_max_right t s]
    have hck := f.equations H hH
    rw [(assembled_fields_eq_on_square f hH).1 t ⟨ht,htH⟩ s ⟨hs,hsH⟩]
    exact CovariancePSD.finite_correlation_bounds hck (ck_horizon_nonnegative hck) ⟨ht,htH⟩ ⟨hs,hsH⟩
  · intro t s hs hst
    have ht := hs.trans hst
    have hH : 0 < t+1 := by linarith
    have hck := f.equations (t+1) hH
    rw [(assembled_fields_eq_on_square f hH).2.1 t ⟨ht,by linarith⟩ s ⟨hs,hst⟩]
    exact (ck_horizon_nonnegative hck).2 t ⟨ht,by linarith⟩ s ⟨hs,hst⟩

theorem assembled_correlation_psd {p : ℕ} {β : ℝ} (f : FiniteFamily p β) :
    PositiveSemidefiniteCorrelation (assembledData f) := by
  intro n times weights htimes
  let H : ℝ := 1+∑ i : Fin n, |times i|
  have hsum : 0 ≤ ∑ i : Fin n, |times i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hH : 0 < H := by dsimp only [H]; linarith
  have hbounded (i : Fin n) : times i ∈ Icc 0 H := by
    have hh : |times i| ≤ ∑ j : Fin n, |times j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (times j)) (Finset.mem_univ i)
    exact ⟨htimes i,by dsimp only [H]; linarith [le_abs_self (times i)]⟩
  have hck := f.equations H hH
  have hh := CovariancePSD.correlation_psd hck (ck_horizon_nonnegative hck) n times weights hbounded
  have he : ∀ i j, (assembledData f).C (times i) (times j)=(f.data H).C (times i) (times j) :=
    fun i j => (assembled_fields_eq_on_square f hH).1 _ (hbounded i) _ (hbounded j)
  simpa only [he] using hh

@[expose] noncomputable def actualFamily {p : ℕ} (hp : 3 ≤ p) {β : ℝ} (hβ : 0 < β) : FiniteFamily p β where
  data := fun T => if hT : 0 < T then Classical.choose (CKClampRemoval.ck_finite_existence hp hβ hT)
    else Classical.choose (CKClampRemoval.ck_finite_existence hp hβ (show (0 : ℝ) < 1 by norm_num))
  equations := by
    intro T hT
    simp only [dite_eq_left hT]
    exact Classical.choose_spec (CKClampRemoval.ck_finite_existence hp hβ hT)

/-- Proposition 3.2: genuine global existence, uniqueness, physical bounds,
and positive semidefinite covariance, solely from p≥3 and β>0. -/
theorem ck_global_wellposedness {p : ℕ} (hp : 3 ≤ p) {β : ℝ} (hβ : 0 < β) :
    ∃ d : CKData, CKEquations p β d ∧ PhysicalBounds d ∧ PositiveSemidefiniteCorrelation d ∧
      ∀ e : CKData, CKEquations p β e → DomainEquivalent d e := by
  let f := actualFamily hp hβ
  let d := assembledData f
  have hck : CKEquations p β d := assembled_ck_equations f
  exact ⟨d,hck,assembled_physical_bounds f,assembled_correlation_psd f,
    fun e he => CKWellposedness.ck_equations_unique hck he⟩

theorem proposition_3_2 : WellposednessGoal := by
  intro p hp β hβ
  exact ck_global_wellposedness hp hβ

end SphericalAging.CKGlobalExistence
