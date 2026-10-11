module

public import SphericalAging.PrefixRectangleStability
public import SphericalAging.PrefixPicardOrder
public import SphericalAging.CKPhysicalConsequences

public section

/-! The genuine limiting future-prefix rectangle of a translated CK cluster.
The limit and its equation are derived from the actual causal tree kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalAging.PrefixRectangleLimit
open CKSpecification CKPhysicalConsequences PrefixReflection PrefixPicardOrder GreenCovariance PrefixRectangleStability

/-- Continuous harmless extension of an actual translated correlation. -/
@[expose] def futureCorrelation (d : CKData) (T a b : ℝ) := clampedCorrelation d (T+a) (T+b)

/-- Continuous harmless extension of an actual causal translated response. -/
@[expose] def futureResponse (d : CKData) (T a u : ℝ) := clampedResponse d (T+a) (T+u)

/-- Continuous harmless extension of the actual future prefix Gram kernel. -/
@[expose] def futurePrefix {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (T a b : ℝ) :=
  prefixKernel h T (max 0 (T+a)) (max 0 (T+b))

@[expose] def stationaryCorrelation (c : ℝ → ℝ) (a b : ℝ) := c |a-b|

@[expose] def stationaryResponse (r : ℝ → ℝ) (a u : ℝ) := r (max 0 (a-u))

theorem futureCorrelation_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) : Continuous (Function.uncurry (futureCorrelation d T)) := by
  exact (clampedCorrelation_continuous h).comp (show Continuous (fun z : ℝ × ℝ => (T+z.1,T+z.2)) by fun_prop)

theorem futureResponse_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) : Continuous (Function.uncurry (futureResponse d T)) := by
  exact (clampedResponse_continuous h).comp (show Continuous (fun z : ℝ × ℝ => (T+z.1,T+z.2)) by fun_prop)

theorem futurePrefix_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) : Continuous (Function.uncurry (futurePrefix h T)) := by
  have hc := prefixVector_clamped_continuous h (physical_bounds_of_equations h) T
  have hl : Continuous (fun z : ℝ × ℝ => prefixVector h T (max 0 (T+z.1))) :=
    hc.comp (show Continuous (fun z : ℝ × ℝ => T+z.1) by fun_prop)
  have hr : Continuous (fun z : ℝ × ℝ => prefixVector h T (max 0 (T+z.2))) :=
    hc.comp (show Continuous (fun z : ℝ × ℝ => T+z.2) by fun_prop)
  convert hl.inner hr using 1
  funext z
  rfl

theorem futureCorrelation_eq {d : CKData} {T a b : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    futureCorrelation d T a b=d.C (T+a) (T+b) :=
  clampedCorrelation_eq (add_nonneg hT ha) (add_nonneg hT hb)

theorem futureResponse_eq {d : CKData} {T a u : ℝ} (hT : 0 ≤ T) (hu : 0 ≤ u) (hua : u ≤ a) :
    futureResponse d T a u=d.R (T+a) (T+u) :=
  clampedResponse_eq (add_nonneg hT hu) (add_le_add le_rfl hua)

theorem futurePrefix_eq {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T a b : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    futurePrefix h T a b=futureKernel h T a b := by
  simp only [futurePrefix,futureKernel,max_eq_right (add_nonneg hT ha),max_eq_right (add_nonneg hT hb)]

theorem stationaryCorrelation_continuous {c : ℝ → ℝ} (hc : ContinuousOn c (Ici 0)) :
    Continuous (Function.uncurry (stationaryCorrelation c)) := by
  exact hc.comp_continuous (show Continuous (fun z : ℝ × ℝ => |z.1-z.2|) by fun_prop) (fun z => abs_nonneg (z.1-z.2))

theorem stationaryResponse_continuous {r : ℝ → ℝ} (hr : ContinuousOn r (Ici 0)) :
    Continuous (Function.uncurry (stationaryResponse r)) := by
  exact hr.comp_continuous (show Continuous (fun z : ℝ × ℝ => max 0 (z.1-z.2)) by fun_prop) (fun z => le_max_left 0 (z.1-z.2))

/-- All regularity and bounds for the exact finite future rectangle follow
from the CK equations and the actual projection norm. -/
theorem future_unitData {p : ℕ} {β A T : ℝ} {d : CKData}
    (h : CKEquations p β d) (hT : 0 ≤ T) :
    UnitData A (futureCorrelation d T) (futureResponse d T) (futurePrefix h T) := by
  have hb := physical_bounds_of_equations h
  refine ⟨futureCorrelation_continuous h T,futureResponse_continuous h T,
    futurePrefix_continuous h T,?_,?_,?_⟩
  · intro a ha b hb'
    rw [futureCorrelation_eq hT ha.1 hb'.1,abs_of_nonneg (hb.1 _ _ (add_nonneg hT ha.1) (add_nonneg hT hb'.1)).1]
    exact (hb.1 _ _ (add_nonneg hT ha.1) (add_nonneg hT hb'.1)).2
  · intro a ha u hu
    rw [futureResponse_eq hT hu.1 hu.2,abs_of_nonneg (hb.2 _ _ (add_nonneg hT hu.1) (add_le_add le_rfl hu.2))]
    exact (response_le_correlation h (add_nonneg hT hu.1) (add_le_add le_rfl hu.2)).trans
      (hb.1 _ _ (add_nonneg hT ha.1) (add_nonneg hT hu.1)).2
  · intro a ha b hb'
    exact prefixKernel_abs_le_one h hb T (le_max_left _ _) (le_max_left _ _)

/-- The finite equation in the source is verified for the continuous
extensions, using actual integral congruence on each physical domain. -/
theorem future_rectangle_equation {p : ℕ} {β A T : ℝ} {d : CKData}
    (h : CKEquations p β d) (hT : 0 ≤ T) :
    RectangleEquation (p-1) (β^2*(p : ℝ)) A
      (futureCorrelation d T) (futureResponse d T) (futurePrefix h T) := by
  intro a ha b hb
  rw [futurePrefix_eq h hT ha.1 hb.1,closed_future_rectangle h (physical_bounds_of_equations h) hT ha.1 hb.1]
  unfold rectangleOperator
  rw [futureCorrelation_eq hT ha.1 hb.1]
  congr 2
  · congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (le_min ha.1 hb.1)] at hu
    dsimp only
    rw [futureResponse_eq hT hu.1 (hu.2.trans (min_le_left _ _)),
      futureResponse_eq hT hu.1 (hu.2.trans (min_le_right _ _))]
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ha.1] at hu
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hb.1] at hv
    dsimp only
    rw [futureResponse_eq hT hu.1 hu.2,futureResponse_eq hT hv.1 hv.2,
      futureCorrelation_eq hT hu.1 hv.1,futurePrefix_eq h hT hu.1 hv.1]

/-- An actual stationary translated cluster determines a unique continuous
limiting prefix kernel, satisfying the source's limiting rectangle equation.
Neither a reflected kernel nor a limiting equation is assumed. -/
theorem prefix_rectangle_limit_exists {p : ℕ} {β A : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (hA : 0 ≤ A) (hT : ∀ n,0 ≤ T n)
    (hc : ContinuousOn c (Ici 0)) (hr : ContinuousOn r (Ici 0))
    (hC : TendstoUniformlyOn (fun n (z : ℝ × ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A))
    (hR : TendstoUniformlyOn (fun n (z : ℝ × ℝ) => d.R (T n+z.1) (T n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A)) :
    ∃ q : ℝ → ℝ → ℝ,
      UnitData A (stationaryCorrelation c) (stationaryResponse r) q ∧
      RectangleEquation (p-1) (β^2*(p : ℝ)) A (stationaryCorrelation c) (stationaryResponse r) q ∧
      TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
        (Function.uncurry q) atTop (square A) ∧
      ∀ q',UnitData A (stationaryCorrelation c) (stationaryResponse r) q' →
        RectangleEquation (p-1) (β^2*(p : ℝ)) A (stationaryCorrelation c) (stationaryResponse r) q' →
        ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,q' a b=q a b := by
  have hC' : TendstoUniformlyOn (fun n => Function.uncurry (futureCorrelation d (T n)))
      (Function.uncurry (stationaryCorrelation c)) atTop (square A) := by
    exact hC.congr (Eventually.of_forall (fun n z hz => (futureCorrelation_eq (hT n) hz.1.1 hz.2.1).symm))
  have hR' : TendstoUniformlyOn (fun n => Function.uncurry (futureResponse d (T n)))
      (Function.uncurry (stationaryResponse r)) atTop (triangle A) := by
    have hs := hR.congr (Eventually.of_forall (fun n z hz =>
      (futureResponse_eq (hT n) hz.2.1 hz.2.2).symm))
    exact hs.congr_right (fun z hz => by
      change r (z.1-z.2)=r (max 0 (z.1-z.2))
      rw [max_eq_right (sub_nonneg.mpr hz.2.2)])
  obtain ⟨q,hq,he,hQ,huniq⟩ := rectangle_limit_exists_equation hA
    (mul_nonneg (sq_nonneg β) (Nat.cast_nonneg p))
    (fun n => future_unitData h (hT n))
    (stationaryCorrelation_continuous hc) (stationaryResponse_continuous hr)
    (fun n => future_rectangle_equation h (hT n)) hC' hR'
  refine ⟨q,hq,he,?_,huniq⟩
  exact hQ.congr (Eventually.of_forall (fun n z hz => futurePrefix_eq h (hT n) hz.1.1 hz.2.1))

/-- Physical bounds survive the genuine prefix limit, using actual Picard
order of the projected causal tree kernels. -/
theorem prefix_limit_physical {p : ℕ} {β A : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} {c : ℝ → ℝ} {q : ℝ → ℝ → ℝ}
    (hT : ∀ n,0 ≤ T n)
    (hC : TendstoUniformlyOn (fun n (z : ℝ × ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A))
    (hQ : TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
      (Function.uncurry q) atTop (square A)) :
    ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,0 ≤ q a b ∧ q a b ≤ c |a-b| ∧ q a b ≤ 1 := by
  intro a ha b hb
  have hqp : Tendsto (fun n => futureKernel h (T n) a b) atTop (nhds (q a b)) := by
    simpa only [Function.uncurry_def] using hQ.tendsto_at (x := (a,b)) ⟨ha,hb⟩
  have hcp := hC.tendsto_at (x := (a,b)) ⟨ha,hb⟩
  have hbounds (n : ℕ) := futureKernel_bounds h (physical_bounds_of_equations h) (hT n) ha.1 hb.1
  refine ⟨?_,?_,?_⟩
  · exact ge_of_tendsto hqp (Eventually.of_forall (fun n => (hbounds n).1))
  · exact le_of_tendsto_of_tendsto hqp hcp (Eventually.of_forall (fun n => (hbounds n).2.1))
  · exact le_of_tendsto hqp (Eventually.of_forall (fun n => (hbounds n).2.2))

/-- The exact source formula on every fixed physical rectangle. -/
theorem limiting_rectangle_formula {p : ℕ} {β A : ℝ} {c r : ℝ → ℝ} {q : ℝ → ℝ → ℝ}
    (heq : RectangleEquation (p-1) (β^2*(p : ℝ)) A
      (stationaryCorrelation c) (stationaryResponse r) q)
    {a b : ℝ} (ha : a ∈ Icc 0 A) (hb : b ∈ Icc 0 A) :
    q a b=c |a-b|-2*(∫ u in (0 : ℝ)..min a b,r (a-u)*r (b-u))-
      β^2*(p : ℝ)*(∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,
        r (a-u)*r (b-v)*(c |u-v|^(p-1)-q u v^(p-1))) := by
  rw [heq a ha b hb]
  unfold rectangleOperator stationaryCorrelation
  have hN : (∫ u in (0 : ℝ)..min a b,stationaryResponse r a u*stationaryResponse r b u)=
      ∫ u in (0 : ℝ)..min a b,r (a-u)*r (b-u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (le_min ha.1 hb.1)] at hu
    dsimp only [stationaryResponse]
    rw [max_eq_right (sub_nonneg.mpr (hu.2.trans (min_le_left _ _))),
      max_eq_right (sub_nonneg.mpr (hu.2.trans (min_le_right _ _)))]
  rw [hN]
  congr 2
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ha.1] at hu
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hb.1] at hv
  dsimp only [stationaryResponse]
  rw [max_eq_right (sub_nonneg.mpr hu.2),max_eq_right (sub_nonneg.mpr hv.2)]

/-- The source Step2, including existence, the exact formula, physical bounds,
uniform convergence and uniqueness, from an actual translated CK cluster. -/
theorem physical_prefix_rectangle_limit {p : ℕ} {β A : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (hA : 0 ≤ A) (hT : ∀ n,0 ≤ T n)
    (hc : ContinuousOn c (Ici 0)) (hr : ContinuousOn r (Ici 0))
    (hC : TendstoUniformlyOn (fun n (z : ℝ × ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A))
    (hR : TendstoUniformlyOn (fun n (z : ℝ × ℝ) => d.R (T n+z.1) (T n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A)) :
    ∃ q : ℝ → ℝ → ℝ,Continuous (Function.uncurry q) ∧
      RectangleEquation (p-1) (β^2*(p : ℝ)) A (stationaryCorrelation c) (stationaryResponse r) q ∧
      (∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,0 ≤ q a b ∧ q a b ≤ c |a-b| ∧ q a b ≤ 1) ∧
      TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
        (Function.uncurry q) atTop (square A) ∧
      ∀ q',UnitData A (stationaryCorrelation c) (stationaryResponse r) q' →
        RectangleEquation (p-1) (β^2*(p : ℝ)) A (stationaryCorrelation c) (stationaryResponse r) q' →
        ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,q' a b=q a b := by
  obtain ⟨q,hq,heq,hQ,huniq⟩ := prefix_rectangle_limit_exists h hA hT hc hr hC hR
  exact ⟨q,hq.solution_continuous,heq,prefix_limit_physical h hT hC hQ,hQ,huniq⟩

end SphericalAging.PrefixRectangleLimit
