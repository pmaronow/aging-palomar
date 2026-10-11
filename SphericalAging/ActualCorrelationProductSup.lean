module

public import SphericalAging.ActualCorrelationProduct
public import SphericalAging.NestedUniformSup

public section

/-! Exact nested supremum and sequence forms of the actual three-time product. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.ActualCorrelationProductSup
open CKSpecification CKPhysicalConsequences CenterThresholdSelection ActualCorrelationProduct
open ProductTransfer NestedUniformSup

@[expose] def cyclicResidual (k : Fin 3) (d : CKData) (q u s t : ℝ) : ℝ :=
  if k=0 then d.C t s*d.C s u-q*d.C t u
  else if k=1 then d.C t u*d.C s u-q*d.C t s
  else d.C t u*d.C t s-q*d.C s u

@[expose] def productValues (k : Fin 3) (d : CKData) (q D S : ℝ) : Set ℝ :=
  {x | x=0 ∨ ∃ u s t : ℝ,0≤u ∧ 0≤s ∧ 0≤t ∧ S+D≤u ∧ u+2*D≤s ∧ s+2*D≤t ∧
    x=positivePart (cyclicResidual k d q u s t)}

@[expose] def productSup (k : Fin 3) (d : CKData) (q D S : ℝ) : ℝ := sSup (productValues k d q D S)

theorem residual_le_one {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    {q u s t : ℝ} (hq : 0≤q) (hu : 0≤u) (hs : 0≤s) (ht : 0≤t) (k : Fin 3) :
    positivePart (cyclicResidual k d q u s t)≤1 := by
  have hCtu := (physical_bounds_of_equations h).1 t u ht hu
  have hCts := (physical_bounds_of_equations h).1 t s ht hs
  have hCsu := (physical_bounds_of_equations h).1 s u hs hu
  have prod {a b c : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (hc : 0≤c) :
      positivePart (a*b-q*c)≤1 := by
    apply positivePart_le _ (by norm_num)
    have hp := mul_le_mul ha.2 hb.2 hb.1 (by norm_num : (0:ℝ)≤1)
    nlinarith [mul_nonneg hq hc]
  fin_cases k <;> norm_num only [cyclicResidual,Fin.reduceEq,ite_true,ite_false]
  · exact prod hCts hCsu hCtu.1
  · exact prod hCtu hCsu hCts.1
  · exact prod hCtu hCts hCsu.1

theorem productSup_bounds {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    {q : ℝ} (hq : 0≤q) (k : Fin 3) (D S : ℝ) : 0≤productSup k d q D S ∧ productSup k d q D S≤1 := by
  have hne : (productValues k d q D S).Nonempty := ⟨0,Or.inl rfl⟩
  have hb : ∀ x∈productValues k d q D S,x≤1 := by
    rintro x (hx | ⟨u,s,t,hu,hs,ht,_,_,_,rfl⟩)
    · rw [hx]; norm_num
    · exact residual_le_one h hq hu hs ht k
  exact ⟨le_csSup ⟨1,hb⟩ (Or.inl rfl),csSup_le hne hb⟩

/-- Exact source lim_D limsup_S sup_A positive-part formula, simultaneously
for each of its three cyclic inequalities. -/
theorem actual_three_time_product_supremum {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) (k : Fin 3) :
    Tendsto (fun D : ℝ => limsup (productSup k d q D) atTop) atTop (nhds 0) := by
  apply nested_limsup_tendsto_zero
    (fun D S => (productSup_bounds h H.q_positive.le k D S).1)
    (fun D S => (productSup_bounds h H.q_positive.le k D S).2)
  intro ε hε
  filter_upwards [actual_three_time_product H hε] with D hD
  filter_upwards [hD.2] with S hS
  apply csSup_le (show (productValues k d q D S).Nonempty from ⟨0,Or.inl rfl⟩)
  rintro x (hx | ⟨u,s,t,_,_,_,hu,hs,ht,rfl⟩)
  · rw [hx]; exact hε.le
  · have hh := hS u s t hu hs ht
    fin_cases k <;> norm_num only [cyclicResidual,Fin.reduceEq,ite_true,ite_false]
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2

/-- The three-gap sequence conclusion requires no convergence of individual
correlations and follows from the proved uniform product theorem. -/
theorem actual_three_time_product_sequences {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q)
    {ι : Type*} {F : Filter ι} {u s t : ι → ℝ}
    (hu : Tendsto u F atTop) (hsu : Tendsto (fun n => s n-u n) F atTop)
    (hts : Tendsto (fun n => t n-s n) F atTop) (k : Fin 3) :
    Tendsto (fun n => positivePart (cyclicResidual k d q (u n) (s n) (t n))) F (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hprod := actual_three_time_product H (by positivity : 0<ε/2)
  obtain ⟨D,_,hD⟩ := hprod.exists
  obtain ⟨S,hS⟩ := hD.exists
  filter_upwards [hu.eventually (eventually_ge_atTop (S+D)),
    hsu.eventually (eventually_ge_atTop (2*D)),hts.eventually (eventually_ge_atTop (2*D))] with n hun hsun htsn
  have hs : u n+2*D≤s n := by linarith
  have ht : s n+2*D≤t n := by linarith
  have hh := hS (u n) (s n) (t n) hun hs ht
  have hb : positivePart (cyclicResidual k d q (u n) (s n) (t n))≤ε/2 := by
    fin_cases k <;> norm_num only [cyclicResidual,Fin.reduceEq,ite_true,ite_false]
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (positivePart_nonneg _)]
  linarith

/-- Literal source sequence liminf, all three cyclic residuals. -/
theorem actual_three_time_product_liminf {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q)
    {u s t : ℕ → ℝ} (hu : Tendsto u atTop atTop)
    (hsu : Tendsto (fun n => s n-u n) atTop atTop)
    (hts : Tendsto (fun n => t n-s n) atTop atTop) (k : Fin 3) :
    0≤liminf (fun n => -cyclicResidual k d q (u n) (s n) (t n)) atTop := by
  have hseq := actual_three_time_product_sequences H hu hsu hts k
  have hnonneg : ∀ᶠ n : ℕ in atTop,0≤u n ∧ 0≤s n ∧ 0≤t n := by
    filter_upwards [hu.eventually (eventually_ge_atTop (0:ℝ)),
      hsu.eventually (eventually_ge_atTop (0:ℝ)),hts.eventually (eventually_ge_atTop (0:ℝ))] with n hun hsun htsn
    exact ⟨hun,by linarith,by linarith⟩
  have hlow : ∀ᶠ n : ℕ in atTop,(-1:ℝ)≤ -cyclicResidual k d q (u n) (s n) (t n) := by
    filter_upwards [hnonneg] with n hn
    have hb := residual_le_one h H.q_positive.le hn.1 hn.2.1 hn.2.2 k
    have hx : cyclicResidual k d q (u n) (s n) (t n)≤positivePart (cyclicResidual k d q (u n) (s n) (t n)) := le_max_left _ _
    linarith
  have hupper : ∀ᶠ n : ℕ in atTop,-cyclicResidual k d q (u n) (s n) (t n)≤q := by
    filter_upwards [hnonneg] with n hn
    have hCtu := (physical_bounds_of_equations h).1 (t n) (u n) hn.2.2 hn.1
    have hCts := (physical_bounds_of_equations h).1 (t n) (s n) hn.2.2 hn.2.1
    have hCsu := (physical_bounds_of_equations h).1 (s n) (u n) hn.2.1 hn.1
    unfold cyclicResidual
    split_ifs
    · nlinarith [mul_nonneg hCts.1 hCsu.1,mul_le_mul_of_nonneg_left hCtu.2 H.q_positive.le]
    · nlinarith [mul_nonneg hCtu.1 hCsu.1,mul_le_mul_of_nonneg_left hCts.2 H.q_positive.le]
    · nlinarith [mul_nonneg hCtu.1 hCts.1,mul_le_mul_of_nonneg_left hCsu.2 H.q_positive.le]
  apply (le_liminf_iff (isCoboundedUnder_ge_of_eventually_le atTop hupper)
    (isBoundedUnder_of_eventually_ge hlow)).mpr
  intro y hy
  have hh := hseq.eventually (gt_mem_nhds (by linarith : (0:ℝ)< -y))
  filter_upwards [hh] with n hn
  have hx : cyclicResidual k d q (u n) (s n) (t n)≤positivePart (cyclicResidual k d q (u n) (s n) (t n)) := le_max_left _ _
  linarith

/-- At the physical critical endpoint the scalar marginality hypothesis is
proved directly at q=1/2 and beta^2=4/3; the other inputs are the preceding
selected-profile and response/Fisher conclusions. -/
theorem critical_endpoint_inputs {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} (hβ : β^2=(4/3:ℝ))
    (H : AgingCenterGram.Inputs h c r (1/2:ℝ))
    (hfdt : ∀ t : ℝ,0<t → HasDerivAt c (-r t) t)
    (hmult : Tendsto d.multiplier atTop (nhds (PlateauAlgebra.multiplier 3 β (1/2))))
    (hR : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2)) (fun z => r (z.1-z.2))
      atTop (PrefixRectangleStability.triangle A)) : Inputs h c r (1/2:ℝ) := by
  refine ⟨H,by norm_num,hfdt,hmult,hR,?_⟩
  norm_num [PlateauAlgebra.marginalityPolynomial,hβ]

/-- Literal critical-endpoint actual product, with its three cyclic supremums. -/
theorem critical_endpoint_product_supremum {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} (hβ : β^2=(4/3:ℝ))
    (H : AgingCenterGram.Inputs h c r (1/2:ℝ))
    (hfdt : ∀ t : ℝ,0<t → HasDerivAt c (-r t) t)
    (hmult : Tendsto d.multiplier atTop (nhds (PlateauAlgebra.multiplier 3 β (1/2))))
    (hR : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2)) (fun z => r (z.1-z.2))
      atTop (PrefixRectangleStability.triangle A)) (k : Fin 3) :
    Tendsto (fun D : ℝ => limsup (productSup k d (1/2) D) atTop) atTop (nhds 0) :=
  actual_three_time_product_supremum (critical_endpoint_inputs hβ H hfdt hmult hR) k

end SphericalAging.ActualCorrelationProductSup
