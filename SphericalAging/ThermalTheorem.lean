module

public import SphericalAging.ThermalAging
public import SphericalAging.ThermalStationary

public section

/-! Complete local source Corollary 11.7, including the actual late triangle,
stationary complete monotonicity, diagonal and aging limits, and both conditional
power equivalents. The spectral law and response mass are constructed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory Asymptotics
open scoped Topology Asymptotics
namespace SphericalAging.ThermalTheorem
open CKSpecification CKPhysicalConsequences PrefixRectangleStability PrefixReflection
  HankelReflection BackwardRowL2 ThermalRowConvergence ThermalAging

structure Inputs {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (c r : ℝ→ℝ) (q : ℝ) : Prop where
  correlation_continuous : ContinuousOn c (Ici 0)
  correlation_initial : c 0=1
  correlation_bound : ∀v : ℝ,0≤v→|c v|≤1
  response_bound : ∀v : ℝ,0<v→0≤r v ∧ r v≤1
  response_positive : ∀v : ℝ,0<v→0<r v
  plateau_limit : Tendsto c atTop (𝓝 q)
  plateau_lt_one : q<1
  fdt : ∀v : ℝ,0≤v→HasDerivWithinAt c (-r v) (Ici 0) v
  reflected_prefix : ∀A : ℝ,0≤A→TendstoUniformlyOn
    (fun T => Function.uncurry (futureKernel h T))
    (fun z => c (z.1+z.2)) atTop (square A)
  response_row : Tendsto (rowError d r) atTop (𝓝 0)
  fixed_wait_forgetting : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0)

theorem profile_hankel {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) : HankelPositive c := by
  apply hankel_positive_of_prefix_limit (T:=fun n : ℕ => (n:ℝ)) h
  intro a b
  let A : ℝ := max (a:ℝ) (b:ℝ)
  have hA : 0≤A := a.coe_nonneg.trans (le_max_left _ _)
  have ha : (a:ℝ)∈Icc 0 A := ⟨a.coe_nonneg,le_max_left _ _⟩
  have hb : (b:ℝ)∈Icc 0 A := ⟨b.coe_nonneg,le_max_right _ _⟩
  have he := (H.reflected_prefix A hA).tendsto_at (x:=((a:ℝ),(b:ℝ))) ⟨ha,hb⟩
  simpa only [Function.comp_def,Function.uncurry_def] using he.comp tendsto_natCast_atTop_atTop

/-- Every assertion of the thermal corollary, with its precise preceding
selected-profile, response localization and fixed-wait forgetting inputs. -/
theorem source11_7 {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) :
    Tendsto (LateTriangleSup.lateSup
      (fun t s => |GreenCovariance.whiteTerm d t s-thermalProfile r (t-s)|) 0) atTop (𝓝 0) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (thermalProfile r) (Ioi 0) ∧
    (∀n : ℕ,∀τ : ℝ,0<τ→0≤(-1:ℝ)^n*iteratedDeriv n (thermalProfile r) τ) ∧
    Tendsto (thermalProfile r) atTop (𝓝 0) ∧
    Tendsto (fun t => GreenCovariance.whiteTerm d t t) atTop
      (𝓝 (2*(∫v : ℝ,(r v)^2 ∂rayMeasure))) ∧
    (∀{ι : Type*} {F : Filter ι} {t s : ι→ℝ},Tendsto s F atTop→
      Tendsto (fun n => t n-s n) F atTop→
      Tendsto (fun n => GreenCovariance.whiteTerm d (t n) (s n)) F (𝓝 0)) ∧
    (∀{ι : Type*} {F : Filter ι} {t s : ι→ℝ} {c₀ : ℝ},Tendsto s F atTop→
      Tendsto (fun n => t n-s n) F atTop→
      Tendsto (fun n => d.C (t n) (s n)) F (𝓝 c₀)→
      Tendsto (fun n => β^2*(p:ℝ)*(∫u in (0:ℝ)..t n,∫v in (0:ℝ)..s n,
        d.R (t n) u*d.R (s n) v*(d.C u v)^(p-1))) F (𝓝 c₀)) ∧
    (∀ a A : ℝ, 0 < a → 0 < A → (r ~[atTop] (fun τ : ℝ => a*A*τ^(-1-a))) →
      (thermalProfile r ~[atTop] (fun τ => 2*(1-q)*r τ)) ∧
      (thermalProfile r ~[atTop] (fun τ : ℝ => 2*(1-q)*a*A*τ^(-1-a)))) := by
  have hH := profile_hankel H
  have hd : ∀v : ℝ,0<v→HasDerivAt c (-r v) v :=
    fun v hv => (H.fdt v hv.le).hasDerivAt (Ici_mem_nhds hv)
  obtain ⟨hi,hm,hsmooth,hcm,hdecay⟩ := ThermalStationary.hankel_thermal_properties
    c r q hH H.correlation_bound H.correlation_initial H.correlation_continuous hd H.plateau_limit
  have hr : MemLp r 2 rayMeasure :=
    ThermalStationary.response_memLp_two_of_bound r hi H.response_bound
  change ContDiffOn ℝ (⊤:ℕ∞) (thermalProfile r) (Ioi 0) at hsmooth
  change ∀n : ℕ,∀τ : ℝ,0<τ→0≤(-1:ℝ)^n*iteratedDeriv n (thermalProfile r) τ at hcm
  change Tendsto (thermalProfile r) atTop (𝓝 0) at hdecay
  refine ⟨thermal_uniform_supremum h hr H.response_row,hsmooth,hcm,hdecay,
    thermal_diagonal_limit h hr H.response_row,?_,?_,?_⟩
  · intro ι F t s hs hlag
    exact thermal_late_diverging_pair h hr H.response_row hdecay hs hlag
  · intro ι F t s c₀ hs hlag hC
    exact colored_aging_rectangle h (physical_bounds_of_equations h) H.fixed_wait_forgetting
      hr H.response_row hdecay hs hlag hC
  · intro a A ha hA heq
    exact (ThermalStationary.hankel_thermal_tail c r a A q hH H.correlation_bound
      H.correlation_initial H.correlation_continuous hd H.plateau_limit
      H.response_positive ha hA H.plateau_lt_one heq).2

end SphericalAging.ThermalTheorem
