module

public import SphericalAging.PositiveMarginalityTheorem
public import SphericalAging.StationaryReflectionFromTranslation
public import SphericalAging.StationaryProfileUniquenessBridge
public import SphericalAging.ContinuousLateLimit

public section

/-! Exact preceding stationary-cluster input for the selection chapter.
Only translated convergence, FDT and plateau/integrability properties are
inputs. The stationary ODE, all physical bounds and scalar constraints follow
from CK and the earlier checked local arguments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.StationaryClusterInputs
open CKSpecification CKPhysicalConsequences ScalarConstraints ProfileCenterEnergy
  StationaryResponseLimit StationaryReflectionFromTranslation PrefixRectangleStability

structure Cluster {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (T : ℕ → ℝ) (c r : ℝ → ℝ) (ell q : ℝ) : Prop where
  late : Tendsto T atTop atTop
  correlation : ∀A : ℝ,0≤A → TendstoUniformlyOn
    (fun n (z : ℝ×ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A)
  response : ∀A : ℝ,0≤A → TendstoUniformlyOn
    (fun n (z : ℝ×ℝ) => d.R (T n+z.1) (T n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A)
  multiplier : ∀A : ℝ,0≤A → TendstoUniformlyOn
    (fun n a => d.multiplier (T n+a)) (fun _ => ell) atTop (Icc 0 A)
  fdt : ∀t : ℝ,0≤t → HasDerivWithinAt c (-r t) (Ici 0) t
  plateau : Tendsto c atTop (𝓝 q)
  plateau_lt_one : q<1
  integrable_response : IntegrableOn r (Ioi 0)

theorem Cluster.stationary {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell q) : StationaryInputs (p-2) (β^2*(p:ℝ)) ell c r :=
  stationaryInputs_of_uniform_translation_and_fdt h H.late
    H.correlation H.response H.multiplier H.fdt

theorem Cluster.physical {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell q) : ∀t : ℝ,0≤t → 0≤r t ∧ r t≤c t ∧ c t≤1 :=
  (stationary_response_of_uniform_translation h H.late
    H.correlation H.response H.multiplier).physical

theorem Cluster.profile {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell q) : Profile c r q := by
  have hs := H.stationary
  refine ⟨hs.continuous_c,hs.continuous_r,?_,hs.initial_c,H.plateau,
    H.integrable_response,?_⟩
  · intro t ht
    exact ⟨(H.physical t ht).1.trans (H.physical t ht).2.1,(H.physical t ht).2.2⟩
  · intro t ht
    exact (H.fdt t ht.le).hasDerivAt (Ici_mem_nhds ht)

theorem Cluster.scalar {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell q) :
    0≤q ∧ ell=PlateauAlgebra.multiplier p β q ∧
      ∀x∈Ioo q 1,PlateauAlgebra.scalarSignPolynomial p β ell x<0 := by
  have hq : 0≤q := ge_of_tendsto H.plateau (by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact (H.physical t ht).1.trans (H.physical t ht).2.1)
  have hmass := weighted_response_integral H.profile 0
  simp only [pow_zero,one_mul,Nat.cast_zero,zero_add,div_one,pow_one] at hmass
  have hs := scalar_constraints_from_stationary (p-2) (β^2*(p:ℝ)) ell q c r
    H.stationary (fun t ht => (H.physical t ht).2.2) hq H.plateau_lt_one
    H.integrable_response hmass H.plateau
  have hnat : p-2+1=p-1 := by have hp:=h.spin_ge_three; omega
  refine ⟨hq,?_,?_⟩
  · simpa only [PlateauAlgebra.multiplier,hnat] using hs.multiplier_identity
  · intro x hx
    simpa only [signPolynomial,scalarPhi,
      PlateauAlgebra.scalarSignPolynomial,hnat] using hs.strict_sign x hx.1 hx.2

theorem Cluster.multiplier_zero {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell q) : Tendsto (d.multiplier ∘ T) atTop (𝓝 ell) := by
  simpa only [Function.comp_def,add_zero] using
    (H.multiplier 0 le_rfl).tendsto_at (x:=0) ⟨le_rfl,le_rfl⟩

end SphericalAging.StationaryClusterInputs
