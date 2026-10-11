module

public import SphericalAging.ForkParameterLimits
public import SphericalAging.EarlierDerivativeForgetting
public import SphericalAging.ExternalFieldElementaryPenalty

public section

/-! The complete local threshold-input passage: the preceding finite-fork
algorithmic ceiling passes to the actual prefix, and the preceding
pointwise waiting-state decorrelation becomes uniform on every compact
waiting interval. The two general-spin inputs remain explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
namespace SphericalAging.GeneralThresholdInputTheorem
open Set Filter CKSpecification ProfileCenterEnergy ForkParameterBounds ForkParameterLimits
  ExternalFieldElementaryPenalty
open scoped Topology

theorem prefix_ceiling_from_finite_forks {p : ℕ} {β e q : ℝ} {c r : ℝ→ℝ}
    (H : Profile c r q) (hβ : 0≤β) (hq : 0<q) (hr : ∀u,0<u→0≤r u)
    (hFork : ∀K : ℕ,1≤K→∀L : ℝ,0≤L→forkEnergy p β e c r K L≤
      thresholdEnergy p*(forkNorm c K L)^((p:ℝ)/2)) :
    ∀L : ℝ,0≤L→prefixEnergy p β e c r L≤thresholdEnergy p*(c (2*L))^((p:ℝ)/2) := by
  intro L hL
  have hc : 0<c (2*L) := hq.trans_le (plateau_le_profile H hr (by positivity))
  have hn := (norm_branch_tendsto H hL).rpow_const (p := (p:ℝ)/2) (Or.inl hc.ne')
  have hl := (energy_branch_tendsto (p:=p) (e:=e) H hβ hL hr).sub (hn.const_mul (thresholdEnergy p))
  have hh : prefixEnergy p β e c r L-thresholdEnergy p*(c (2*L))^((p:ℝ)/2)≤0 := by
    apply le_of_tendsto hl
    filter_upwards [eventually_ge_atTop (1:ℕ)] with K hK
    linarith [hFork K hK L hL]
  linarith

@[expose] def waitingSup (d : CKData) (S t : ℝ) : ℝ := sSup ((fun s => |d.C t s|)''Icc 0 S)

theorem waiting_sup_tendsto_zero {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {S : ℝ} (hS : 0≤S) : Tendsto (waitingSup d S) atTop (𝓝 0) := by
  have hb := CKPhysicalConsequences.physical_bounds_of_equations h
  have hu := EarlierDerivativeForgetting.correlation_fixed_wait_uniform h hb hforget S
  have hne (t : ℝ) : (((fun s => |d.C t s|)''Icc 0 S)).Nonempty :=
    ⟨|d.C t 0|,⟨0,⟨le_rfl,hS⟩,rfl⟩⟩
  have hbb (t : ℝ) (ht : 0≤t) : BddAbove ((fun s => |d.C t s|)''Icc 0 S) := by
    refine ⟨1,?_⟩
    rintro z ⟨s,hs,rfl⟩
    change |d.C t s|≤1
    rw [abs_of_nonneg (hb.1 t s ht hs.1).1]
    exact (hb.1 t s ht hs.1).2
  have hn (t : ℝ) (ht : 0≤t) : 0≤waitingSup d S t :=
    (abs_nonneg (d.C t 0)).trans (le_csSup (hbb t ht) ⟨0,⟨le_rfl,hS⟩,rfl⟩)
  apply tendsto_order.mpr
  constructor
  · intro z hz
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact hz.trans_le (hn t ht)
  · intro z hz
    have hh := Metric.tendstoUniformlyOn_iff.mp hu (z/2) (by linarith)
    filter_upwards [hh] with t ht
    have hs : waitingSup d S t≤z/2 := by
      apply csSup_le (hne t)
      rintro a ⟨s,hs,rfl⟩
      have ha : |d.C t s|<z/2 := by simpa [Real.dist_eq] using ht s hs
      exact ha.le
    linarith

theorem source8_1_from_finite_forks_and_fixed_wait {p : ℕ} {β e q : ℝ}
    {d : CKData} (h : CKEquations p β d) {c r : ℝ→ℝ}
    (H : Profile c r q) (hq : 0<q) (hr : ∀u,0<u→0≤r u)
    (hFork : ∀K : ℕ,1≤K→∀L : ℝ,0≤L→forkEnergy p β e c r K L≤
      thresholdEnergy p*(forkNorm c K L)^((p:ℝ)/2))
    (hFixedWait : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0)) :
    (∀L : ℝ,0≤L→prefixEnergy p β e c r L≤thresholdEnergy p*(c (2*L))^((p:ℝ)/2)) ∧
    (∀S : ℝ,0≤S→Tendsto (waitingSup d S) atTop (𝓝 0)) :=
  ⟨prefix_ceiling_from_finite_forks H h.beta_pos.le hq hr hFork,
    fun S hS => waiting_sup_tendsto_zero h hFixedWait hS⟩

end SphericalAging.GeneralThresholdInputTheorem
