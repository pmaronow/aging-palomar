module

public import SphericalAging.GaussianForkUniformConcentration

public section

/-! The actual all-basepoint concentration event is closed and measurable.
Its high-probability bound follows from the constructed uniform tail. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianForkUniformEvents
open Set MeasureTheory ProbabilityTheory FiniteModel
open GaussianOrthogonalForkCovariance GaussianFixedBaseForkConcentration
open GaussianOrthogonalForkSupremum OrthogonalForkNonempty GaussianForkUniformConcentration
open scoped NNReal
variable {N p K : ℕ}

theorem fixedBase_supremum_continuous (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (a b r q : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hrq : r≤q) (hq1 : q≤1) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*r) :
    Continuous (GaussianFixedBaseForkConcentration.supremum (p:=p) (K:=K) a b r q x) := by
  letI := leafDomain_nonempty hKN x r q hr hrq hx
  let A : LeafDomain N K x r q→(ForkTensor N p K→L[ℝ] ℝ) := fun y => forkDual a b x y.1
  have hA : ∀y,‖A y‖≤(⟨Real.sqrt (1/((K:ℝ)*N)),Real.sqrt_nonneg _⟩:ℝ≥0) :=
    fun y => orthogonal_forkDual_norm_le (by omega) hp hK a b ha hab hb x y.1 r q hr (hr.trans hrq) hq1 y.2
  have hInput : Continuous (tensorInputs (N:=N) (p:=p) (K:=K)) :=
    (PiLp.continuous_toLp 2 (fun _ : Option (Fin K) => AdaptiveGradientDisclosure.TensorSpace N p)).comp
      (continuous_pi (fun i =>
        (PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).comp (continuous_apply i)))
  have hC := (GaussianDualSupConcentration.supremum_lipschitz A hA).continuous.comp hInput
  convert hC using 1
  funext J
  change sSup (Set.range (fun y : LeafDomain N K x r q => averagedIncrement a b x y.1 J))=
    sSup (Set.range (fun y : LeafDomain N K x r q => forkDual a b x y.1 (tensorInputs J)))
  simp_rw [forkDual_tensorInputs]

@[expose] def goodEvent (N p K : ℕ) (a b r q ε : ℝ) : Set (ForkDisorder N p K) :=
  {J | ∀x : Vector N,‖x‖^2=(N:ℝ)*r→
    |GaussianFixedBaseForkConcentration.supremum a b r q x J-
      ∫J',GaussianFixedBaseForkConcentration.supremum a b r q x J' ∂forkLaw N p K|≤ε}

theorem goodEvent_isClosed (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (a b r q ε : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hrq : r≤q) (hq1 : q≤1) : IsClosed (goodEvent N p K a b r q ε) := by
  have hEq : goodEvent N p K a b r q ε=
      ⋂x : Vector N,⋂hx : ‖x‖^2=(N:ℝ)*r,
      {J | |GaussianFixedBaseForkConcentration.supremum a b r q x J-
        ∫J',GaussianFixedBaseForkConcentration.supremum a b r q x J' ∂forkLaw N p K|≤ε} := by
    ext J
    simp only [goodEvent,mem_setOf_eq,mem_iInter]
  rw [hEq]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro hx
  exact isClosed_le (continuous_abs.comp ((fixedBase_supremum_continuous hp hK hKN
    a b r q ha hab hb hr hrq hq1 x hx).sub continuous_const)) continuous_const

theorem actual_uniform_fork_success_probability (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (a b δ r q ε : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hδ : 0<δ) (hδr : δ≤r) (hrq : r≤q) (hq1 : q≤1) (hε : 0<ε) :
    1-2*(1+2/mesh p δ ε)^N*Real.exp (-((K:ℝ)*N)*ε^2/(8*(Real.pi/2)^2))-
      ((K:ℝ)+1)*Real.exp (-(N:ℝ))≤
      (forkLaw N p K).real (goodEvent N p K a b r q ε) := by
  have hgood := goodEvent_isClosed hp hK hKN a b r q ε ha hab hb (hδ.le.trans hδr) hrq hq1
  have hcomp : (goodEvent N p K a b r q ε)ᶜ⊆
      {J | ∃x : Vector N,‖x‖^2=(N:ℝ)*r ∧
        ε≤|GaussianFixedBaseForkConcentration.supremum a b r q x J-
          ∫J',GaussianFixedBaseForkConcentration.supremum a b r q x J' ∂forkLaw N p K|} := by
    intro J hJ
    simp only [goodEvent,mem_compl_iff,mem_setOf_eq,not_forall,not_le] at hJ
    obtain ⟨x,hx,hdev⟩ := hJ
    exact ⟨x,hx,hdev.le⟩
  have hbad := (measureReal_mono hcomp).trans
    (actual_uniform_fork_probability_bound hp hK hKN a b δ r q ε ha hab hb hδ hδr hrq hq1 hε)
  have hsum := measureReal_add_measureReal_compl (μ:=forkLaw N p K) hgood.measurableSet
  rw [probReal_univ] at hsum
  linarith

end SphericalAging.GaussianForkUniformEvents
