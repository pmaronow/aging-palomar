module

public import SphericalAging.OrthogonalForkEnergyTransport
public import SphericalAging.OrthogonalForkNonempty

public section

/-! The genuine fixed-base fork supremum changes continuously on the
actual bounded-landscape event. This is the spatial extension ingredient
in Huang--Sellke Lemma 3.2. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.OrthogonalForkSupremumTransport
open Set MeasureTheory FiniteModel GaussianLandscape ForkEnergyComparison
  GaussianOrthogonalForkCovariance GaussianOrthogonalForkSupremum
  OrthogonalForkBasepointTransport OrthogonalForkEnergyTransport
variable {N p K : ℕ}
open scoped NNReal

theorem csSup_transport_abs_le {I J : Type*} [Nonempty I] [Nonempty J]
    (e : I≃J) (f : I→ℝ) (g : J→ℝ) (hf : BddAbove (Set.range f))
    (hg : BddAbove (Set.range g)) (B : ℝ) (h : ∀i,|f i-g (e i)|≤B) :
    |sSup (Set.range f)-sSup (Set.range g)|≤B := by
  have hfg : sSup (Set.range f)≤sSup (Set.range g)+B := by
    apply csSup_le (Set.range_nonempty _)
    rintro z ⟨i,rfl⟩
    have hi := le_csSup hg (Set.mem_range_self (e i))
    have hh := (le_abs_self _).trans (h i)
    linarith
  have hgf : sSup (Set.range g)≤sSup (Set.range f)+B := by
    apply csSup_le (Set.range_nonempty _)
    rintro z ⟨j,rfl⟩
    have hi := le_csSup hf (Set.mem_range_self (e.symm j))
    have hh := (neg_le_abs _).trans (h (e.symm j))
    rw [e.apply_symm_apply] at hh
    linarith
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem actual_range_bddAbove (hN : 0<N) (hp : 1≤p) (hK : 0<K)
    (a b r q : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hq : 0≤q) (hq1 : q≤1) (x : Vector N)
    [Nonempty (GaussianFixedBaseForkConcentration.LeafDomain N K x r q)]
    (J : ForkDisorder N p K) :
    BddAbove (Set.range (fun y : GaussianFixedBaseForkConcentration.LeafDomain N K x r q =>
      averagedIncrement a b x y.val J)) := by
  let A : GaussianFixedBaseForkConcentration.LeafDomain N K x r q→
      (ForkTensor N p K→L[ℝ]ℝ) := fun y => forkDual a b x y.val
  have hA : ∀y,‖A y‖≤(⟨Real.sqrt (1/((K:ℝ)*N)),Real.sqrt_nonneg _⟩:ℝ≥0) :=
    fun y => orthogonal_forkDual_norm_le hN hp hK a b ha hab hb x y.val r q hr hq hq1 y.property
  have hh := GaussianDualSupConcentration.range_bddAbove A hA (tensorInputs J)
  change BddAbove (Set.range (fun y : GaussianFixedBaseForkConcentration.LeafDomain N K x r q =>
    forkDual a b x y.val (tensorInputs J))) at hh
  simpa only [forkDual_tensorInputs] using hh

/-- The same original fork disorder is used at both nearby basepoints. -/
theorem actual_fixedBase_supremum_transport_bound (hN : 0<N) (hp : 1≤p)
    (hK : 0<K) (hKN : K<N) (a b r q : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hrq : r≤q) (hq1 : q≤1) (x x' : Vector N)
    (hxnorm : ‖x‖^2=(N:ℝ)*r) (hxx' : ‖x‖=‖x'‖) (hx : x≠0)
    (J : ForkDisorder N p K) (R : ℝ) (hR : 0≤R)
    (hland : ∀i,landscapeNorm N p (J i)≤R) :
    |GaussianFixedBaseForkConcentration.supremum a b r q x J-
      GaussianFixedBaseForkConcentration.supremum a b r q x' J|≤
      12*(p:ℝ)*R*‖x-x'‖/‖x‖ := by
  have hxnorm' : ‖x'‖^2=(N:ℝ)*r := by rw [←hxx'];exact hxnorm
  letI := OrthogonalForkNonempty.leafDomain_nonempty hKN x r q hr hrq hxnorm
  letI := OrthogonalForkNonempty.leafDomain_nonempty hKN x' r q hr hrq hxnorm'
  let e := forkEquiv (K:=K) x x' hxx' r q
  have hbb := actual_range_bddAbove hN hp hK a b r q ha hab hb hr (hr.trans hrq) hq1 x J
  have hbb' := actual_range_bddAbove hN hp hK a b r q ha hab hb hr (hr.trans hrq) hq1 x' J
  apply csSup_transport_abs_le e _ _ hbb hbb'
  intro y
  exact actual_averagedIncrement_transport_bound hN hK a b ha hab hb x x' hxx' hx
    y.val r q (hrq.trans hq1) hq1 y.property J R hR hland

end SphericalAging.OrthogonalForkSupremumTransport
