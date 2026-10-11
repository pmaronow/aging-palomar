module

public import SphericalAging.OrthogonalForkNonempty
public import SphericalAging.OrthogonalForkBasepointTransport
public import SphericalAging.TensorHamiltonianRotation

public section

/-! Exact constancy of the expected fixed-base fork supremum on each
radius sphere, from the literal orthogonal invariance of every original
Gaussian disorder block. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianForkBasepointExpectation
open Set MeasureTheory ProbabilityTheory FiniteModel
open GaussianOrthogonalForkCovariance GaussianFixedBaseForkConcentration OrthogonalForkNonempty
open TensorHamiltonianRotation OrthogonalForkBasepointTransport
variable {N p K : ℕ}

@[expose] def rotatedFork (O : Vector N≃ₗᵢ[ℝ]Vector N) (J : ForkDisorder N p K) : ForkDisorder N p K :=
  fun i => rotatedDisorder O (J i)

theorem rotatedFork_hasLaw (O : Vector N≃ₗᵢ[ℝ]Vector N) :
    HasLaw (rotatedFork (p:=p) (K:=K) O) (forkLaw N p K) (forkLaw N p K) := by
  refine ⟨(Measurable.of_eval (fun i => (rotatedDisorder_measurable O).comp
    (measurable_pi_apply i))).aemeasurable,?_⟩
  change (Measure.pi (fun _ : Option (Fin K) => disorderLaw N p)).map
    (fun J i => rotatedDisorder O (J i))=_
  rw [Measure.pi_map_pi (fun _ => (rotatedDisorder_hasLaw (p:=p) O).aemeasurable)]
  simp_rw [(rotatedDisorder_hasLaw (p:=p) O).map_eq]
  rfl

private def leafRotation (O : Vector N≃ₗᵢ[ℝ]Vector N) (x : Vector N) (r q : ℝ) :
    LeafDomain N K x r q≃LeafDomain N K (O x) r q where
  toFun y := ⟨fun i => O (y.val i),fork_map O y.property⟩
  invFun y := ⟨fun i => O.symm (y.val i),by
    have hh := fork_map O.symm y.property
    simpa only [O.symm_apply_apply] using hh⟩
  left_inv y := by apply Subtype.ext;funext i;exact O.symm_apply_apply _
  right_inv y := by apply Subtype.ext;funext i;exact O.apply_symm_apply _

theorem averagedIncrement_rotated (O : Vector N≃ₗᵢ[ℝ]Vector N) (a b : ℝ)
    (x : Vector N) (y : Fin K→Vector N) (J : ForkDisorder N p K) :
    averagedIncrement a b (O x) (fun i => O (y i)) (rotatedFork O J)=averagedIncrement a b x y J := by
  simp only [averagedIncrement,increment,sharedIncrement,block,rotatedFork,Hamiltonian_rotated]

theorem supremum_rotated (O : Vector N≃ₗᵢ[ℝ]Vector N) (a b r q : ℝ)
    (x : Vector N) (J : ForkDisorder N p K) :
    supremum a b r q (O x) (rotatedFork O J)=supremum a b r q x J := by
  let e := leafRotation (K:=K) O x r q
  have he := e.surjective.range_comp (fun y : LeafDomain N K (O x) r q =>
    averagedIncrement a b (O x) y.1 (rotatedFork O J))
  change sSup (Set.range (fun y : LeafDomain N K (O x) r q =>
    averagedIncrement a b (O x) y.1 (rotatedFork O J)))=_
  rw [←he]
  change sSup (Set.range (fun y : LeafDomain N K x r q =>
    averagedIncrement a b (O x) (fun i => O (y.val i)) (rotatedFork O J)))=_
  simp_rw [averagedIncrement_rotated]
  rfl

theorem supremum_integrable (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (a b r q : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hrq : r≤q) (hq1 : q≤1) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*r) :
    Integrable (supremum (p:=p) (K:=K) a b r q x) (forkLaw N p K) := by
  letI := leafDomain_nonempty hKN x r q hr hrq hx
  have hI := (supremum_centered_hasSubgaussianMGF (by omega) hp hK a b r q ha hab hb hr
    (hr.trans hrq) hq1 x).integrable
  convert hI.add (integrable_const (∫J,supremum a b r q x J ∂forkLaw N p K)) using 1
  funext J
  exact (sub_add_cancel _ _).symm

theorem expectation_rotated (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (a b r q : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hrq : r≤q) (hq1 : q≤1) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*r)
    (O : Vector N≃ₗᵢ[ℝ]Vector N) :
    (∫J,supremum a b r q x J ∂forkLaw N p K)=∫J,supremum a b r q (O x) J ∂forkLaw N p K := by
  have hI := supremum_integrable hp hK hKN a b r q ha hab hb hr hrq hq1 (O x)
    (by simpa only [O.norm_map] using hx)
  have hh := (rotatedFork_hasLaw (p:=p) (K:=K) O).integral_comp hI.aestronglyMeasurable
  simp only [Function.comp_def] at hh
  simpa only [supremum_rotated] using hh

theorem expectation_equal_norm (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (a b r q : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hrq : r≤q) (hq1 : q≤1) (x x' : Vector N) (hx : ‖x‖^2=(N:ℝ)*r)
    (hxx' : ‖x‖=‖x'‖) :
    (∫J,supremum a b r q x J ∂forkLaw N p K)=∫J,supremum a b r q x' J ∂forkLaw N p K := by
  have hh := expectation_rotated hp hK hKN a b r q ha hab hb hr hrq hq1 x hx
    (PredictableHouseholder.update x x')
  rwa [PredictableHouseholder.update_equal_norm hxx'] at hh

end SphericalAging.GaussianForkBasepointExpectation
