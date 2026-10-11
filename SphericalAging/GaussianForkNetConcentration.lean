module

public import SphericalAging.OrthogonalForkNonempty
public import SphericalAging.NormalizedSphereNets

public section

/-! The genuine finite-net stage of Huang--Sellke Lemma 3.2. Both the
sphere net and every fixed-base Gaussian tail are constructed internally. -/
noncomputable section
namespace SphericalAging.GaussianForkNetConcentration
open Set MeasureTheory FiniteModel GaussianOrthogonalForkCovariance
open OrthogonalForkNonempty NormalizedSphereNets

theorem exists_sphere_net_concentration {N p K : ℕ} (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (a b r q : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hrq : r≤q) (hq1 : q≤1) (η ε : ℝ) (hη : 0<η) (hε : 0≤ε) :
    ∃S : Finset (Vector N),
      (∀x∈S,‖x‖^2=(N:ℝ)*r) ∧
      (∀x : Vector N,‖x‖^2=(N:ℝ)*r→∃y∈S,dist x y≤η*Real.sqrt (N:ℝ)) ∧
      (S.card:ℝ)≤(1+2/η)^N ∧
      (forkLaw N p K).real {J | ∃x∈S,ε≤|GaussianFixedBaseForkConcentration.supremum a b r q x J-
        ∫J',GaussianFixedBaseForkConcentration.supremum a b r q x J' ∂forkLaw N p K|}≤
        2*(1+2/η)^N*Real.exp (-((K:ℝ)*N)*ε^2/(2*(Real.pi/2)^2)) := by
  classical
  obtain ⟨S,hS,hcov,hcard⟩ := normalized_sphere_net N r hr (hrq.trans hq1) hη
  refine ⟨S,hS,hcov,hcard,?_⟩
  let F := fun x J => GaussianFixedBaseForkConcentration.supremum (p:=p) (K:=K) a b r q x J-
    ∫J',GaussianFixedBaseForkConcentration.supremum a b r q x J' ∂forkLaw N p K
  have hset : {J | ∃x∈S,ε≤|F x J|}=⋃x∈S,{J | ε≤|F x J|} := by
    ext J
    simp
  change (forkLaw N p K).real {J | ∃x∈S,ε≤|F x J|}≤_
  rw [hset]
  calc
    _≤∑x∈S,(forkLaw N p K).real {J | ε≤|F x J|} := measureReal_biUnion_finset_le _ _
    _≤∑_x∈S,2*Real.exp (-((K:ℝ)*N)*ε^2/(2*(Real.pi/2)^2)) :=
      Finset.sum_le_sum (fun x hx => actual_fixedBaseFork_absolute_tail hp hK hKN a b r q ha hab hb hr
        hrq hq1 x (hS x hx) ε hε)
    _=(S.card:ℝ)*(2*Real.exp (-((K:ℝ)*N)*ε^2/(2*(Real.pi/2)^2))) := by simp
    _≤_ := (mul_le_mul_of_nonneg_right hcard
      (by positivity : 0≤2*Real.exp (-((K:ℝ)*N)*ε^2/(2*(Real.pi/2)^2)))).trans_eq (by ring)

end SphericalAging.GaussianForkNetConcentration
