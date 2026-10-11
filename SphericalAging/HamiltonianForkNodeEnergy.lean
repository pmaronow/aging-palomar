module

public import SphericalAging.RegularTreeEnergyTelescoping
public import SphericalAging.GaussianForkUniformEvents
public import SphericalAging.OrthogonalForkSupremumTransport

public section

/-! The literal local Hamiltonian increment used in the tree-energy
telescoping argument. Its relation to the actual orthogonal-fork supremum
is derived from the constructed coupled disorder coefficients. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianForkNodeEnergy
open Set MeasureTheory FiniteModel GaussianOrthogonalForkCovariance GaussianForkUniformEvents
open RegularTreeEnergyTelescoping OrthogonalForkSupremumTransport
open scoped BigOperators
variable {N p K : ℕ}

@[expose] def parentDisorder (a : ℝ) (J : ForkDisorder N p K) : Disorder N p := Real.sqrt a • J none
@[expose] def childDisorder (a b : ℝ) (J : ForkDisorder N p K) (i : Fin K) : Disorder N p :=
  Real.sqrt a • J none+Real.sqrt (b-a) • J (some i)

theorem Hamiltonian_disorder_add (J J' : Disorder N p) (x : Vector N) :
    Hamiltonian N p (J+J') x=Hamiltonian N p J x+Hamiltonian N p J' x := by
  simp only [←hamiltonianCLM_apply,(hamiltonianCLM x).map_add]

theorem Hamiltonian_disorder_smul (c : ℝ) (J : Disorder N p) (x : Vector N) :
    Hamiltonian N p (c • J) x=c*Hamiltonian N p J x := by
  simp only [←hamiltonianCLM_apply,(hamiltonianCLM x).map_smul,smul_eq_mul]

theorem coupled_increment_eq (a b : ℝ) (x : Vector N) (y : Fin K→Vector N)
    (J : ForkDisorder N p K) (i : Fin K) :
    Hamiltonian N p (childDisorder a b J i) (y i)-Hamiltonian N p (parentDisorder a J) x=
      increment a b x y i J := by
  simp only [childDisorder,parentDisorder,Hamiltonian_disorder_add,Hamiltonian_disorder_smul,
    increment,sharedIncrement,block]
  ring

@[expose] def nodeEnergyTree (a b : ℝ) (x : Vector N) (y : Fin K→Vector N)
    (J : ForkDisorder N p K) : TreeData ℝ K 1 :=
  (Hamiltonian N p (parentDisorder a J) x/(N:ℝ),
    fun i => Hamiltonian N p (childDisorder a b J i) (y i)/(N:ℝ))

theorem node_localEdge_eq_actual_increment (hN : 0<N) (hK : 0<K)
    (a b : ℝ) (x : Vector N) (y : Fin K→Vector N) (J : ForkDisorder N p K) :
    localEdge 1 (nodeEnergyTree a b x y J)=averagedIncrement a b x y J := by
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hk : (K:ℝ)≠0 := by exact_mod_cast hK.ne'
  simp only [nodeEnergyTree,localEdge,root]
  rw [←Finset.sum_div]
  unfold averagedIncrement
  simp_rw [←coupled_increment_eq]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp [hn,hk]

theorem actual_node_energy_upper_on_goodEvent (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (a b r q ε : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hrq : r≤q) (hq1 : q≤1) (x : Vector N) (y : Fin K→Vector N)
    (hy : OrthogonalFork x y r q) (J : ForkDisorder N p K) (hJ : J∈goodEvent N p K a b r q ε) :
    localEdge 1 (nodeEnergyTree a b x y J)≤
      (∫J',GaussianFixedBaseForkConcentration.supremum a b r q x J' ∂forkLaw N p K)+ε := by
  have hN : 0<N := by omega
  letI : Nonempty (GaussianFixedBaseForkConcentration.LeafDomain N K x r q) := ⟨⟨y,hy⟩⟩
  have hinc : averagedIncrement a b x y J≤GaussianFixedBaseForkConcentration.supremum a b r q x J :=
    le_csSup (actual_range_bddAbove hN hp hK a b r q ha hab hb hr (hr.trans hrq) hq1 x J)
      (Set.mem_range_self (⟨y,hy⟩ : GaussianFixedBaseForkConcentration.LeafDomain N K x r q))
  have hh := (le_abs_self _).trans (hJ x hy.base_norm)
  rw [node_localEdge_eq_actual_increment hN hK]
  linarith

end SphericalAging.HamiltonianForkNodeEnergy
