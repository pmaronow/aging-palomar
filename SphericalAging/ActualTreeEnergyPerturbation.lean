module

public import SphericalAging.ActualAlgorithmTreeEnergy
public import SphericalAging.NormalizedFieldEnergyLipschitz

public section

/-! Perturbing the actual spatial leaves under the same original branching
disorder costs only their true distance and the true leaf landscape norms. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualTreeEnergyPerturbation
open FiniteModel AdaptiveGradientDisclosure GaussianLandscape
open ActualAlgorithmTreeEnergy NormalizedFieldEnergyLipschitz IndependentBranchingSuccess
open GaussianBranchingSuccess PartialVarianceBranchingCoefficients RegularTreeEnergyTelescoping
open RegularTreeGlobalToLocal HamiltonianTreeEnergy HamiltonianTreeFieldBand
open scoped BigOperators InnerProductSpace
variable {N p K : ℕ}

@[expose] def LeafDistance (ε : ℝ) :
    (d : ℕ)→TreeData (Vector N) K d→TreeData (Vector N) K d→Prop
  | 0,c,w => ‖(show Vector N from c)-(show Vector N from w)‖/Real.sqrt N≤ε
  | d+1,c,w => ∀i,LeafDistance ε d (c.2 i) (w.2 i)

@[expose] def LeafLandscapeBound (V : ℕ→ℝ) (C : ℝ) :
    (d : ℕ)→TensorSpace N p→TreeSample (TensorSpace N p) K d→Prop
  | 0,s,_ => landscapeNorm N p (partialDisorder V 0 s)≤C
  | d+1,s,z => ∀i,LeafLandscapeBound V C d
      (update (parentCoefficient V) (freshCoefficient V) d s (z i).1) (z i).2

theorem leafDistance_of_addresses (ε : ℝ) (d : ℕ)
    (c w : TreeData (Vector N) K d)
    (h : ∀a : Fin d→Fin K,‖leafAt d c a-leafAt d w a‖/Real.sqrt N≤ε) :
    LeafDistance ε d c w := by
  induction d with
  | zero => exact h (fun i => Fin.elim0 i)
  | succ d ih =>
    intro i;apply ih _ _
    intro a
    exact h (Fin.cons (α := fun _ : Fin (d+1) => Fin K) i a)

theorem actual_total_energy_perturbation (hN : 0<N) (hK : 0<K)
    (V : ℕ→ℝ) (h : Vector N) (C H ε : ℝ) (hH : 0≤H) (hh : ‖h‖≤Real.sqrt N*H)
    (d : ℕ) (c w : TreeData (Vector N) K d)
    (hc : AllLeaves (fun x => ‖x‖≤Real.sqrt N) d c)
    (hw : AllLeaves (fun x => ‖x‖≤Real.sqrt N) d w) (hd : LeafDistance ε d c w)
    (s : TensorSpace N p) (z : TreeSample (TensorSpace N p) K d)
    (hland : LeafLandscapeBound V C d s z) :
    totalLeafEnergy V d h c (s,z)≤totalLeafEnergy V d h w (s,z)+((p:ℝ)*C+H)*ε := by
  have hk : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  induction d generalizing s with
  | zero =>
    have hi := actual_energy_error hN (partialDisorder V 0 s) h c w C H ε hland hH hh hc hw hd
    have he := (abs_le.mp hi).2
    change Hamiltonian N p (partialDisorder V 0 s) c/(N:ℝ)+⟪h,c⟫_ℝ/(N:ℝ)≤
      (Hamiltonian N p (partialDisorder V 0 s) w/(N:ℝ)+⟪h,w⟫_ℝ/(N:ℝ))+_
    dsimp [energy] at he
    linarith
  | succ d ih =>
    rw [totalLeafEnergy_succ,totalLeafEnergy_succ]
    have hi (i : Fin K) := ih (c.2 i) (w.2 i) (hc i) (hw i) (hd i)
      (update (parentCoefficient V) (freshCoefficient V) d s (z i).1) (z i).2 (hland i)
    have hh' := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh'
    have hi' := div_le_div_of_nonneg_right hh' hk.le
    exact hi'.trans_eq (by rw [add_div,mul_div_cancel_left₀ _ hk.ne'])

end SphericalAging.ActualTreeEnergyPerturbation
