module

public import SphericalAging.HamiltonianForkExpectedEdgeUpper
public import SphericalAging.HamiltonianTreeEnergy

public section

/-! Actual finite branching-energy ceiling from the literal expected fork edges.
Partial-variance weights and their order are derived from the true schedules. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianTreeExpectedEdgeUpper
open Set MeasureTheory ProbabilityTheory FiniteModel
open GaussianOrthogonalForkCovariance HamiltonianForkExpectedEdgeUpper HamiltonianTreeEnergy
open scoped BigOperators
variable {N p K : ℕ}

 theorem expectedEdge_upper (hN : 0<N) (hp : 2≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j) (d : ℕ) :
    expectedEdge (N:=N) (p:=p) (K:=K) hN V Q d≤
      Real.sqrt ((Q d-Q (d+1))*(V d*(p:ℝ)*(Q d)^(p-1)-V (d+1)*(p:ℝ)*(Q (d+1))^(p-1)))+
      Real.sqrt (V (d+1)*(p:ℝ)*(Q (d+1))^(p-1)*(Q d-Q (d+1))/K) :=
  actual_expected_edge_upper hN hp hK hKN (hV _).1 (hVm _) (hV _).2
    (hQ _).1 (hQm _) (hQ _).2 _ (referenceBase_norm hN _ (hQ _).1)

 theorem expectedEdge_upper_uniform_remainder (hN : 0<N) (hp : 2≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j) (d : ℕ) :
    expectedEdge (N:=N) (p:=p) (K:=K) hN V Q d≤
      Real.sqrt ((Q d-Q (d+1))*(V d*(p:ℝ)*(Q d)^(p-1)-V (d+1)*(p:ℝ)*(Q (d+1))^(p-1)))+
      Real.sqrt ((p:ℝ)/K) := by
  apply (expectedEdge_upper hN hp hK hKN V Q hV hVm hQ hQm d).trans
  apply add_le_add le_rfl
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg K)
  have hpw : 0≤(Q (d+1))^(p-1) := pow_nonneg (hQ _).1 _
  have hdiff : 0≤Q d-Q (d+1) := sub_nonneg.mpr (hQm _)
  have hdiff1 : Q d-Q (d+1)≤1 := (sub_le_self _ (hQ _).1).trans (hQ _).2
  calc
    V (d+1)*(p:ℝ)*(Q (d+1))^(p-1)*(Q d-Q (d+1))≤
        1*(p:ℝ)*1*1 := by
      gcongr
      · exact (hV _).2
      · exact pow_le_one₀ (hQ _).1 (hQ _).2
    _ = _ := by ring

@[expose]  def discreteCeiling (p D : ℕ) (V Q : ℕ→ℝ) : ℝ :=
  ∑d∈Finset.range D,Real.sqrt ((Q d-Q (d+1))*
    (V d*(p:ℝ)*(Q d)^(p-1)-V (d+1)*(p:ℝ)*(Q (d+1))^(p-1)))

 theorem expectedEdge_sum_upper (hN : 0<N) (hp : 2≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j) (D : ℕ) :
    (∑d∈Finset.range D,expectedEdge (N:=N) (p:=p) (K:=K) hN V Q d)≤
      discreteCeiling p D V Q+(D:ℝ)*Real.sqrt ((p:ℝ)/K) := by
  have hh := Finset.sum_le_sum (s:=Finset.range D)
    (fun d _ => expectedEdge_upper_uniform_remainder hN hp hK hKN V Q hV hVm hQ hQm d)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,discreteCeiling] using hh

end SphericalAging.HamiltonianTreeExpectedEdgeUpper
