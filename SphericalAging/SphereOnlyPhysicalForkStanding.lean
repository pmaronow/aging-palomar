module

public import SphericalAging.SphereOnlyPhysicalForkRealization
public import SphericalAging.PhysicalForkStanding

public section

/-! Construction of the literal physical finite-fork standing family on
a genuine Fisher dimension subsequence. Its global time quantifier is
kept explicit: all diverging waiting sequences must realize the common
stationary profile. This intermediate interface can be discharged after
the whole translated-family selection theorem. -/
noncomputable section
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereOnlyPhysicalForkStanding
open MeasureTheory ProbabilityTheory Filter Set FiniteModel HardSphereDynamics
open CKSpecification StationaryClusterInputs ActualSphereOnlyForkRealization
open PhysicalForkConstruction PhysicalForkPastLaw PhysicalForkWaitingTransfer
open SphereOnlyPhysicalForkRealization PhysicalForkNormTheorem ForkParameterBounds
open PhysicalForkCenterConcentration AnnealedHamiltonianEnergyStein
open scoped NNReal Topology

/-- The exact all-time input necessary for the stronger standing interface.
It asserts translated stationary clusters, rather than any fork error,
energy limit, concentration, ceiling, or approximation conclusion. -/
@[expose] def AllRealizingClusters {p : ℕ} {β : ℝ≥0} {d : CKData}
    (h : CKEquations p β d) (c r : ℝ→ℝ) (ell q : ℝ) : Prop :=
  ∀t : ℕ→ℝ≥0,(∀n,0<t n)→Tendsto (fun n => (t n:ℝ)) atTop atTop→
    Cluster h (fun n => (t n:ℝ)) c r ell q

/-- Every field of the physical standing family is constructed from the
actual branch SDE and native sphere Fisher extraction. -/
theorem of_all_realizing_clusters {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j)
    (hTop : Tendsto dim atTop atTop) (F : Realization h dim)
    {c r : ℝ→ℝ} {ell q : ℝ} (hAll : AllRealizingClusters h c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    Nonempty (PhysicalForkStanding.Forks (fun j => dim (F.extraction j)) p β
      ((ell-1)/((p:ℝ)*(β:ℝ))) c r) := by
  let D : ℕ→ℕ := fun j => dim (F.extraction j)
  let t₀ : ℕ→ℝ≥0 := fun n => (n:ℝ≥0)+1
  have ht₀ : Tendsto (fun n => (t₀ n:ℝ)) atTop atTop := by
    have ht : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    simpa only [t₀,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,
      Nat.cast_add,Nat.cast_one] using ht
  have hpos₀ : ∀n,0<t₀ n := fun n => by dsimp [t₀];positivity
  have H₀ := hAll t₀ hpos₀ ht₀
  let B : ∀K (L T : ℝ≥0),∀j,Fin K→WienerForkTransfer.ForkSpace (D j) p K→Vector (D j) :=
    fun K L T j => branch (N:=D j) (p:=p) (K:=K) β (T+L) T
  refine ⟨{
    branches := B,
    branch_law:=fun K L T j => fork_joint_law β (T+L) T,
    energy_limit:=?_,
    concentration_limit:=?_,
    ceiling:=?_,
    approximation:=?_,
    past_law:=fun K L T j s hs => physical_past_law β (T+L) T s hs}⟩
  · intro K hK L t hpos ht
    have H := hAll t hpos ht
    have ho := proposition_10_4_realization H (fun n => (t n).coe_nonneg)
      dim hDim hTop F hThreshold (by omega : 0<K) L
    simpa only [Real.toNNReal_coe] using ho.2.2.1
  · intro K hK L t hpos ht
    have H := hAll t hpos ht
    have ho := proposition_10_4_realization H (fun n => (t n).coe_nonneg)
      dim hDim hTop F hThreshold (by omega : 0<K) L
    simpa only [Real.toNNReal_coe] using ho.2.2.2.2.1
  · intro K hK L
    exact (proposition_10_4_realization H₀ (fun n => (t₀ n).coe_nonneg)
      dim hDim hTop F hThreshold (by omega : 0<K) L).2.2.2.1
  · intro K hK L T _hT ε _hε
    exact SphereOnlyPhysicalForkNormTheorem.actual_fork_approximation (by omega : 0<K)
      (by have := h.spin_ge_three;omega : 2≤p) D
      (fun j => by dsimp [D];have := hDim (F.extraction j);omega) (F.dimension_tendsto hTop) β
      (PhysicalForkCenterConcentration.forkNorm_pos_of_profile H₀.profile (by omega : 0<K) L) L T ε

end SphericalAging.SphereOnlyPhysicalForkStanding
