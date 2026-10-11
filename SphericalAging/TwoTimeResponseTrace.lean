module

public import SphericalAging.TwoTimeResponseMatrix

public section

/-! The scalar finite-N response is the normalized expected trace of the
constructed physical two-time matrix. Integrability and its literal
finite-N diagonal (N-1)/N follow from the actual response and tangent
projection, rather than a stipulated CK diagonal. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.TwoTimeResponseTrace
open HardSphereDynamics LocalSDE TwoTimePhysicalResponse TwoTimeResponseMatrix
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Normalized expected trace of an actual terminal L² response matrix. -/
@[expose] def normalizedTrace (M : State N →L[ℝ] Lp (State N) 2 P) : ℝ :=
  ∫ omega,(∑ i : Fin N,inner ℝ (basisVector i) ((M (basisVector i)) omega))/(N : ℝ) ∂P

lemma normalizedTrace_integrable (M : State N →L[ℝ] Lp (State N) 2 P) :
    Integrable (fun omega => (∑ i : Fin N,inner ℝ (basisVector i) ((M (basisVector i)) omega))/(N : ℝ)) P := by
  have hi (i : Fin N) : Integrable (fun omega => inner ℝ (basisVector i) ((M (basisVector i)) omega)) P := by
    exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      ((Lp.memLp (M (basisVector i))).continuousLinearMap_comp (innerSL ℝ (basisVector i)))
  exact (integrable_finsetSum Finset.univ (fun i _ => hi i)).div_const _

lemma projection_basis_trace_onSphere (hN : N ≠ 0) (x : State N) (hx : OnSphere x) :
    (∑ i : Fin N,inner ℝ (basisVector i) (projection x (basisVector i)))=(N : ℝ)-1 := by
  calc
    _ = projectionTraceSquare x := by
      unfold projectionTraceSquare
      apply Finset.sum_congr rfl
      intro i _
      have h := projection_self_adjoint x (basisVector i) (projection x (basisVector i))
      rw [projection_idempotent hN x (basisVector i) hx] at h
      exact h.symm
    _ = _ := projectionTraceSquare_onSphere hN x hx

lemma projectedTerminal_normalizedTrace (hN : N ≠ 0)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X) (s : ℝ≥0)
    (hSphere : ∀ᵐ omega ∂P,OnSphere (X s omega)) :
    normalizedTrace (projectedTerminalOperator hN X hXa s hSphere)=kappa N := by
  have hproj : ∀ᵐ omega ∂P,∀ i : Fin N,
      (projectedTerminalOperator hN X hXa s hSphere (basisVector i)) omega=
        projection (X s omega) (basisVector i) :=
    ae_all_iff.mpr (fun i => (projectedInitial_memLp hN hXa s (basisVector i) hSphere).coeFn_toLp)
  calc
    _ = ∫ _omega : Ω,kappa N ∂P := by
      unfold normalizedTrace
      apply integral_congr_ae
      filter_upwards [hproj,hSphere] with omega hp hx
      simp only [hp]
      rw [projection_basis_trace_onSphere hN (X s omega) hx]
      rfl
    _ = _ := by simp

/-- The scalar response has the exact finite-N physical diagonal. -/
theorem response_diagonal (hN : N ≠ 0) (D : BrownianDriver N P F)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) {Kb Ks : ℝ≥0}
    (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (s T : ℝ≥0) (hSphere : ∀ᵐ omega ∂P,OnSphere (X s omega))
    (hSpherePath : ∀ᵐ omega ∂P,∀ t,t ≤ s+T → OnSphere (X t omega)) :
    normalizedTrace (terminalResponse hN D X hXa hXc β J R hR hb hs s T hSphere 0)=kappa N := by
  rw [terminalResponse_initial hN D X hXa hXc β J R hR hb hs s T hSphere hNR hSpherePath]
  exact projectedTerminal_normalizedTrace hN X hXa s hSphere

end SphericalAging.TwoTimeResponseTrace
