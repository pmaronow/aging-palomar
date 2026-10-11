module

public import SphericalAging.SphereEulerInterpolationAlgebra
public import SphericalAging.ElementaryTerminalFormula

public section

/-! Identification of the literal Euler interpolation with the actual
predictable drift and Itô terminal classes. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped BigOperators NNReal ENNReal InnerProductSpace
namespace SphericalAging.SphereEulerTerminalRepresentation
open HardSphereDynamics SphereEulerCoefficients SphereEulerPredictable
open SphereEulerInterpolationAlgebra ElementaryTerminalFormula TerminalLinearity
open TerminalStateRepresentation PredictableDriftTime PredictableItoTime
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
variable (hN : 0<N) (D : BrownianDriver N P F) (β h : ℝ≥0)
  (J : FiniteModel.Disorder N p) (x : State N) (M : ℕ)

@[expose] def stateClass (t : ℝ≥0) : Lp (State N) 2 P :=
  terminalClass D x (driftRows hN D β h J x M) (noiseRows hN D β h J x M) (grid h M) t

theorem driftRows_terminal_ae (i : Fin N) (t : ℝ≥0) :
    (driftTerminalOperator (grid h M) t (driftRows hN D β h J x M i) : Ω→ℝ)=ᵐ[P]
      fun omega => ∑k ∈ Finset.range M,
        (((min t (grid h (k+1)) : ℝ≥0):ℝ)-((min t (grid h k):ℝ≥0):ℝ))*driftField D β h J x k i omega := by
  have he (k : ℕ) (hk : k∈Finset.range M) :
      (driftTerminalOperator (grid h M) t
        (elementaryPredictable F (grid h k) (grid h (k+1)) (driftKnown hN D β h J x k i)) : Ω→ℝ)=ᵐ[P]
      fun omega => (((min t (grid h (k+1)) : ℝ≥0):ℝ)-((min t (grid h k):ℝ≥0):ℝ))*driftField D β h J x k i omega := by
    have hh := driftTerminal_elementary_ae (grid h k) (grid h (k+1)) (grid h M) t
      (grid_mono h (Nat.le_succ k)) (grid_mono h (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))
      (driftKnown hN D β h J x k i)
    have hz := boundedKnown_ae (P:=P) (grid h k) (driftField D β h J x k i)
      (driftField_stronglyMeasurable D β h J x k i) (driftCap β J) (driftField_bound hN D β h J x k i)
    filter_upwards [hh,hz] with omega hh hz
    change (driftKnown hN D β h J x k i : Ω→ℝ) omega=driftField D β h J x k i omega at hz
    rw [hh,hz]
    simp only [NNReal.coe_min]
  rw [driftRows,map_sum]
  have hs := (Lp.coeFn_fun_finsetSum (Finset.range M) (fun k => driftTerminalOperator (grid h M) t
    (elementaryPredictable F (grid h k) (grid h (k+1)) (driftKnown hN D β h J x k i))))
  have heall : ∀ᵐ omega ∂P,∀k,k∈Finset.range M →
      _ := ae_all_iff.mpr (fun k => by
        by_cases hk : k∈Finset.range M
        · exact (he k hk).mono (fun _ he _ => he)
        · exact .of_forall (fun _ hk' => False.elim (hk hk')))
  filter_upwards [hs,heall] with omega hs heall
  rw [hs]
  exact Finset.sum_congr rfl (fun k hk => heall k hk)

theorem noiseRows_terminal_ae (i j : Fin N) (t : ℝ≥0) :
    (itoTerminalOperator D j t (noiseRows hN D β h J x M i j) : Ω→ℝ)=ᵐ[P]
      fun omega => ∑k ∈ Finset.range M,noiseField D β h J x k i j omega*
        (D.coordinate j (min t (grid h (k+1))) omega-D.coordinate j (min t (grid h k)) omega) := by
  have he (k : ℕ) (_hk : k∈Finset.range M) :
      (itoTerminalOperator D j t
        (elementaryPredictable F (grid h k) (grid h (k+1)) (noiseKnown hN D β h J x k i j)) : Ω→ℝ)=ᵐ[P]
      fun omega => noiseField D β h J x k i j omega*
        (D.coordinate j (min t (grid h (k+1))) omega-D.coordinate j (min t (grid h k)) omega) := by
    have hh := itoTerminal_elementary_ae D j (grid h k) (grid h (k+1)) t
      (grid_mono h (Nat.le_succ k)) (noiseKnown hN D β h J x k i j)
    have hz := boundedKnown_ae (P:=P) (grid h k) (noiseField D β h J x k i j)
      (noiseField_stronglyMeasurable D β h J x k i j) noiseCap (noiseField_bound hN D β h J x k i j)
    filter_upwards [hh,hz] with omega hh hz
    change (noiseKnown hN D β h J x k i j : Ω→ℝ) omega=noiseField D β h J x k i j omega at hz
    rw [hh,hz]
  rw [noiseRows,map_sum]
  have hs := (Lp.coeFn_fun_finsetSum (Finset.range M) (fun k => itoTerminalOperator D j t
    (elementaryPredictable F (grid h k) (grid h (k+1)) (noiseKnown hN D β h J x k i j))))
  have heall : ∀ᵐ omega ∂P,∀k,k∈Finset.range M →
      _ := ae_all_iff.mpr (fun k => by
        by_cases hk : k∈Finset.range M
        · exact (he k hk).mono (fun _ he _ => he)
        · exact .of_forall (fun _ hk' => False.elim (hk hk')))
  filter_upwards [hs,heall] with omega hs heall
  rw [hs]
  exact Finset.sum_congr rfl (fun k hk => heall k hk)

theorem block_coordinate (k : ℕ) (t : ℝ≥0) (omega : Ω) (i : Fin N) :
    block D β h J x k t omega i=
      (((min t (grid h (k+1)) : ℝ≥0):ℝ)-((min t (grid h k):ℝ≥0):ℝ))*driftField D β h J x k i omega+
      ∑j : Fin N,noiseField D β h J x k i j omega*
        (D.coordinate j (min t (grid h (k+1))) omega-D.coordinate j (min t (grid h k)) omega) := by
  have hs := SphereEulerQuerySpan.noise_sum (clip (node D β h J x k omega))
    (stoppedIncrement D h k t omega)
  unfold block
  rw [←hs]
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,driftField]
  congr 1
  simp only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,noiseField,SphereEulerCoefficients.noise]
  apply Finset.sum_congr rfl
  intro j _
  have he : stoppedIncrement D h k t omega j=
      D.coordinate j (min t (grid h (k+1))) omega-D.coordinate j (min t (grid h k)) omega := by
    simp [stoppedIncrement,basisVector,Pi.single_apply,mul_ite]
  rw [he,mul_comm]

theorem stateClass_ae (t : ℝ≥0) : stateClass hN D β h J x M t=ᵐ[P] interpolant D β h J x M t := by
  have hd (i : Fin N) : driftVersion (driftRows hN D β h J x M i) (grid h M) t=ᵐ[P]
      fun omega => ∑k ∈ Finset.range M,
        (((min t (grid h (k+1)) : ℝ≥0):ℝ)-((min t (grid h k):ℝ≥0):ℝ))*driftField D β h J x k i omega :=
    (driftVersion_memLp _ _ _).coeFn_toLp.symm.trans (driftRows_terminal_ae hN D β h J x M i t)
  have hn (i j : Fin N) : itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
      (D.filtered j) (noiseRows hN D β h J x M i j) t=ᵐ[P]
      fun omega => ∑k ∈ Finset.range M,noiseField D β h J x k i j omega*
        (D.coordinate j (min t (grid h (k+1))) omega-D.coordinate j (min t (grid h k)) omega) :=
    (itoVersion_ae_eq (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) _ t).symm.trans
      (noiseRows_terminal_ae hN D β h J x M i j t)
  filter_upwards [terminalClass_ae D x (driftRows hN D β h J x M)
    (noiseRows hN D β h J x M) (grid h M) t,ae_all_iff.mpr hd,
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hn i))] with omega he hd hn
  change (terminalClass D x (driftRows hN D β h J x M) (noiseRows hN D β h J x M) (grid h M) t : Ω→State N) omega=_
  rw [he]
  apply PiLp.ext
  intro i
  simp only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,basisVector,PiLp.single_apply]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true,hd,hn]
  rw [interpolant,PiLp.add_apply,WithLp.ofLp_sum,Finset.sum_apply]
  simp_rw [block_coordinate D β h J x]
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  abel

end SphericalAging.SphereEulerTerminalRepresentation
