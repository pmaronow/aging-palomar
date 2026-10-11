module

public import SphericalAging.ScalarSourceSecondMoment
public import SphericalAging.VectorSDEFourthMoment

public section

/-! Fourth moments from the true quartic generator production of an
arbitrary bounded vector Itô process. The forcing may be unbounded in
probability; only its genuine integrated fourth production is used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.VectorSourceFourthMoment
open HardSphereDynamics PredictableDriftTime RadialUniqueness VectorIto
  LinearSDEFourthMoment SharpRadialMoment ScalarSourceSecondMoment
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def fourthProduction (x : State N) (a : Fin N→ℝ) (b : Fin N→Fin N→ℝ) : ℝ :=
  2*‖x‖^2*((∑i : Fin N,2*x i*a i)+(∑i : Fin N,∑j : Fin N,(b i j)^2))+
    ∑j : Fin N,(∑i : Fin N,2*x i*b i j)^2

theorem bounded_vector_source_fourthMoment (D : BrownianDriver N P F)
    (Y : ℝ≥0→Ω→State N) (hYa : StronglyAdapted F Y)
    (hYc : ∀omega,Continuous (fun t => Y t omega)) (R M S : ℝ≥0)
    (hYbound : ∀t omega,‖Y t omega‖≤R) (T : ℝ≥0)
    (Z0 : Ω→State N) (hZ0 : MemLp Z0 4 P)
    (G : ℝ≥0×Ω→ℝ) (hG : Integrable G (nonnegativeLebesgueMeasure.prod P))
    (hGpos : ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,0≤G q)
    (A : Fin N→PredictableProcessL2 F P) (U : Fin N→Fin N→PredictableProcessL2 F P)
    (μ : Fin N→ℝ≥0→Ω→ℝ)
    (hA : ∀i,(A i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P] Function.uncurry (μ i))
    (hμ : ∀i,Measurable (Function.uncurry (μ i)))
    (hμint : ∀i t,∀ᵐomega∂P,IntegrableOn (fun s => μ i s omega) (Ioc 0 t) nonnegativeLebesgueMeasure)
    (hUb : ∀i j,∀ᵐq∂nonnegativeLebesgueMeasure.prod P,‖(U i j : TimeProcessL2 P) q‖≤S)
    (hUsupport : ∀i j,∀ᵐq∂nonnegativeLebesgueMeasure.prod P,
      q.1∉Ioc 0 T→(U i j : TimeProcessL2 P) q=0)
    (hproduction : ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,q.1∈Ioc 0 T→
      fourthProduction (Y q.1 q.2) (fun i => (A i : TimeProcessL2 P) q)
        (fun i j => (U i j : TimeProcessL2 P) q)≤(M:ℝ)*‖Y q.1 q.2‖^4+G q)
    (hinitial : ∀ᵐomega∂P,Y 0 omega=Z0 omega)
    (heq : ∀i t,t≤T→(fun omega => Y t omega i)=ᵐ[P] fun omega =>
      Y 0 omega i+integratedDrift (μ i) t omega+vectorProcess D (U i) t omega)
    (t : ℝ≥0) (ht : t≤T) :
    (∫omega,‖Y t omega‖^4∂P)≤
      ((∫omega,‖Z0 omega‖^4∂P)+(∫q,G q∂nonnegativeLebesgueMeasure.prod P))*Real.exp ((M:ℝ)*t) := by
  let X := SpherePreservation.coordinates Y
  have hXa := SpherePreservation.coordinates_adapted hYa
  have hXc := SpherePreservation.coordinates_continuous (P:=P) hYc
  have hXbound := SpherePreservation.coordinates_bound hYbound
  let B := RadialProcess.radialDrift A U X hXa hXc R hXbound S hUb T
  let V := RadialProcess.radialNoise U X hXa hXc R hXbound T
  let Z : ℝ≥0→Ω→ℝ := fun s omega => ‖Y s omega‖^2
  have hZa : StronglyAdapted F Z := fun s => (hYa s).norm.pow 2
  have hZc : ∀ᵐomega∂P,Continuous (fun s => Z s omega) :=
    .of_forall (fun omega => (hYc omega).norm.pow 2)
  have hZb : ∀s omega,‖Z s omega‖≤(R^2:ℝ≥0) := by
    intro s omega
    simpa only [Z,Real.norm_of_nonneg (sq_nonneg _),NNReal.coe_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (hYbound s omega) 2
  have hsum (s : ℝ≥0) (omega : Ω) : (∑i : Fin N,X i s omega^2)=‖Y s omega‖^2 := by
    simpa only [X,SpherePreservation.coordinates,real_inner_self_eq_norm_sq] using coordinate_square_sum (Y s omega)
  have hZe : ∀s,s≤T→∀ᵐomega∂P,Z s omega=‖Z0 omega‖^2+driftVersion B s s omega+
      (vectorProcessLp D V s : Ω→ℝ) omega := by
    intro s hs
    have hh := LocalRadialIto.quadratic_class_equation_on D A U X μ hXa hXc R hXbound S hUb T s hs
      hA hμ hμint heq
    filter_upwards [hh,hinitial] with omega he h0
    rw [hsum s omega,hsum 0 omega,h0] at he
    dsimp only [Z]
    linarith
  have hBsupport : ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,q.1∉Ioc 0 T→(B : TimeProcessL2 P) q=0 := by
    have hus := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hUsupport i))
    filter_upwards [RadialProcess.radialDrift_coe A U X hXa hXc R hXbound S hUb T,hus] with q hb hu
    intro hq
    rw [hb]
    simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_false,zero_mul,Finset.sum_const_zero,zero_add]
    simp_rw [hu _ _ hq,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero]
  have hVb : ∀j,∀ᵐq∂nonnegativeLebesgueMeasure.prod P,
      ‖(V j : TimeProcessL2 P) q‖≤(2*N*R*S:ℝ≥0) := by
    intro j
    filter_upwards [RadialProcess.radialNoise_coe U X hXa hXc R hXbound T j,
      ae_all_iff.mpr (fun i => hUb i j)] with q hv hu
    rw [hv]
    by_cases hq : q.1∈Ioc 0 T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,RadialItoRepresentation.twiceState]
      calc
        _≤∑i : Fin N,‖2*X i q.1 q.2*(U i j : TimeProcessL2 P) q‖ := norm_sum_le _ _
        _≤∑_i : Fin N,2*(R:ℝ)*S := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_mul,norm_mul,show ‖(2:ℝ)‖=2 by norm_num]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hXbound i q.1 q.2) (by norm_num)) (hu i)
            (norm_nonneg _) (by positivity)
        _=(2*N*R*S:ℝ≥0) := by simp;ring
    · simp [FourPapersCommon.continuousAdaptedTimeCut,hq]
      positivity
  have hp : ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,q.1∈Ioc 0 T→
      2*Z q.1 q.2*(B : TimeProcessL2 P) q+∑j : Fin N,((V j : TimeProcessL2 P) q)^2≤
        (M:ℝ)*(Z q.1 q.2)^2+G q := by
    have hv := ae_all_iff.mpr (fun j => RadialProcess.radialNoise_coe U X hXa hXc R hXbound T j)
    filter_upwards [RadialProcess.radialDrift_coe A U X hXa hXc R hXbound S hUb T,hv,hproduction] with q hb hv hp
    intro hq
    have he (j : Fin N) : (V j : TimeProcessL2 P) q=
        ∑i : Fin N,2*(Y q.1 q.2) i*(U i j : TimeProcessL2 P) q := by
      rw [hv j]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,RadialItoRepresentation.twiceState,
        X,SpherePreservation.coordinates]
    simp_rw [he]
    rw [hb]
    simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,RadialItoRepresentation.twiceState,
      X,SpherePreservation.coordinates,Z]
    simpa only [fourthProduction,←pow_mul,show 2*2=4 from rfl] using hp hq
  have hz0 : MemLp (fun omega => ‖Z0 omega‖^2) 2 P := by
    apply (memLp_two_iff_integrable_sq (hZ0.aestronglyMeasurable.norm.pow 2)).mpr
    simpa only [Pi.pow_apply,←pow_mul,show 2*2=4 from rfl] using hZ0.integrable_norm_pow'
  have hh := scalar_equation_source_secondMoment D Z hZa hZc (R^2) M (2*N*R*S) hZb T
    (fun omega => ‖Z0 omega‖^2) hz0 G hG hGpos B V hBsupport hp hVb hZe t ht
  simpa only [meanSquare,Z,←pow_mul,show 2*2=4 from rfl] using hh

end SphericalAging.VectorSourceFourthMoment
