module

public import SphericalAging.SpaceTimeItoFormula
public import SphericalAging.PhysicalC2Ito
public import SphericalAging.WienerTrunkWeight

public section

/-! True space-time Itô representation for the physical Hamiltonian sphere SDE. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.PhysicalSpaceTimeIto
open HardSphereDynamics LocalSDE VectorIto AnnealedSDECore
open MultivariateTaylor SpaceTimeItoFormula PhysicalC2Ito
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Actual time integration of the coordinate drift and covariance is
precisely the actual Frechet coefficient generator integral. -/
lemma generator_integral_coordinates (β : ℝ) (J : FiniteModel.Disorder N p)
    {f : ℝ≥0 → State N → ℝ}
    (hD : Continuous (Function.uncurry (fun s => fderiv ℝ (f s))))
    (hH : Continuous (Function.uncurry (fun s => Hessian (f s)))) (g : ℝ≥0 → State N)
    (hg : Continuous g) (T : ℝ≥0) :
    (∑ i : Fin N,∫ s in Ioc (0 : ℝ≥0) T,fderiv ℝ (f s) (g s) (basisVector i)*
      hamiltonianDrift β J (g s) i ∂nonnegativeLebesgueMeasure)+
    (1/2 : ℝ)*(∑ i : Fin N,∑ k : Fin N,∫ s in Ioc (0 : ℝ≥0) T,
      Hessian (f s) (g s) (basisVector i) (basisVector k)*
        (∑ j : Fin N,noiseColumn (g s) j i*noiseColumn (g s) j k) ∂nonnegativeLebesgueMeasure)=
    ∫ s in Ioc (0 : ℝ≥0) T,SphereGenerator.coefficientGenerator β J (f s) (g s) ∂nonnegativeLebesgueMeasure := by
  let d (i : Fin N) (s : ℝ≥0) := fderiv ℝ (f s) (g s) (basisVector i)*hamiltonianDrift β J (g s) i
  let q (i k : Fin N) (s : ℝ≥0) := Hessian (f s) (g s) (basisVector i) (basisVector k)*
    (∑ j : Fin N,noiseColumn (g s) j i*noiseColumn (g s) j k)
  have hd (i : Fin N) : IntegrableOn (d i) (Ioc (0 : ℝ≥0) T) nonnegativeLebesgueMeasure := by
    have hc : Continuous (d i) := ((hD.clm_apply continuous_const).comp (continuous_id.prodMk hg)).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp ((contDiff_hamiltonianDrift β J).continuous.comp hg))
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hq (i k : Fin N) : IntegrableOn (q i k) (Ioc (0 : ℝ≥0) T) nonnegativeLebesgueMeasure := by
    have hnoise (j a : Fin N) : Continuous (fun s => noiseColumn (g s) j a) :=
      (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) a).comp ((contDiff_noiseColumn j).continuous.comp hg)
    have hc : Continuous (q i k) := (((hH.clm_apply continuous_const).clm_apply continuous_const).comp (continuous_id.prodMk hg)).mul
      (continuous_finsetSum Finset.univ (fun j _ => (hnoise j i).mul (hnoise j k)))
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hds := integrable_finsetSum Finset.univ (fun i _ => hd i)
  have hqs := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun k _ => hq i k))
  change (∑ i,∫ s in Ioc (0 : ℝ≥0) T,d i s ∂nonnegativeLebesgueMeasure)+
    (1/2 : ℝ)*(∑ i,∑ k,∫ s in Ioc (0 : ℝ≥0) T,q i k s ∂nonnegativeLebesgueMeasure)=_
  calc
    _ = (∫ s in Ioc (0 : ℝ≥0) T,∑ i,d i s ∂nonnegativeLebesgueMeasure)+
      (1/2 : ℝ)*(∫ s in Ioc (0 : ℝ≥0) T,∑ i,∑ k,q i k s ∂nonnegativeLebesgueMeasure) := by
        rw [integral_finsetSum _ (fun i _ => hd i),
          integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hq i k))]
        congr 2
        exact Finset.sum_congr rfl (fun i _ => (integral_finsetSum _ (fun k _ => hq i k)).symm)
    _ = ∫ s in Ioc (0 : ℝ≥0) T,((∑ i,d i s)+(1/2 : ℝ)*(∑ i,∑ k,q i k s)) ∂nonnegativeLebesgueMeasure := by
      have he := integral_add hds (hqs.const_mul (1/2 : ℝ))
      rw [he,integral_const_mul]
    _ = _ := integral_congr_ae (.of_forall (fun s => (generator_coordinates β J (f s) (g s)).symm))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Genuine general C² Itô formula for the actual sphere Hamiltonian SDE,
with the actual physical coefficient generator rather than an assumed PDE. -/
theorem physical_spaceTime_ito_formula (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (T : ℝ≥0) (hX : IsRandomStrongSolutionOn D
      (fun _ i x => hamiltonianDrift β J x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ ω ∂P,∀ s,OnSphere (X s ω)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f fdot : ℝ → State N → ℝ}
    (hf : ∀ s : ℝ≥0,ContDiff ℝ 2 (f s))
    (hF : Continuous (fun q : ℝ≥0 × State N => f q.1 q.2))
    (hD : Continuous (fun q : ℝ≥0 × State N => fderiv ℝ (f q.1) q.2))
    (hH : Continuous (fun q : ℝ≥0 × State N => Hessian (f q.1) q.2))
    (hTime : ∀ᵐ ω ∂P,
      (∀ r∈Icc (0 : ℝ) T,ContinuousOn (fun s => f s (X (Real.toNNReal r) ω)) (Icc 0 T)) ∧
      (∀ r∈Icc (0 : ℝ) T,∀ s∈Ioo (0 : ℝ) T,
        HasDerivAt (fun u => f u (X (Real.toNNReal r) ω)) (fdot s (X (Real.toNNReal r) ω)) s) ∧
      ContinuousOn (fun q : ℝ × ℝ => fdot q.1 (X (Real.toNNReal q.2) ω))
        (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T)) :
    ∃ V : Fin N → Fin N → PredictableProcessL2 F P,
      (∀ i j,(V i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut
          (fun s ω => fderiv ℝ (f s) (X s ω) (basisVector i)*noiseColumn (X s ω) j i) T) ∧
      ∀ᵐ ω ∂P,f T (X T ω)=f 0 (Z0 ω)+
        (∫ s in Ioc (0 : ℝ≥0) T,fdot s (X s ω) ∂nonnegativeLebesgueMeasure)+
        (∫ s in Ioc (0 : ℝ≥0) T,SphereGenerator.coefficientGenerator β J (f s) (X s ω) ∂nonnegativeLebesgueMeasure)+
        ∑ i : Fin N,(vectorIto D (V i) : Ω → ℝ) ω := by
  have hb : ∀ᵐ ω ∂P,∀ s,‖X s ω‖≤R := by
    filter_upwards [hXs] with ω hω
    intro s
    have hn : ‖X s ω‖^2=(N : ℝ) := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hω s
    nlinarith [norm_nonneg (X s ω)]
  obtain ⟨V,hV,he⟩ := strong_spaceTime_ito_formula D T hX
    (fun _ i j => (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp (contDiff_noiseColumn j).continuous)
    R hR hb hf hF hD hH hTime
  refine ⟨V,hV,?_⟩
  filter_upwards [he,hX.2.2.1] with ω heω hc
  have hg := generator_integral_coordinates β J (f := fun s => f s) hD hH (fun s => X s ω) hc T
  have ht := WienerTrunkWeight.nnreal_interval_integral T
    (fun s => fdot s (X (Real.toNNReal s) ω))
  simp only [Real.toNNReal_coe] at ht
  linarith

end SphericalAging.PhysicalSpaceTimeIto
