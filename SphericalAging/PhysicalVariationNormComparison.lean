module

public import SphericalAging.PhysicalVariationalEquation
public import SphericalAging.SphereRegularizedPhysicalGenerator
public import SphericalAging.PrefixVectorC2Representation
public import SphericalAging.IntegrableScalarItoComparison
public import SphericalAging.RegularizedNormIntegrability
public import SphericalAging.VectorNormComparisonLimits

public section

/-! Sharp physical tangent first moments in every N≥2. Smooth norm Itô,
true generator cancellation, Fubini and scalar Grönwall yield the estimate;
regularization tends to zero without a supplied response moment bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SphericalAging.PhysicalVariationNormComparison
open HardSphereDynamics FiniteModel LocalSDE PredictableDriftTime VectorIto
open SphereRegularizedNorm SphereRegularizedNormBounds SphereRegularizedPhysicalGenerator
open PrefixVectorC2Generator RegularizedNormIntegrability
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem norm_firstMoment (hN : 2≤N) (hp : 2≤p) (β : ℝ≥0) (J : Disorder N p)
    (D : BrownianDriver N P F) (X Y : ℝ≥0 → Ω → State N) (v : State N) (T : ℝ≥0)
    (hY : PhysicalVariationalEquation.IsStrongSolutionOn β J X D v Y T)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun s => X s ω))
    (hSphere : ∀ᵐ ω ∂P,∀ s,s≤T → OnSphere (X s ω))
    (hTangent : ∀ᵐ ω ∂P,∀ s,s≤T → ⟪X s ω,Y s ω⟫_ℝ=0)
    (hYfourth : ∀ s,s≤T → Integrable (fun ω => ‖Y s ω‖^4) P)
    (hYtime : Integrable (fun q => ‖LinearSDETimeFourthMoment.stateTimeCut Y T q‖^4)
      (nonnegativeLebesgueMeasure.prod P)) (t : ℝ≥0) (ht : t≤T) :
    (∫ ω,‖Y t ω‖ ∂P)≤‖v‖*Real.exp (((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t:ℝ)) := by
  obtain ⟨hYa,hYc,A,U,hA,hU,hEq⟩ := hY
  let sigma (i j : Fin N) (s : ℝ≥0) (ω : Ω) :=
    (fderiv ℝ (fun z : State N => noiseColumn z j) (X s ω) (Y s ω)) i
  have hprefix : ∀ s,s≤T → ∀ i : Fin N,(fun ω => Y s ω i)=ᵐ[P]
      fun ω => v i+driftVersion (A i) T s ω+vectorProcess D (U i) s ω := by
    intro s hs i
    have hd := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
      (fun r ω => (fderiv ℝ (hamiltonianDrift β J) (X r ω) (Y r ω)) i) T (A i) (hA i)
    have hn : driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s (U i j))=
        vectorProcessLp D (U i) s := CutoffSphere.driverItoMap_eq_vectorIto D _
    have he := hEq s hs i
    rw [hn] at he
    filter_upwards [he,hd,vectorProcessLp_ae_eq D (U i) s] with ω he hd hn
    rw [← hd s hs,hn] at he
    exact he
  have hsc : ∀ᵐ ω ∂P,∀ i j,Continuous (fun s => sigma i j s ω) := by
    filter_upwards [hXc,hYc] with ω hxc hyc
    intro i j
    have hc : Continuous (fderiv ℝ (fun z : State N => noiseColumn z j)) :=
      ((contDiff_noiseColumn j).fderiv_right (m:=0) (by simp)).continuous
    exact (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp ((hc.comp hxc).clm_apply hyc)
  let K : ℝ≥0 := ⟨(β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J,
    mul_nonneg (mul_nonneg β.coe_nonneg (sq_nonneg _)) (GaussianLandscape.landscapeNorm_nonnegative N p J)⟩
  have hYi : Integrable (fun ω => ‖Y t ω‖) P := by
    apply ((integrable_const (1:ℝ)).add (hYfourth t ht)).mono'
      (((hYa t).mono (F.le t)).aestronglyMeasurable.norm)
    exact .of_forall (fun ω => by rw [Real.norm_of_nonneg (norm_nonneg _)];exact norm_le_one_add_fourth _)
  apply VectorNormComparisonLimits.regularized_bound_limit v K t T (by omega) (∫ ω,‖Y t ω‖ ∂P)
  intro ε hε
  let f : State N → ℝ := regularizedNorm ε
  let L : ℝ≥0 := ⟨2/Real.sqrt ε,by positivity⟩
  let c : ℝ≥0 := ⟨Real.sqrt ε/(N:ℝ),by positivity⟩
  have hf : ContDiff ℝ 2 f := (regularizedNorm_contDiff hε).of_le (by simp)
  have hKf : ∀ i x,‖fderiv ℝ f x (basisVector i)‖≤(1:ℝ≥0) := by
    intro i x
    have hh := derivative_apply_norm_le hε x (basisVector i)
    simpa only [basisVector,EuclideanSpace.norm_single,norm_one,NNReal.coe_one] using hh
  have hLf : ∀ i k x,‖MultivariateTaylor.Hessian f x (basisVector i) (basisVector k)‖≤L := by
    intro i k x
    have hh := hessian_apply_norm_le hε x (basisVector i) (basisVector k)
    have hLe : (L:ℝ)=2/Real.sqrt ε := rfl
    rw [hLe]
    simpa only [f,MultivariateTaylor.Hessian,basisVector,EuclideanSpace.norm_single,norm_one,mul_one] using hh
  let G := generator f Y T A U
  have hGi : Integrable G (nonnegativeLebesgueMeasure.prod P) :=
    generator_integrable hf Y hYa hYc T A U 1 L hKf hLf
  have hZi (s : ℝ≥0) (hs : s≤T) : Integrable (fun ω => f (Y s ω)) P :=
    regularized_integrable hε _ (((hYa s).mono (F.le s)).aestronglyMeasurable) (hYfourth s hs)
  have hZtime (s : ℝ≥0) (hs : s≤T) : Integrable (FourPapersCommon.continuousAdaptedTimeCut
      (fun r ω => f (Y r ω)) s) (nonnegativeLebesgueMeasure.prod P) :=
    regularized_timeCut_integrable hε Y hYa hYc T s hs hYtime
  have hGb : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1∈Ioc 0 T →
      G q≤(K:ℝ)*f (Y q.1 q.2)+c :=
    generator_bound_ae hN hp hε β.coe_nonneg J X Y T A U hA hU hSphere hTangent
  have hZe : ∀ s,s≤T → ∃ V : Fin N → Fin N → PredictableProcessL2 F P,
      (fun ω => f (Y s ω))=ᵐ[P] fun ω => f v+
        (∫ r in Ioc (0 : ℝ≥0) s,G (r,ω) ∂nonnegativeLebesgueMeasure)+
        (∑ i : Fin N,(vectorIto D (V i) : Ω → ℝ) ω) := by
    intro s hs
    exact PrefixVectorC2Representation.scalar_representation D A U Y (fun _ => v) sigma T s hs
      hprefix hU hYa hYc hsc hf 1 L hKf hLf
  have hb := IntegrableScalarItoComparison.firstMoment_le D T K c (fun r ω => f (Y r ω))
    (fun _ => f v) G (integrable_const _) hZi hZtime hGi hGb hZe t ht
  have hh : (∫ ω,‖Y t ω‖ ∂P)≤∫ ω,f (Y t ω) ∂P :=
    integral_mono hYi (hZi t ht) (fun ω => norm_le_regularizedNorm hε _)
  have hb' := hh.trans hb
  have hce : (c:ℝ)=Real.sqrt ε/(N:ℝ) := rfl
  rw [hce] at hb'
  simpa only [f,integral_const,probReal_univ,one_smul] using hb' 

end SphericalAging.PhysicalVariationNormComparison
