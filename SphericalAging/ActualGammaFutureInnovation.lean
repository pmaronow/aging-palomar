module

public import SphericalAging.ActualOverlapFutureInnovation
public import SphericalAging.ActualBackgroundGammaLaw

public section

/-! True future innovation for the Brownian pairing. The observed Brownian
direction at the waiting time remains correlated with the observed state;
only the constructed future Wiener path is independent of their joint law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualGammaFutureInnovation
open HardSphereDynamics ActualSphereTransition AnnealedSDECore ActualSphereBackwardIto
open ActualSphereMarkovRestart BrownianFuturePath BrownianFutureFiltered ActualSphereLinearInnovation
open BrownianVectorMoments ActualBrownianPrimitiveTimeModulus ActualBackgroundGammaLaw
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem pairing_square_le_of_norm_sq (hN : 0<N) (a y : State N) (hy : ‖y‖^2≤(N : ℝ)) :
    (⟪a,y⟫_ℝ/(Real.sqrt 2*(N : ℝ)))^2≤‖a‖^2/(2*(N : ℝ)) := by
  have hn : (N : ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  calc
    _≤(‖a‖^2*(N : ℝ))/(2*(N : ℝ)^2) :=
      div_le_div_of_nonneg_right ((inner_square_le a y).trans
        (mul_le_mul_of_nonneg_left hy (sq_nonneg _))) (by positivity)
    _=_ := by field_simp

theorem brownianVector_waiting_measurable (s : ℝ≥0) :
    Measurable[NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) s]
      (brownianVector (N := N) s) := by
  have hcoord (i : Fin N) :
      Measurable[NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) s]
        (VectorBrownian.coordinate i s) :=
    ((VectorBrownian.coordinate_stronglyAdapted i s).mono
      (NullAugmentation.le_augment (VectorBrownian.filtration N) s)).measurable
  letI : MeasurableSpace (VectorBrownian.Space N) :=
    NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) s
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)
  exact L.symm.continuous.measurable.comp (measurable_pi_iff.mpr hcoord)

theorem future_gamma_innovation_variance_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    {Z0 : VectorBrownian.Space N → State N}
    (X : ℝ≥0 → VectorBrownian.Space N → State N)
    (hX : ∀ T,IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω))
    (s u : ℝ≥0) :
    (∫ ω,((⟪brownianVector s ω,X (s+u) ω⟫_ℝ-
      ⟪brownianVector s ω,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u (X s ω)⟫_ℝ)/
        (Real.sqrt 2*(N : ℝ)))^2 ∂VectorBrownian.law N)≤
      ((s : ℝ)*u/(N : ℝ))*Real.exp (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*u) := by
  let P := VectorBrownian.law N
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let F := NullAugmentation.augment (VectorBrownian.filtration N) P
  have hn : 0<N := by omega
  have hZa : Measurable[F s] (fun ω => (X s ω,brownianVector s ω)) :=
    ((hX 0).2.1 s).measurable.prodMk (brownianVector_waiting_measurable s)
  let Z : VectorBrownian.Space N → State N×State N := fun ω => (X s ω,brownianVector s ω)
  have hZm : Measurable Z := hZa.mono (F.le s) le_rfl
  let μ := P.map Z
  letI : IsProbabilityMeasure μ :=
    (hasLaw_map hZm.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hZmap : MeasurePreserving Z P μ := ⟨hZm,rfl⟩
  have hμs : ∀ᵐ z ∂μ,OnSphere z.1 :=
    (ae_map_iff hZm.aemeasurable (ActualSphereKernelSupport.measurableSet_onSphere.preimage measurable_fst)).mpr
      (hSphere.mono (fun ω h => h s))
  have hBi : Integrable (fun z : State N×State N => ‖z.2‖^2) μ :=
    (hZmap.integrable_comp (by fun_prop)).mp (brownianVector_memLp s (q := 2) (by norm_num)).integrable_norm_pow'
  have hBint : (∫ z : State N×State N,‖z.2‖^2 ∂μ)=(N : ℝ)*s := by
    rw [← hZmap.map_eq,integral_map hZm.aemeasurable (by fun_prop)]
    exact brownianVector_secondMoment s
  let Y : (State N×State N)×VectorBrownian.Space N → State N := fun q => jointProcess D β R hR (J,q.1.1) u q.2
  let g : State N×State N → ℝ := fun z => ⟪z.2,mean D β R hR J u z.1⟫_ℝ/(Real.sqrt 2*(N : ℝ))
  let G : (State N×State N)×VectorBrownian.Space N → ℝ := fun q => ⟪q.1.2,Y q⟫_ℝ/(Real.sqrt 2*(N : ℝ))
  let E : (State N×State N)×VectorBrownian.Space N → ℝ := fun q => (G q-g q.1)^2
  have hY : StronglyMeasurable Y := (jointProcess_measurable D β R hR).comp_measurable
    ((measurable_const.prodMk (measurable_fst.comp measurable_fst)).prodMk (measurable_const.prodMk measurable_snd))
  have hmean : Continuous (mean D β R hR J u) :=
    (show Differentiable ℝ (mean D β R hR J u) from fun x =>
      (ActualSphereMeanDerivative.mean_hasFDerivAt (VectorBrownian.driver N) β J R hR x (u+1) u
        (by simp) (by positivity)).differentiableAt).continuous
  have hg : Continuous g := (continuous_snd.inner (hmean.comp continuous_fst)).div_const _
  have hG : StronglyMeasurable G := (continuous_id.div_const (Real.sqrt 2*(N : ℝ))).comp_stronglyMeasurable
    ((measurable_snd.comp measurable_fst).stronglyMeasurable.inner hY)
  have hE : StronglyMeasurable E := (hG.sub (hg.stronglyMeasurable.comp_measurable measurable_fst)).pow 2
  have hsp : ∀ᵐ q ∂μ.prod P,OnSphere q.1.1 ∧ OnSphere (Y q) := by
    have hm : MeasurableSet {q : (State N×State N)×VectorBrownian.Space N | OnSphere q.1.1 ∧ OnSphere (Y q)} :=
      (ActualSphereKernelSupport.measurableSet_onSphere.preimage (measurable_fst.comp measurable_fst)).inter
        (ActualSphereKernelSupport.measurableSet_onSphere.preimage hY.measurable)
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [hμs] with z hz
    exact (jointProcess_onSphere (Nat.ne_of_gt hn) (VectorBrownian.driver N) β R hR hNR J z.1 hz).mono
      (fun ω h => ⟨hz,h u⟩)
  have hEi : Integrable E (μ.prod P) := by
    apply ((hBi.const_mul (2/(N : ℝ))).comp_fst P).mono' hE.aestronglyMeasurable
    filter_upwards [hsp] with q hq
    have h1 : (G q)^2≤‖q.1.2‖^2/(2*(N : ℝ)) := pairing_square_le_of_norm_sq hn _ _
      ((onSphere_iff_norm_sq _).mp hq.2).le
    have h2 : (g q.1)^2≤‖q.1.2‖^2/(2*(N : ℝ)) := pairing_square_le_of_norm_sq hn _ _
      (mean_norm_sq_le (Nat.ne_of_gt hn) (VectorBrownian.driver N) β R hR hNR J u q.1.1 hq.1)
    change ‖(G q-g q.1)^2‖≤(2/(N : ℝ))*‖q.1.2‖^2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _≤2*(G q)^2+2*(g q.1)^2 := by nlinarith [sq_nonneg (G q+g q.1)]
      _≤4*(‖q.1.2‖^2/(2*(N : ℝ))) := by linarith
      _=_ := by ring
  let φ : VectorBrownian.Space N → (State N×State N)×VectorBrownian.Space N := fun ω => (Z ω,future s ω)
  have hφ : MeasurePreserving φ P (μ.prod P) := waiting_future_measurePreserving s Z hZa
  have hpull : (∫ ω,E (φ ω) ∂P)=∫ q,E q ∂μ.prod P := by
    rw [← hφ.map_eq]
    exact (integral_map hφ.measurable.aemeasurable hE.aestronglyMeasurable).symm
  have he : (fun ω => ((⟪brownianVector s ω,X (s+u) ω⟫_ℝ-
      ⟪brownianVector s ω,mean D β R hR J u (X s ω)⟫_ℝ)/(Real.sqrt 2*(N : ℝ)))^2)=ᵐ[P]
      fun ω => E (φ ω) := by
    filter_upwards [actual_future_eq_joint (Nat.ne_of_gt hn) β R hR hNR J X hX hSphere s u] with ω hω
    dsimp only [E,G,g,φ,Z,Y]
    rw [hω,sub_div]
  let c : ℝ := (u : ℝ)/(N : ℝ)^2*Real.exp (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*u)
  have hb : ∀ᵐ z ∂μ,(∫ ω,E (z,ω) ∂P)≤c*‖z.2‖^2 := by
    filter_upwards [hμs] with z hz
    have hh := linear_innovation_variance_le hN hp β R hR hNR J
      (jointProcess D β R hR (J,z.1)) u
      (jointProcess_physical (Nat.ne_of_gt hn) (VectorBrownian.driver N) β R hR hNR J z.1 hz u)
      (jointProcess_onSphere (Nat.ne_of_gt hn) (VectorBrownian.driver N) β R hR hNR J z.1 hz)
      ((Real.sqrt 2*(N : ℝ))⁻¹ • z.2)
      (ActualSphereLinearRegularity.linear_spatialC2Transition β R hR J ((Real.sqrt 2*(N : ℝ))⁻¹ • z.2))
    have heq : (fun ω => (⟪(Real.sqrt 2*(N : ℝ))⁻¹ • z.2,jointProcess D β R hR (J,z.1) u ω⟫_ℝ-
        ⟪(Real.sqrt 2*(N : ℝ))⁻¹ • z.2,mean D β R hR J u z.1⟫_ℝ)^2)=fun ω => E (z,ω) := by
      funext ω
      simp only [E,G,g,Y,real_inner_smul_left,div_eq_mul_inv]
      ring
    rw [heq,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (by positivity)),mul_pow,inv_pow,
      mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)] at hh
    refine hh.trans_eq ?_
    dsimp only [c]
    field_simp
  rw [integral_congr_ae he,hpull,integral_prod E hEi]
  have hh := integral_mono_of_nonneg (.of_forall (fun z => integral_nonneg (fun _ => sq_nonneg _)))
    (hBi.const_mul c) hb
  rw [integral_const_mul,hBint] at hh
  refine hh.trans_eq ?_
  dsimp only [c]
  have hn' : (N : ℝ)≠0 := (Nat.cast_pos.mpr hn).ne'
  field_simp

/-- All solution and support inputs discharged for the actual canonical
physical process, with the true correlated waiting Brownian observation. -/
theorem joint_future_gamma_innovation_variance_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x : State N) (hx : OnSphere x) (s u : ℝ≥0) :
    (∫ ω,(jointGamma β R hR (s+u) s ((J,x),ω)-
      ⟪brownianVector s ω,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u
        (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) s ω)⟫_ℝ/
          (Real.sqrt 2*(N : ℝ)))^2 ∂VectorBrownian.law N)≤
      ((s : ℝ)*u/(N : ℝ))*Real.exp (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*u) := by
  have hn : N≠0 := by omega
  have hh := future_gamma_innovation_variance_le hN hp β R hR hNR J
    (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x))
    (fun T => jointProcess_physical hn (VectorBrownian.driver N) β R hR hNR J x hx T)
    (jointProcess_onSphere hn (VectorBrownian.driver N) β R hR hNR J x hx) s u
  simpa only [jointGamma,real_inner_comm,sub_div] using hh

end SphericalAging.ActualGammaFutureInnovation
