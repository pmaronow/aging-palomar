module

public import SphericalAging.PhysicalForkRestart

public section

/-! Distinct branches of the genuine whole-path finite fork have the
literal two-independent-future overlap law. The sample law is proved by
independence of distinct coordinates of the actual future product law. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.PhysicalForkPairSampler
open FiniteModel HardSphereDynamics WienerForkTransfer PhysicalForkConstruction
  PhysicalForkRestart ActualSphereTransition AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N p K : ℕ}

@[expose] abbrev PairSample (N p : ℕ) := Disorder N p×
  ((State N×VectorBrownian.Space N)×(VectorBrownian.Space N×VectorBrownian.Space N))

@[expose] def pairLaw (N p : ℕ) : Measure (PairSample N p) :=
  (disorderLaw N p).prod (((SphereInitialLaw.sphereLaw N).prod (VectorBrownian.law N)).prod
    ((VectorBrownian.law N).prod (VectorBrownian.law N)))

theorem futurePair_measurePreserving (b c : Fin K) (hbc : b≠c) :
    MeasurePreserving (fun z : FutureSpace N K => (z b,z c)) (futureLaw N K)
      ((VectorBrownian.law N).prod (VectorBrownian.law N)) := by
  have hi : iIndepFun (fun b (z : FutureSpace N K) => z b) (futureLaw N K) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  refine ⟨(measurable_pi_apply b).prodMk (measurable_pi_apply c),?_⟩
  rw [(hi.indepFun hbc).map_prod_eq_prod_map_map (measurable_pi_apply b).aemeasurable
    (measurable_pi_apply c).aemeasurable]
  have hb : (futureLaw N K).map (fun z : FutureSpace N K => z b)=VectorBrownian.law N :=
    (measurePreserving_eval (fun _ : Fin K => VectorBrownian.law N) b).map_eq
  have hc : (futureLaw N K).map (fun z : FutureSpace N K => z c)=VectorBrownian.law N :=
    (measurePreserving_eval (fun _ : Fin K => VectorBrownian.law N) c).map_eq
  rw [hb,hc]

@[expose] def pairSampler (b c : Fin K) (z : ForkSpace N p K) : PairSample N p :=
  (z.1.1.1,((z.1.1.2,z.2),(z.1.2 b,z.1.2 c)))

theorem pairSampler_measurePreserving (b c : Fin K) (hbc : b≠c) :
    MeasurePreserving (pairSampler (N:=N) (p:=p) b c) (forkLaw N p K) (pairLaw N p) := by
  have h1 := measurePreserving_prodAssoc (AnnealedModelLaw.parameterLaw N p)
    (futureLaw N K) (VectorBrownian.law N)
  have h2 := (MeasurePreserving.id (AnnealedModelLaw.parameterLaw N p)).prod
    (Measure.measurePreserving_swap.comp ((futurePair_measurePreserving (N:=N) b c hbc).prod
      (MeasurePreserving.id (VectorBrownian.law N))))
  have h3 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (AnnealedModelLaw.parameterLaw N p) (VectorBrownian.law N)
      ((VectorBrownian.law N).prod (VectorBrownian.law N)))
  have h4 := (measurePreserving_prodAssoc (disorderLaw N p) (SphereInitialLaw.sphereLaw N)
    (VectorBrownian.law N)).prod
      (MeasurePreserving.id ((VectorBrownian.law N).prod (VectorBrownian.law N)))
  have h5 := measurePreserving_prodAssoc (disorderLaw N p)
    ((SphereInitialLaw.sphereLaw N).prod (VectorBrownian.law N))
      ((VectorBrownian.law N).prod (VectorBrownian.law N))
  have hh := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  convert hh using 1 <;> rfl

@[expose] def restartOverlap (β : ℝ) (T a d : ℝ≥0) (z : PairSample N p) : ℝ :=
  ⟪jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1) (modelRadius_pos N)
      (z.1,jointEndpoint β T ((z.1,z.2.1.1),z.2.1.2)) a z.2.2.1,
    jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1) (modelRadius_pos N)
      (z.1,jointEndpoint β T ((z.1,z.2.1.1),z.2.1.2)) d z.2.2.2⟫_ℝ/(N:ℝ)

theorem restartOverlap_measurable (β : ℝ) (T a d : ℝ≥0) :
    Measurable (restartOverlap (N:=N) (p:=p) β T a d) := by
  have hw : Measurable (fun z : PairSample N p => jointEndpoint β T ((z.1,z.2.1.1),z.2.1.2)) :=
    (jointEndpoint_measurable β T).comp
      ((measurable_fst.prodMk (measurable_fst.comp (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp (measurable_fst.comp measurable_snd)))
  have hparam : Measurable (fun z : PairSample N p =>
      (z.1,jointEndpoint β T ((z.1,z.2.1.1),z.2.1.2))) := measurable_fst.prodMk hw
  have h1 : Measurable (fun z : PairSample N p => jointProcess
      (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1) (modelRadius_pos N)
        (z.1,jointEndpoint β T ((z.1,z.2.1.1),z.2.1.2)) a z.2.2.1) :=
    (jointProcess_measurable (NullAugmentation.driver (VectorBrownian.driver N))
      β (N+1) (modelRadius_pos N)).measurable.comp
      (hparam.prodMk (measurable_const.prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))))
  have h2 : Measurable (fun z : PairSample N p => jointProcess
      (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1) (modelRadius_pos N)
        (z.1,jointEndpoint β T ((z.1,z.2.1.1),z.2.1.2)) d z.2.2.2) :=
    (jointProcess_measurable (NullAugmentation.driver (VectorBrownian.driver N))
      β (N+1) (modelRadius_pos N)).measurable.comp
      (hparam.prodMk (measurable_const.prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  exact ((continuous_fst.inner continuous_snd).measurable.comp (h1.prodMk h2)).div_const _

theorem branchOverlap_eq_restart (hN : 0<N) (β : ℝ) (T a d : ℝ≥0) (b c : Fin K) :
    (fun z : ForkSpace N p K =>
      ⟪branch β (T+a) T b z,branch β (T+d) T c z⟫_ℝ/(N:ℝ))=ᵐ[forkLaw N p K]
      (fun z => restartOverlap β T a d (pairSampler b c z)) := by
  filter_upwards [branch_eq_restarted (N:=N) (p:=p) hN β T a b,
    branch_eq_restarted (N:=N) (p:=p) hN β T d c] with z hb hc
  rw [hb,hc]
  rfl

/-- Every measurable test, including the first two moments and the
squared distance from a CK value, transfers to the true independent
future overlap law. -/
theorem branch_test_integral (hN : 0<N) (β : ℝ) (T a d : ℝ≥0)
    (b c : Fin K) (hbc : b≠c) {f : ℝ→ℝ} (hf : Measurable f) :
    (∫z : ForkSpace N p K,f (⟪branch β (T+a) T b z,branch β (T+d) T c z⟫_ℝ/(N:ℝ))
      ∂forkLaw N p K)=∫z : PairSample N p,f (restartOverlap β T a d z) ∂pairLaw N p := by
  calc
    _ = ∫z : ForkSpace N p K,f (restartOverlap β T a d (pairSampler b c z)) ∂forkLaw N p K :=
      integral_congr_ae ((branchOverlap_eq_restart (N:=N) (p:=p) hN β T a d b c).mono
        (fun _ h => congrArg f h))
    _ = _ := by
      have hh := (pairSampler_measurePreserving (N:=N) (p:=p) b c hbc).hasLaw.integral_comp
        (hf.comp (restartOverlap_measurable β T a d)).aestronglyMeasurable
      simpa only [Function.comp_def] using hh

end SphericalAging.PhysicalForkPairSampler
