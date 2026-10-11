module

public import SphericalAging.WienerForkTransfer

public section

/-! Actual regrouping of the finite fork probability space into an independent
seed and disorder. The seed contains the initial point and every Wiener path. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory
namespace SphericalAging.ForkSeedCoordinates
open FiniteModel WienerForkTransfer WienerVectorGaussian WienerTrunkWeight
open scoped ENNReal

@[expose] abbrev Seed (N K : ℕ) := (Vector N×FutureSpace N K)×VectorBrownian.Space N
@[expose] def law (N K : ℕ) : Measure (Seed N K) :=
  ((SphereInitialLaw.sphereLaw N).prod (futureLaw N K)).prod (VectorBrownian.law N)
instance probability (N K : ℕ) : IsProbabilityMeasure (law N K) := by
  unfold law
  infer_instance

@[expose] def toFork {N p K : ℕ} (z : Seed N K×Disorder N p) : ForkSpace N p K :=
  (((z.2,z.1.1.1),z.1.1.2),z.1.2)

@[expose] def equiv (N p K : ℕ) : Seed N K×Disorder N p≃ᵐForkSpace N p K :=
  (MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.prodAssoc.symm.trans
      (MeasurableEquiv.prodAssoc.symm.prodCongr (MeasurableEquiv.refl _))))

theorem equiv_apply {N p K : ℕ} (z : Seed N K×Disorder N p) :
    equiv N p K z=toFork z := rfl

theorem toFork_measurePreserving (N p K : ℕ) :
    MeasurePreserving (toFork (N:=N) (p:=p) (K:=K))
      ((law N K).prod (disorderLaw N p)) (forkLaw N p K) := by
  have hs : MeasurePreserving
      (Prod.swap : Seed N K×Disorder N p→Disorder N p×Seed N K)
      ((law N K).prod (disorderLaw N p)) ((disorderLaw N p).prod (law N K)) :=
    Measure.measurePreserving_swap
  have ha := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (disorderLaw N p)
      ((SphereInitialLaw.sphereLaw N).prod (futureLaw N K)) (VectorBrownian.law N))
  have hb := (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (disorderLaw N p) (SphereInitialLaw.sphereLaw N)
      (futureLaw N K))).prod (MeasurePreserving.id (VectorBrownian.law N))
  exact hb.comp (ha.comp hs)

theorem toFork_measurable (N p K : ℕ) :
    Measurable (toFork (N:=N) (p:=p) (K:=K)) := (toFork_measurePreserving N p K).measurable

theorem toFork_integral {N p K : ℕ} (f : ForkSpace N p K→ℝ) :
    (∫z,f (toFork z) ∂(law N K).prod (disorderLaw N p))=
      ∫z,f z ∂forkLaw N p K :=
  (toFork_measurePreserving N p K).integral_comp (equiv N p K).measurableEmbedding f

theorem disorder_hasLaw (N p K : ℕ) :
    HasLaw (fun z : Seed N K×Disorder N p => z.2) (disorderLaw N p)
      ((law N K).prod (disorderLaw N p)) := measurePreserving_snd.hasLaw

@[expose] def gaussian {N K : ℕ} (k : TimeL2) (z : Seed N K) : Vector N := vectorIntegral k z.2

theorem gaussian_measurable {N K : ℕ} (k : TimeL2) :
    Measurable (gaussian (N:=N) (K:=K) k) :=
  (vectorIntegral_measurable N k).comp measurable_snd

theorem gaussian_hasLaw {N K : ℕ} {k : TimeL2} (hk : ‖k‖^2=1) :
    HasLaw (gaussian (N:=N) (K:=K) k) (stdGaussian (Vector N)) (law N K) := by
  have hk' : ‖k‖=1 := by nlinarith [norm_nonneg k]
  exact (vectorIntegral_law k hk').comp measurePreserving_snd.hasLaw

end SphericalAging.ForkSeedCoordinates
