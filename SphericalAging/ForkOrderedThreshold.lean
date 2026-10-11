module

public import SphericalAging.SeededBallEnergyThreshold
public import SphericalAging.FiniteForkMoments
public import SphericalAging.CurriedLimitTransfer
public import SphericalAging.ForkOrderedParameters

public section

/-! Threshold transfer for a genuine finite fork in the dimension-first
ordered filter. Lipschitz constants may depend on each fixed outer time;
no uniform-in-time algorithm estimate is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.ForkOrderedThreshold
open MeasureTheory ProbabilityTheory Set Filter FiniteModel
open WienerForkTransfer ForkSeedCoordinates FiniteForkMoments ForkNormalizedEnergy
open RandomGaussianPairing ForkEnergyComparison SeededBallEnergyThreshold ExternalFieldProbabilityTransfer
open ExternalFieldElementaryPenalty ExternalFieldUniformCost
open scoped NNReal ENNReal Topology

structure Algorithm {dim : ℕ→ℕ} (p K : ℕ) (Q : ℝ)
    (Y : ∀j,Fin K→ForkSpace (dim j) p K→Vector (dim j)) where
  lip : ℝ≥0
  output : ∀j,Seed (dim j) K×Disorder (dim j) p→Vector (dim j)
  measurable : ∀j,Measurable (output j)
  lipschitz : ∀j ξ,LipschitzWith lip
    (fun J : EuclideanSpace ℝ (TensorIndex (dim j) p) => output j (ξ,J.ofLp))
  ball : ∀j ξ J,‖output j (ξ,J)‖≤Real.sqrt (dim j)
  error : Tendsto (fun j => (∫z,‖output j z-projected Q (seededMean (Y j)) z‖^2
    ∂measure (dim j) p K)/(dim j:ℝ)) atTop (𝓝 0)

theorem energy_ceiling {p K : ℕ} (hp : 3≤p) (hK : 0<K)
    (dim : ℕ→ℕ) (hDim : ∀j,0<dim j) (hTop : Tendsto dim atTop atTop)
    {β Q e : ℝ} (hQ : 0<Q) (hQ1 : Q≤1) {t trunk : ℕ→ℝ≥0}
    (Y : ∀n j,Fin K→ForkSpace (dim j) p K→Vector (dim j))
    (hY : ∀n j,ForkJointLaw β (t n) (trunk n) (Y n j))
    (hEnergy : Tendsto (fun z : ℕ×ℕ => expectedEnergy (μ:=measure (dim z.2) p K)
      Prod.snd (seededMean (Y z.1 z.2))) ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 e))
    (hProjection : Tendsto (fun z : ℕ×ℕ => distanceRoot (measure (dim z.2) p K) (dim z.2)
      (projected Q (seededMean (Y z.1 z.2))) (normalized Q (seededMean (Y z.1 z.2))))
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 0))
    (A : ∀n,Algorithm p K Q (Y n)) (hThreshold : ∀Lip,PublishedFieldThreshold p Lip) :
    e≤thresholdEnergy p*Q^((p:ℝ)/2) := by
  have hA (n j : ℕ) : MemLp ((A n).output j) 2 (measure (dim j) p K) :=
    MemLp.of_bound ((A n).measurable j).aestronglyMeasurable (Real.sqrt (dim j))
      (Eventually.of_forall fun z => (A n).ball j z.1 z.2)
  have hd (n : ℕ) : Tendsto (fun j => distanceRoot (measure (dim j) p K) (dim j)
      ((A n).output j) (projected Q (seededMean (Y n j)))) atTop (𝓝 0) := by
    have hh := (A n).error.sqrt
    simp only [Real.sqrt_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall fun j => by
      dsimp only
      rw [←distanceRoot_sq (hDim j) (hA n j) (projected_memLp (Q:=Q) (hDim j) (seededMean_memLp (hY n j)))]
      exact Real.sqrt_sq (distanceRoot_nonneg _ _)
  have hdOrder : Tendsto (fun z : ℕ×ℕ => distanceRoot (measure (dim z.2) p K) (dim z.2)
      ((A z.1).output z.2) (projected Q (seededMean (Y z.1 z.2))))
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 0) :=
    CurriedLimitTransfer.tendsto_curried_of_iterated_limits
    (Eventually.of_forall hd) (tendsto_const_nhds (x:=(0:ℝ)))
  have hLowerLimit : Tendsto (fun z : ℕ×ℕ =>
      Q^(-((p:ℝ)/2))*expectedEnergy (μ:=measure (dim z.2) p K) Prod.snd (seededMean (Y z.1 z.2))-
        comparison p Q*(distanceRoot (measure (dim z.2) p K) (dim z.2)
          ((A z.1).output z.2) (projected Q (seededMean (Y z.1 z.2)))+
            distanceRoot (measure (dim z.2) p K) (dim z.2)
              (projected Q (seededMean (Y z.1 z.2))) (normalized Q (seededMean (Y z.1 z.2)))))
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 (Q^(-((p:ℝ)/2))*e)) := by
    simpa only [zero_add,mul_zero,sub_zero] using
      (hEnergy.const_mul (Q^(-((p:ℝ)/2)))).sub ((hdOrder.add hProjection).const_mul (comparison p Q))
  have hLower (n j : ℕ) := algorithm_energy_lower (hDim j) (by omega : 0<p) hQ hQ1
    (disorder_hasLaw (dim j) p K) (seededMean_memLp (hY n j)) (hA n j)
    (seededMean_bound hK (hY n j)) (Eventually.of_forall fun z => (A n).ball j z.1 z.2)
  have hUpper (n : ℕ) : ∀ε>0,∀ᶠj in atTop,
      expectedEnergy (μ:=measure (dim j) p K) Prod.snd ((A n).output j)≤thresholdEnergy p+ε :=
    seeded_energy_eventually hp (hThreshold (A n).lip) dim (fun j => by have hd:=hDim j;omega)
      hTop (fun j => ForkSeedCoordinates.law (dim j) K) (A n).output (A n).measurable
      (fun j => Eventually.of_forall fun ξ => ⟨(A n).lipschitz j ξ,(A n).ball j ξ⟩)
  have hceil : Q^(-((p:ℝ)/2))*e≤thresholdEnergy p := by
    by_contra hc
    have hg : thresholdEnergy p<Q^(-((p:ℝ)/2))*e := lt_of_not_ge hc
    let ε := (Q^(-((p:ℝ)/2))*e-thresholdEnergy p)/2
    have hε : 0<ε := by dsimp [ε];linarith
    have he : ∀ᶠz : ℕ×ℕ in ((atTop : Filter ℕ).curry (atTop : Filter ℕ)),
        Q^(-((p:ℝ)/2))*expectedEnergy (μ:=measure (dim z.2) p K) Prod.snd (seededMean (Y z.1 z.2))-
          comparison p Q*(distanceRoot (measure (dim z.2) p K) (dim z.2)
            ((A z.1).output z.2) (projected Q (seededMean (Y z.1 z.2)))+
              distanceRoot (measure (dim z.2) p K) (dim z.2)
                (projected Q (seededMean (Y z.1 z.2))) (normalized Q (seededMean (Y z.1 z.2))))
          ≤thresholdEnergy p+ε := by
      rw [eventually_curry_iff]
      exact Eventually.of_forall fun n => (hUpper n ε hε).mono fun j hj => (hLower n j).trans hj
    have hh := le_of_tendsto hLowerLimit he
    dsimp [ε] at hh
    linarith
  have hPower : 0<Q^((p:ℝ)/2) := Real.rpow_pos_of_pos hQ _
  have hMul := mul_le_mul_of_nonneg_left hceil hPower.le
  have hCancel : Q^((p:ℝ)/2)*Q^(-((p:ℝ)/2))=1 := by
    rw [←Real.rpow_add hQ,add_neg_cancel,Real.rpow_zero]
  calc
    e = Q^((p:ℝ)/2)*(Q^(-((p:ℝ)/2))*e) := by rw [←mul_assoc,hCancel,one_mul]
    _ ≤ Q^((p:ℝ)/2)*thresholdEnergy p := hMul
    _ = _ := mul_comm _ _

end SphericalAging.ForkOrderedThreshold
