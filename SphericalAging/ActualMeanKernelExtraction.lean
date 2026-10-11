module

public import SphericalAging.ActualMeanKernelTimeCompactness

public section

/-! Simultaneous actual C/Γ subsequence extraction on every compact
nonnegative time set, derived from true mean bounds and time increments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualMeanKernelExtraction
open HardSphereDynamics ActualStateIncrementMoments ActualModelOverlapVariance
  ActualOverlapTimeModulus ActualBrownianPrimitiveTimeModulus ActualMeanKernelTimeCompactness
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

 theorem overlapMean_abs_le_one (hN : 1≤N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (z : ℝ≥0×ℝ≥0) :
    |overlapMean (N := N) (p := p) β R hR z|≤1 := by
  have hf := actualOverlap_memLp_two (p := p) hN β R hR hNR z.1 z.2
  calc
    _≤∫ ω,|actualOverlap (N := N) (p := p) β R hR z.1 z.2 ω| ∂AnnealedModelLaw.law N p :=
      abs_integral_le_integral_abs
    _≤∫ _ : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N,(1 : ℝ)
        ∂AnnealedModelLaw.law N p := by
      apply integral_mono_ae (hf.norm.integrable (by norm_num)) (integrable_const _)
      filter_upwards [actualState_onSphere (p := p) hN β R hR hNR] with ω hω
      exact FiniteCorrelationIto.overlap_abs_le_one (by omega : 0<N) (hω z.1) (hω z.2)
    _=1 := by simp

 theorem gammaMean_abs_le (hN : 1≤N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (z : ℝ≥0×ℝ≥0) :
    |gammaMean (N := N) (p := p) β R hR z|≤Real.sqrt ((z.2 : ℝ)/2) := by
  have hf := actualGamma_memLp_two (p := p) hN β R hR hNR z.1 z.2
  have hh := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq (AnnealedModelLaw.law N p)
    (actualGamma (N := N) (p := p) β R hR z.1 z.2) hf
  simp only [probReal_univ,one_mul] at hh
  apply (Real.le_sqrt (abs_nonneg _) (by positivity : 0≤(z.2 : ℝ)/2)).mpr
  rw [sq_abs]
  exact hh.trans (actualGamma_secondMoment_le hN β R hR hNR z.1 z.2)

/-- Pointwise bounds suffice for Arzelà–Ascoli on locally compact,
sigma-compact domains; the bound may grow with the observation point. -/
 theorem pointwise_bounded_equicontinuous_compact {X : Type*} [TopologicalSpace X]
    (F : ℕ→C(X,ℝ)) (B : X→ℝ) (hBound : ∀ n x,|F n x|≤B x)
    (hEqui : Equicontinuous (fun n x => F n x)) :
    ∃ S : Set C(X,ℝ),IsCompact S ∧ ∀n,F n∈S := by
  let A : Set (X→ℝ) := closure (range (fun n => (F n : X→ℝ)))
  have hEqA : A.Equicontinuous := (equicontinuous_iff_range.mp hEqui).closure
  have hSubset : A⊆Set.pi univ (fun x => Icc (-(B x)) (B x)) := by
    apply closure_minimal
    · rintro f ⟨n,rfl⟩ x _
      exact abs_le.mp (hBound n x)
    · exact isClosed_set_pi (fun _ _ => isClosed_Icc)
  have hCompactA : IsCompact A :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset isClosed_closure hSubset
  let S : Set C(X,ℝ) := {f | (f : X→ℝ)∈A}
  have hImage : ContinuousMap.toFun '' S=A := by
    ext f
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f,hEqA.continuous_of_mem hf⟩,hf,rfl⟩
  have hEquiS : Equicontinuous ((↑) : S→X→ℝ) :=
    hEqA.comp (fun f : S => ⟨(f.1 : X→ℝ),f.2⟩)
  refine ⟨S,ArzelaAscoli.isCompact_of_equicontinuous S (hImage.symm ▸ hCompactA) hEquiS,?_⟩
  intro n
  exact subset_closure (mem_range_self n)

 theorem pointwise_bounded_equicontinuous_subsequence {X : Type*} [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
    (F : ℕ→C(X,ℝ)) (B : X→ℝ) (hBound : ∀ n x,|F n x|≤B x)
    (hEqui : Equicontinuous (fun n x => F n x)) :
    ∃f : C(X,ℝ),∃φ : ℕ→ℕ,StrictMono φ ∧ ∀K : Set X,IsCompact K →
      TendstoUniformlyOn (fun n x => F (φ n) x) f atTop K := by
  obtain ⟨S,hS,hFS⟩ := pointwise_bounded_equicontinuous_compact F B hBound hEqui
  obtain ⟨f,_,φ,hφ,hconv⟩ := hS.tendsto_subseq hFS
  exact ⟨f,φ,hφ,ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hconv⟩

 theorem actual_means_common_subsequence (dim : ℕ→ℕ) (hD : ∀n,1≤dim n)
    (p : ℕ) (hp : 0<p) (β : ℝ≥0) (R : ℕ→ℝ≥0) (hR : ∀n,0<(R n : ℝ))
    (hNR : ∀n,(dim n : ℝ)<(R n : ℝ)^2) :
    ∃c g : C(ℝ≥0×ℝ≥0,ℝ),∃φ : ℕ→ℕ,StrictMono φ ∧
      ∀K : Set (ℝ≥0×ℝ≥0),IsCompact K →
        TendstoUniformlyOn (fun n z => overlapMean (N := dim (φ n)) (p := p) β (R (φ n)) (hR (φ n)) z) c atTop K ∧
        TendstoUniformlyOn (fun n z => gammaMean (N := dim (φ n)) (p := p) β (R (φ n)) (hR (φ n)) z) g atTop K := by
  have hc := actual_overlap_means_equicontinuous dim hD p hp β R hR hNR
  let FC : ℕ→C(ℝ≥0×ℝ≥0,ℝ) := fun n => ⟨overlapMean (N := dim n) (p := p) β (R n) (hR n),hc.continuous n⟩
  obtain ⟨c,φ,hφ,hcφ⟩ := pointwise_bounded_equicontinuous_subsequence FC (fun _ => 1)
    (fun n z => overlapMean_abs_le_one (hD n) β (R n) (hR n) (hNR n) z) hc
  have hg := actual_gamma_means_equicontinuous (dim ∘ φ) (fun n => hD (φ n)) p hp β
    (R ∘ φ) (fun n => hR (φ n)) (fun n => hNR (φ n))
  let FG : ℕ→C(ℝ≥0×ℝ≥0,ℝ) := fun n => ⟨gammaMean (N := dim (φ n)) (p := p) β (R (φ n)) (hR (φ n)),hg.continuous n⟩
  obtain ⟨g,ψ,hψ,hgψ⟩ := pointwise_bounded_equicontinuous_subsequence FG
    (fun z => Real.sqrt ((z.2 : ℝ)/2))
    (fun n z => gammaMean_abs_le (hD (φ n)) β (R (φ n)) (hR (φ n)) (hNR (φ n)) z) hg
  refine ⟨c,g,φ ∘ ψ,hφ.comp hψ,?_⟩
  intro K hK
  exact ⟨(hcφ K hK).seq_tendstoUniformlyOn ψ hψ.tendsto_atTop,hgψ K hK⟩

end SphericalAging.ActualMeanKernelExtraction
