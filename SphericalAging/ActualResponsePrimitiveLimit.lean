module

public import SphericalAging.ResponsePrimitiveLimitIdentification
public import SphericalAging.ActualResponsePrimitiveInterchange

public section

/-! The genuine joint-time response has integrable real-time rows by its
Gaussian landscape envelope. Uniform response limits therefore identify
limits of the literal Γ primitive on the entire nonnegative time square. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualResponsePrimitiveLimit
open FiniteModel ActualAnnealedCorrelationIntegral ActualAnnealedGammaIntegral
  ActualResponsePrimitiveInterchange ActualResponseJointKernel ActualResponseJointEnvelope
  AnnealedHamiltonianEnergyStein GaussianLandscape GaussianLandscapeMoments
  ResponsePrimitiveLimitIdentification
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def responseEnvelope (β : ℝ≥0) (t : ℝ≥0) : ℝ :=
  ∫ q : ModelSample N p,Real.exp
    (((β : ℝ)*(p : ℝ)^2*landscapeNorm N p q.1.1)*(t : ℝ)) ∂AnnealedModelLaw.law N p

lemma response_envelope_integrable (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0) (t : ℝ≥0) :
    Integrable (fun q : ModelSample N p => Real.exp
      (((β : ℝ)*(p : ℝ)^2*landscapeNorm N p q.1.1)*(t : ℝ))) (AnnealedModelLaw.law N p) := by
  have h := ((uniform_exponential_moment (by omega : 1≤N) (by omega : 0<p)
    ((β : ℝ)*(p : ℝ)^2*(t : ℝ))).1.comp_fst (SphereInitialLaw.sphereLaw N)).comp_fst (VectorBrownian.law N)
  convert h using 1
  · funext q
    congr 1
    ring
  · rfl

lemma modelResponse_abs_le_envelope (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    (t s : ℝ≥0) :
    |modelResponse (N := N) (p := p) β t s|≤responseEnvelope (N := N) (p := p) β t := by
  have hi := backwardTraceField_integrable hN hp β (N+1) (modelRadius_pos N)
    (modelRadius_sq N) t s
  have he := response_envelope_integrable hN hp β t
  have hb := backwardTraceField_abs_le_exp hN hp β (N+1) (modelRadius_pos N)
    (modelRadius_sq N) t s
  change ‖∫ q : ModelSample N p,backwardTraceField β (N+1) (modelRadius_pos N) ((t,s),q)
    ∂AnnealedModelLaw.law N p‖≤_
  exact (norm_integral_le_integral_norm _).trans (integral_mono_ae hi.norm he (by
    filter_upwards [hb] with q hq
    simpa only [Real.norm_eq_abs] using hq))

/-- Every true real-time model response row is integrable on compact intervals.
Its proof uses the constructed unbounded full-law response envelope. -/
theorem modelResponse_intervalIntegrable (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    (t s : ℝ≥0) :
    IntervalIntegrable (fun v : ℝ => modelResponse (N := N) (p := p) β t v.toNNReal)
      volume 0 (s : ℝ) := by
  have hm : StronglyMeasurable (fun v : ℝ => modelResponse (N := N) (p := p) β t v.toNNReal) :=
    (responseMeanPair_stronglyMeasurable (N := N) (p := p) β (N+1) (modelRadius_pos N)).comp_measurable
      (g := fun v : ℝ => (t,v.toNNReal)) (by fun_prop)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le s.coe_nonneg).mpr
  apply Integrable.of_bound hm.aestronglyMeasurable.restrict
    (responseEnvelope (N := N) (p := p) β t)
  exact .of_forall (fun v => by
    simpa only [Real.norm_eq_abs] using modelResponse_abs_le_envelope hN hp β t v.toNNReal)

/-- The literal actual Γ mean limit is the prefix of any uniform response
row limit. Arbitrary dimension filters are allowed; finite-N row regularity
and the exact primitive identity are discharged from the physical model. -/
theorem actual_gamma_response_limit {ι : Type*} {l : Filter ι} [NeBot l]
    (dim : ι→ℕ) (hDim : Tendsto dim l atTop) (hp : 2≤p) (β : ℝ≥0)
    (t s : ℝ≥0) {R : ℝ→ℝ} {g : ℝ}
    (hR : IntervalIntegrable R volume 0 (min (t : ℝ) (s : ℝ)))
    (hRlim : TendstoUniformlyOn (fun i => fun v : ℝ =>
      modelResponse (N := dim i) (p := p) β t v.toNNReal) R l
        (uIcc 0 (min (t : ℝ) (s : ℝ))))
    (hGlim : Tendsto (fun i => annealedGammaPair (N := dim i) (p := p) β
      (dim i+1) (modelRadius_pos (dim i)) t s) l (𝓝 g)) :
    g=∫ v in (0 : ℝ)..(min (t : ℝ) (s : ℝ)),R v := by
  have hN : ∀ᶠ i in l,3≤dim i := hDim.eventually (eventually_ge_atTop 3)
  have hI : ∀ᶠ i in l,IntervalIntegrable (fun v : ℝ =>
      modelResponse (N := dim i) (p := p) β t v.toNNReal)
        volume 0 (min (t : ℝ) (s : ℝ)) := by
    filter_upwards [hN] with i hi
    simpa only [NNReal.coe_min] using modelResponse_intervalIntegrable hi hp β t (min t s)
  have htend := intervalIntegral_tendsto_of_uniform_integrable hI hR hRlim
  have he : (fun i => annealedGammaPair (N := dim i) (p := p) β
      (dim i+1) (modelRadius_pos (dim i)) t s)=ᶠ[l]
      (fun i => ∫ v in (0 : ℝ)..(min (t : ℝ) (s : ℝ)),
        modelResponse (N := dim i) (p := p) β t v.toNNReal) := by
    filter_upwards [hN] with i hi
    exact actual_gamma_response_min_prefix hi hp β t s
  exact tendsto_nhds_unique hGlim (htend.congr' he.symm)

end SphericalAging.ActualResponsePrimitiveLimit
