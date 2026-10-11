module

public import SphericalAging.ActualCKMeanKernelConvergence
public import SphericalAging.ActualSphereCKFisherMajorant

public section

/-! The preceding actual-model mean bridges are theorems of the genuine
whole-sequence C/Γ/R convergence. The signed response primitive clause is
identified with the literal Brownian pairing using the proved source3.4. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology
namespace SphericalAging.ActualSphereCKBridges
open FiniteModel CKSpecification ActualForkMeanBridge ActualResponseWindowLimit
open ActualSphereRowPrimitiveLimit ActualSphereCKFisherMajorant
open ActualCanonicalMeanKernelExtraction ActualCompactCKMemoryLimit
open ActualCKMeanKernelConvergence AnnealedHamiltonianEnergyStein
open ActualEnergyUniformBridge ActualResponseKernel TwoTimeResponseTimeParameter
open GreenCovariance
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

theorem actualMean_eq_modelCorrelation (β : ℝ≥0) (t s : ℝ) :
    actualMean (N:=N) (p:=p) β (N+1) (modelRadius_pos N) t s=
      modelCorrelation N p β t.toNNReal s.toNNReal :=
  overlapMean_eq_correlationPair β (N+1) (modelRadius_pos N) (t.toNNReal,s.toNNReal)

theorem canonical_responseRow_eq_modelResponse (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    (H s : ℝ≥0) (hs : s≤H) :
    dimensionResponseRow hp β (fun _ => N) 0 H s=
      ActualResponsePrimitiveInterchange.modelResponse (N:=N) (p:=p) β H s := by
  let uw : WaitingTime H := ⟨s,bot_le,hs⟩
  have hd := dimensionResponseRow_eq_actual hp β H (fun _ => N) 0 (by omega) uw
  have hc : ActualResponsePrimitiveInterchange.modelResponse (N:=N) (p:=p) β H s=
      annealedResponse (p:=p) (by omega : N≠0) β (N+1) (modelRadius_pos N)
        (modelRadius_sq N) H uw :=
    ActualResponseJointEnvelope.responseMeanPair_eq_annealedResponse hN hp β (N+1)
      (modelRadius_pos N) (modelRadius_sq N) H uw
  exact hd.trans hc.symm

theorem canonical_responsePrimitive_eq_modelGamma (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    (H s : ℝ≥0) (hs : s≤H) :
    (∫u in (0:ℝ)..(s:ℝ),dimensionResponseRow hp β (fun _ => N) 0 H u)=modelGamma N p β H s := by
  rw [modelGamma,ActualResponsePrimitiveInterchange.actual_gamma_response_prefix hN hp β H s hs]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u∈Icc (0:ℝ) (s:ℝ) := by simpa only [uIcc_of_le s.coe_nonneg] using hu
  have hsu : u.toNNReal≤H := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hu'.1]
    exact hu'.2.trans hs
  have he := canonical_responseRow_eq_modelResponse hN hp β H u.toNNReal hsu
  simpa only [Real.coe_toNNReal _ hu'.1] using he

theorem canonical_MeanBridge (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKData) (h : CKEquations p β d) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    MeanBridge (p:=p) β dim (fun n => dim n+1) (fun n => modelRadius_pos (dim n)) d := by
  intro A hA
  have hc := (actual_ck_means_uniform_limit dim hdim hp β hβ d h ⟨A,hA⟩).1
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hc ε hε] with n hn
  intro z hz
  have hz' : (z.1.toNNReal,z.2.toNNReal)∈CompactKernelMemoryLimit.square ⟨A,hA⟩ := by
    constructor <;> apply NNReal.coe_le_coe.mp
    · rw [Real.coe_toNNReal _ hz.1.1];exact hz.1.2
    · rw [Real.coe_toNNReal _ hz.2.1];exact hz.2.2
  simpa only [actualMean_eq_modelCorrelation,Real.coe_toNNReal _ hz.1.1,
    Real.coe_toNNReal _ hz.2.1,Function.uncurry_apply_pair] using hn (z.1.toNNReal,z.2.toNNReal) hz'

theorem canonical_ResponsePrimitiveBridge (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKData) (h : CKEquations p β d) (dim : ℕ→ℕ)
    (hDim : ∀n,3≤dim n) (hdim : Tendsto dim atTop atTop) :
    ResponsePrimitiveBridge (by omega : 2≤p) β dim d := by
  intro H
  have hg := (actual_ck_means_uniform_limit dim hdim hp β hβ d h H).2.1
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hg ε hε] with n hn
  intro z hz
  have ht := hz.1.1
  have hs := hz.2.1
  have hst := hz.2.2
  let tn : ℝ≥0 := ⟨z.1,ht⟩
  let sn : ℝ≥0 := ⟨z.2,hs⟩
  have hz' : (tn,sn)∈CompactKernelMemoryLimit.square H := ⟨hz.1.2,hst.trans hz.1.2⟩
  have hiR := (responseRow_integrable (by omega : 2≤p) β (dim n-1) ht).mono_set
    (show uIcc (0:ℝ) z.2⊆uIcc 0 z.1 from by rw [uIcc_of_le hs,uIcc_of_le ht];exact Icc_subset_Icc le_rfl hst)
  have hRc : ContinuousOn (fun u => d.R z.1 u) (Icc 0 z.2) :=
    h.response_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ⟨hu.1,hu.2.trans hst⟩)
  have he : (∫u in (0:ℝ)..z.2,dimensionResponseRow (by omega : 2≤p) β dim n z.1 u-d.R z.1 u)=
      modelGamma (dim n) p β tn sn-ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2 := by
    calc
      _=(∫u in (0:ℝ)..z.2,dimensionResponseRow (by omega : 2≤p) β dim n z.1 u)-
          (∫u in (0:ℝ)..z.2,d.R z.1 u) := intervalIntegral.integral_sub hiR (hRc.intervalIntegrable_of_Icc hs)
      _=_ := by
        have hg' := canonical_responsePrimitive_eq_modelGamma (hDim n) (by omega : 2≤p) β tn sn hst
        change (∫u in (0:ℝ)..z.2,dimensionResponseRow (by omega : 2≤p) β dim n z.1 u)=
          modelGamma (dim n) p β tn sn at hg'
        rw [hg',ResponsePrimitiveInterchange.responsePrimitive,min_eq_right hst]
  rw [he]
  have hh := hn (tn,sn) hz'
  change dist (ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2)
    (modelGamma (dim n) p β tn sn)<ε at hh
  rw [Real.dist_eq,abs_sub_comm] at hh
  simpa only [Real.dist_eq,sub_zero,zero_sub,abs_neg] using hh

end SphericalAging.ActualSphereCKBridges
