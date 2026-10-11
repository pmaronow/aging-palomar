module

public import SphericalAging.ActualSphereDensityCorrelation
public import SphericalAging.ActualSphereDensityResponseMoments
public import SphericalAging.ActualSphereAnnealedFDT
public import SphericalAging.ActualResponseWindowLimit
public import SphericalAging.SphereCKFisherMajorant

public section

/-! Literal finite FDT row primitives converge from the preceding actual
correlation and signed response primitive bridges. No row-primitive limit
or Fisher domination is supplied as an assumption. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology
namespace SphericalAging.ActualSphereRowPrimitiveLimit
open FiniteModel CKSpecification GreenCovariance PrefixRectangleStability
open HardSphereDynamics SphereInitialLaw SphereQuenchedFDT SphereAnnealedCurrentFDT
open ActualSphereGibbsDensity ActualSphereMeanSpatialInterface ActualSphereDensityCorrelation
open ActualSphereDensityResponse ActualSphereDensityResponseMoments ActualSphereAnnealedFDT
open ActualForkMeanBridge ActualResponseWindowLimit SphereCKFisherMajorant
open ActualResponseKernel TwoTimeResponseTimeParameter CanonicalAnnealedResponseRepresentative
open AnnealedHamiltonianEnergyStein ActualEnergyUniformBridge
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

theorem actual_rowPrimitive_eq_model (hN : 3≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (H s : ℝ≥0) (hs : s≤H) :
    ActualSphereAnnealedFDT.annealedRowPrimitive (N:=N) (p:=p) β R hR H s=
      actualMean (N:=N) (p:=p) β R hR H s-actualMean (N:=N) (p:=p) β R hR H 0-
        (∫u in (0:ℝ)..(s:ℝ),∫J : Disorder N p,
          quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) H u ∂disorderLaw N p) := by
  have hiS := densityCorrelation_disorder_integrable (N:=N) (p:=p) (by omega) (by omega) β R hR hNR H s hs
  have hi0 := densityCorrelation_disorder_integrable (N:=N) (p:=p) (by omega) (by omega) β R hR hNR H 0 (bot_le)
  simp only [NNReal.coe_zero] at hi0
  have hiR := densityResponse_interval_fubini (by omega) hp β R hR hNR H s hs
  let fS : Disorder N p→ℝ := fun J => quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) H s
  let f0 : Disorder N p→ℝ := fun J => quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) H 0
  let fR : Disorder N p→ℝ := fun J => ∫u in (0:ℝ)..(s:ℝ),
    quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) H u
  change Integrable fS (disorderLaw N p) at hiS
  change Integrable f0 (disorderLaw N p) at hi0
  have hiR' : Integrable fR (disorderLaw N p) := hiR.1
  unfold ActualSphereAnnealedFDT.annealedRowPrimitive rowPrimitive
  change (∫J : Disorder N p,(fS-f0-fR) J ∂disorderLaw N p)=_
  calc
    _=(∫J : Disorder N p,(fS-f0) J ∂disorderLaw N p)-(∫J : Disorder N p,fR J ∂disorderLaw N p) :=
      integral_sub (hiS.sub hi0) hiR'
    _=((∫J : Disorder N p,fS J ∂disorderLaw N p)-(∫J : Disorder N p,f0 J ∂disorderLaw N p))-
        (∫J : Disorder N p,fR J ∂disorderLaw N p) :=
      congrArg (fun z => z-(∫J : Disorder N p,fR J ∂disorderLaw N p)) (integral_sub hiS hi0)
    _=_ := by
      dsimp only [fS,f0,fR]
      have he0 := densityCorrelation_annealed_eq_actualMean (N:=N) (p:=p) (by omega) (by omega)
        β R hR hNR H 0 bot_le
      simp only [NNReal.coe_zero] at he0
      rw [hiR.2,
        densityCorrelation_annealed_eq_actualMean (by omega) (by omega) β R hR hNR H s hs,
        he0]

theorem canonical_rowPrimitive_eq_dimension (hp : 2≤p) (β : ℝ≥0)
    (dim : ℕ→ℕ) (j : ℕ) (hDim : 3≤dim j) (H s : ℝ≥0) (hs : s≤H) :
    ActualSphereAnnealedFDT.annealedRowPrimitive (N:=dim j) (p:=p) β (dim j+1)
      (modelRadius_pos (dim j)) H s=
      actualMean (N:=dim j) (p:=p) β (dim j+1) (modelRadius_pos (dim j)) H s-
        actualMean (N:=dim j) (p:=p) β (dim j+1) (modelRadius_pos (dim j)) H 0-
        (∫u in (0:ℝ)..(s:ℝ),dimensionResponseRow hp β dim j H u) := by
  rw [actual_rowPrimitive_eq_model hDim hp β (dim j+1) (modelRadius_pos (dim j))
    (modelRadius_sq (dim j)) H s hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u∈Icc (0:ℝ) (s:ℝ) := by simpa only [uIcc_of_le s.coe_nonneg] using hu
  let un : ℝ≥0 := ⟨u,hu'.1⟩
  let uw : WaitingTime H := ⟨un,bot_le,show un≤H from hu'.2.trans hs⟩
  have he := densityResponse_annealed_eq_physicalResponse hDim hp β (dim j+1)
    (modelRadius_pos (dim j)) (modelRadius_sq (dim j)) H uw
  have hd := dimensionResponseRow_eq_actual hp β H dim j (by omega) uw
  exact he.trans hd.symm

/-- Exact preceding source3.3 mean and response primitive clauses imply
the finite row primitive limits required for the Fisher transfer. -/
theorem actual_rowPrimitive_dimension_limit (hp : 2≤p) (β : ℝ≥0)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (d : CKData) (h : CKEquations p β d)
    (hmean : MeanBridge (p:=p) β dim (fun j => dim j+1) (fun j => modelRadius_pos (dim j)) d)
    (hresponse : ResponsePrimitiveBridge hp β dim d)
    {t s : ℝ} (hs : 0≤s) (hst : s≤t) :
    Tendsto (fun j => ActualSphereAnnealedFDT.annealedRowPrimitive (N:=dim j) (p:=p)
      β (dim j+1) (modelRadius_pos (dim j)) t s) atTop (𝓝 (ckRowPrimitive d t s)) := by
  have ht := hs.trans hst
  have hcS := (hmean t ht).tendsto_at (show (t,s)∈square t from ⟨⟨ht,le_rfl⟩,hs,hst⟩)
  have hc0 := (hmean t ht).tendsto_at (show (t,0)∈square t from ⟨⟨ht,le_rfl⟩,le_rfl,ht⟩)
  have hr := (hresponse ⟨t,ht⟩).tendsto_at
    (show (t,s)∈WeightedPrimitiveConvergence.compactTriangle t from ⟨⟨ht,le_rfl⟩,hs,hst⟩)
  have hiC : IntervalIntegrable (fun u => clampedResponse d t u) volume 0 s :=
    ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 s
  have heR j : (∫u in (0:ℝ)..s,dimensionResponseRow hp β dim j t u-d.R t u)=
      (∫u in (0:ℝ)..s,dimensionResponseRow hp β dim j t u)-
        (∫u in (0:ℝ)..s,clampedResponse d t u) := by
    have hiR := (responseRow_integrable hp β (dim j-1) ht).mono_set
      (show uIcc (0:ℝ) s⊆uIcc 0 t from by
        rw [uIcc_of_le hs,uIcc_of_le ht]
        exact Icc_subset_Icc le_rfl hst)
    calc
      _=(∫u in (0:ℝ)..s,dimensionResponseRow hp β dim j t u-clampedResponse d t u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu' : u∈Icc (0:ℝ) s := by simpa only [uIcc_of_le hs] using hu
        dsimp only
        rw [clampedResponse_eq hu'.1 (hu'.2.trans hst)]
      _=_ := intervalIntegral.integral_sub hiR hiC
  simp_rw [heR] at hr
  have hr' := hr.add_const (∫u in (0:ℝ)..s,clampedResponse d t u)
  simp only [sub_add_cancel,zero_add] at hr'
  have he j : ActualSphereAnnealedFDT.annealedRowPrimitive (N:=dim j) (p:=p)
      β (dim j+1) (modelRadius_pos (dim j)) t s=
      actualMean (N:=dim j) (p:=p) β (dim j+1) (modelRadius_pos (dim j)) t s-
        actualMean (N:=dim j) (p:=p) β (dim j+1) (modelRadius_pos (dim j)) t 0-
        (∫u in (0:ℝ)..s,dimensionResponseRow hp β dim j t u) :=
    canonical_rowPrimitive_eq_dimension hp β dim j (hDim j) ⟨t,ht⟩ ⟨s,hs⟩ hst
  simp_rw [he]
  exact (hcS.sub hc0).sub hr'

end SphericalAging.ActualSphereRowPrimitiveLimit
