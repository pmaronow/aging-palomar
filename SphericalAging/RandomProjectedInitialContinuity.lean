module

public import SphericalAging.RandomInitialDependence
public import SphericalAging.HamiltonianPicardDependence
public import SphericalAging.ProjectedRandomFlowDerivative

public section

/-! Genuine L² continuity of the projected finite-parameter initial data.
The globally Lipschitz cutoff noise columns give a continuous class map;
on the physical sphere it is exactly Z₀+P_{Z₀}v. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.RandomProjectedInitialContinuity
open HardSphereDynamics RandomInitialDependence HamiltonianPicardDependence
open HamiltonianParameter LocalSDE
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma centeredLipschitz {K : ℝ≥0} {g : State N → ℝ} (hg : LipschitzWith K g) :
    LipschitzWith K (fun x => g x-g 0) :=
  LipschitzWith.of_dist_le_mul (fun x y => by
    simpa only [dist_eq_norm,sub_sub_sub_cancel_right] using hg.dist_le_mul x y)

/-- Continuous Nemytskii class on the actual initial sigma-algebra,
including a nonzero constant term. -/
@[expose] def nonlinearClass {K : ℝ≥0} {g : State N → ℝ} (hg : LipschitzWith K g)
    (Z : InitialSpace N F P) : lpMeas ℝ ℝ (F 0) 2 P :=
  let h0 : (fun x => g x-g 0) (0 : State N)=0 := sub_self _
  let Y := (centeredLipschitz hg).compLp h0 (Z : Lp (State N) 2 P)+Lp.const 2 P (g 0)
  ⟨Y,by
    have hy : (Y : Ω → ℝ)=ᵐ[P] (fun ω => g ((Z : Lp (State N) 2 P) ω)) := by
      filter_upwards [Lp.coeFn_add ((centeredLipschitz hg).compLp h0 (Z : Lp (State N) 2 P))
          (Lp.const 2 P (g 0)),(centeredLipschitz hg).coeFn_compLp h0 (Z : Lp (State N) 2 P),
        Lp.coeFn_const 2 P (g 0)] with ω hadd hcomp hc
      rw [hadd,Pi.add_apply,hcomp,hc]
      simp only [Function.comp_def,Function.const_apply,sub_add_cancel]
    exact (hg.continuous.comp_aestronglyMeasurable (lpMeas.aestronglyMeasurable Z)).congr hy.symm⟩

lemma nonlinearClass_ae {K : ℝ≥0} {g : State N → ℝ} (hg : LipschitzWith K g)
    (Z : InitialSpace N F P) :
    (nonlinearClass hg Z : Lp ℝ 2 P)=ᵐ[P] (fun ω => g ((Z : Lp (State N) 2 P) ω)) := by
  let h0 : (fun x => g x-g 0) (0 : State N)=0 := sub_self _
  filter_upwards [Lp.coeFn_add ((centeredLipschitz hg).compLp h0 (Z : Lp (State N) 2 P))
      (Lp.const 2 P (g 0)),(centeredLipschitz hg).coeFn_compLp h0 (Z : Lp (State N) 2 P),
    Lp.coeFn_const 2 P (g 0)] with ω hadd hcomp hc
  change (((centeredLipschitz hg).compLp h0 (Z : Lp (State N) 2 P)+Lp.const 2 P (g 0)) : Lp ℝ 2 P) ω=_
  rw [hadd,Pi.add_apply,hcomp,hc]
  simp only [Function.comp_def,Function.const_apply,sub_add_cancel]

lemma nonlinearClass_continuous {K : ℝ≥0} {g : State N → ℝ} (hg : LipschitzWith K g) :
    Continuous (nonlinearClass (F := F) (P := P) hg) := by
  apply continuous_induced_rng.mpr
  exact (((centeredLipschitz hg).continuous_compLp (sub_self _)).comp continuous_subtype_val).add continuous_const

@[expose] def stateInclusion (i : Fin N) : lpMeas ℝ ℝ (F 0) 2 P →L[ℝ] InitialSpace N F P :=
  (((ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).compLpL 2 P).domRestrict
    (lpMeas ℝ ℝ (F 0) 2 P)).codRestrict (InitialSpace N F P) (fun Z => by
      apply ((lpMeas.aestronglyMeasurable Z).smul_const (basisVector i)).congr
      have h := (ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).coeFn_compLpL (Z : Lp ℝ 2 P)
      filter_upwards [h] with ω hw
      simpa only [ContinuousLinearMap.toSpanSingleton_apply,ContinuousLinearMap.domRestrict_apply] using hw.symm)

@[expose] def noiseColumnClass (R : ℝ≥0) (hR : 0<(R : ℝ)) (j : Fin N)
    (Z : InitialSpace N F P) : InitialSpace N F P :=
  ∑ i : Fin N,stateInclusion i (nonlinearClass (noise_family_lipschitz N R hR i j) Z)

lemma noiseColumnClass_continuous (R : ℝ≥0) (hR : 0<(R : ℝ)) (j : Fin N) :
    Continuous (noiseColumnClass (F := F) (P := P) R hR j) :=
  continuous_finsetSum Finset.univ (fun i _ => (stateInclusion i).continuous.comp
    (nonlinearClass_continuous (noise_family_lipschitz N R hR i j)))

lemma noiseColumnClass_ae (R : ℝ≥0) (hR : 0<(R : ℝ)) (j : Fin N)
    (Z : InitialSpace N F P) :
    (noiseColumnClass R hR j Z : Lp (State N) 2 P)=ᵐ[P]
      (fun ω => WithLp.toLp 2 (fun i => CutoffSDE.cutoffNoise N R hR i j ((Z : Lp (State N) 2 P) ω))) := by
  have hs : ((noiseColumnClass R hR j Z : InitialSpace N F P) : Lp (State N) 2 P)=ᵐ[P]
      (fun ω => ∑ i : Fin N,((stateInclusion i (nonlinearClass (noise_family_lipschitz N R hR i j) Z) : InitialSpace N F P) : Lp (State N) 2 P) ω) := by
    simpa only [noiseColumnClass,Submodule.coe_sum] using Lp.coeFn_fun_finsetSum Finset.univ
      (fun i => ((stateInclusion i (nonlinearClass (noise_family_lipschitz N R hR i j) Z) : InitialSpace N F P) : Lp (State N) 2 P))
  have hi := ae_all_iff.mpr (fun i : Fin N => (ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).coeFn_compLp
    (nonlinearClass (noise_family_lipschitz N R hR i j) Z : Lp ℝ 2 P))
  have hn := ae_all_iff.mpr (fun i : Fin N => nonlinearClass_ae (noise_family_lipschitz N R hR i j) Z)
  filter_upwards [hs,hi,hn] with ω hsum hinc hnoise
  rw [hsum]
  calc
    _ = ∑ i : Fin N,(CutoffSDE.cutoffNoise N R hR i j ((Z : Lp (State N) 2 P) ω)) • basisVector i := by
      apply Finset.sum_congr rfl
      intro i _
      change ((ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).compLp
        (nonlinearClass (noise_family_lipschitz N R hR i j) Z : Lp ℝ 2 P)) ω=_
      rw [hinc i,hnoise i]
      rfl
    _ = _ := state_sum_basis _

@[expose] def projectedParameterClass (R : ℝ≥0) (hR : 0<(R : ℝ))
    (q : InitialSpace N F P × State N) : InitialSpace N F P :=
  q.1+(Real.sqrt 2)⁻¹ • ∑ j : Fin N,(q.2 j) • noiseColumnClass R hR j q.1

theorem projectedParameterClass_continuous (R : ℝ≥0) (hR : 0<(R : ℝ)) :
    Continuous (projectedParameterClass (N := N) (F := F) (P := P) R hR) := by
  have hs : Continuous (fun q : InitialSpace N F P × State N =>
      ∑ j : Fin N,(q.2 j) • noiseColumnClass R hR j q.1) := by
    apply continuous_finsetSum
    intro j _
    exact ((VariationalCoefficients.coordinate j).continuous.comp continuous_snd).smul
      ((noiseColumnClass_continuous R hR j).comp continuous_fst)
  convert continuous_fst.add (hs.const_smul (Real.sqrt 2)⁻¹) using 1
  funext q
  simp only [projectedParameterClass,Pi.add_apply,Pi.smul_apply]

/-- The continuous cutoff-column construction is the literal projected
initial perturbation along every sphere-valued random initial state. -/
theorem projectedParameterClass_initialStateClass (hN : N≠0)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)≤(R : ℝ)^2)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hm : MemLp Z0 2 P)
    (hSphere : ∀ᵐ ω ∂P,OnSphere (Z0 ω)) (v : State N) :
    projectedParameterClass R hR (initialStateClass Z0 hZ0 hm,v)=
      initialStateClass (ProjectedRandomFlowDerivative.parameterInitial Z0 v)
        (ProjectedRandomFlowDerivative.parameterInitial_stronglyMeasurable Z0 hZ0 v)
        (ProjectedRandomFlowDerivative.parameterInitial_memLp hN Z0 hZ0 hSphere hm v) := by
  let Z := initialStateClass Z0 hZ0 hm
  have hn (j : Fin N) : ((noiseColumnClass R hR j Z : InitialSpace N F P) : Lp (State N) 2 P)=ᵐ[P]
      (fun ω => noiseColumn (Z0 ω) j) := by
    filter_upwards [noiseColumnClass_ae R hR j Z,hm.coeFn_toLp,hSphere] with ω hc hz hx
    change (Z : Lp (State N) 2 P) ω=Z0 ω at hz
    rw [hc,hz]
    ext i
    change CutoffSDE.cutoffNoise N R hR i j (Z0 ω)=noiseColumn (Z0 ω) j i
    apply CutoffSDE.cutoffNoise_eq
    have hsq := (onSphere_iff_norm_sq _).mp hx
    nlinarith [norm_nonneg (Z0 ω),R.coe_nonneg]
  let S : Lp (State N) 2 P := ∑ j : Fin N,(v j) • (noiseColumnClass R hR j Z : Lp (State N) 2 P)
  have hs : (S : Ω → State N)=ᵐ[P] (fun ω => ∑ j : Fin N,(v j) • noiseColumn (Z0 ω) j) :=
    by
      have hsum := Lp.coeFn_fun_finsetSum Finset.univ
        (fun j : Fin N => (v j) • (noiseColumnClass R hR j Z : Lp (State N) 2 P))
      have hcols := ae_all_iff.mpr (fun j : Fin N =>
        (Lp.coeFn_smul (v j) (noiseColumnClass R hR j Z : Lp (State N) 2 P)).trans ((hn j).const_smul (v j)))
      filter_upwards [hsum,hcols] with ω hh hc
      rw [hh]
      exact Finset.sum_congr rfl (fun j _ => hc j)
  have hcoe : ((projectedParameterClass R hR (Z,v) : InitialSpace N F P) : Lp (State N) 2 P)=
      (Z : Lp (State N) 2 P)+(Real.sqrt 2)⁻¹ • S := by
    simp only [projectedParameterClass,Submodule.coe_add,Submodule.coe_smul,Submodule.coe_sum,S]
  apply Subtype.ext
  apply Lp.ext
  rw [hcoe]
  filter_upwards [Lp.coeFn_add (Z : Lp (State N) 2 P) ((Real.sqrt 2)⁻¹ • S),
    Lp.coeFn_smul (Real.sqrt 2)⁻¹ S,hs,hm.coeFn_toLp,
    (ProjectedRandomFlowDerivative.parameterInitial_memLp hN Z0 hZ0 hSphere hm v).coeFn_toLp]
    with ω hadd hsmul hsum hz hp
  change (Z : Lp (State N) 2 P) ω=Z0 ω at hz
  change ((initialStateClass (ProjectedRandomFlowDerivative.parameterInitial Z0 v)
    (ProjectedRandomFlowDerivative.parameterInitial_stronglyMeasurable Z0 hZ0 v)
    (ProjectedRandomFlowDerivative.parameterInitial_memLp hN Z0 hZ0 hSphere hm v) : InitialSpace N F P) :
      Lp (State N) 2 P) ω=ProjectedRandomFlowDerivative.parameterInitial Z0 v ω at hp
  rw [hadd,Pi.add_apply,hsmul,Pi.smul_apply,hsum,hz,hp]
  have hsumNoise : (∑ j : Fin N,(v j) • noiseColumn (Z0 ω) j)=
      Real.sqrt 2 • projection (Z0 ω) v := by
    calc
      _ = Real.sqrt 2 • (∑ j : Fin N,(v j) • projection (Z0 ω) (basisVector j)) := by
        simp only [noiseColumn,Finset.smul_sum,smul_smul,mul_comm]
      _ = Real.sqrt 2 • projection (Z0 ω) (∑ j : Fin N,(v j) • basisVector j) := by
        rw [projection_sum]
        simp only [projection_smul]
      _ = _ := by rw [state_sum_basis]
  rw [hsumNoise,smul_smul,inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2))),one_smul]
  rfl

end SphericalAging.RandomProjectedInitialContinuity
