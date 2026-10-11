module

public import SphericalAging.PositiveFrameTrace
public import SphericalAging.DisjointCausalStripTheorem
public import SphericalAging.TreeCoherentOperator
public import SphericalAging.CenterNormalization

public section

/-! Literal cubic prefix root frames and their old/recent splitting in the
actual completed Hilbert--Schmidt space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set Filter MeasureTheory UniformSpace
open scoped InnerProductSpace TensorProduct Topology
namespace SphericalAging.ActualCausalRootFrame
open CausalTree CausalTree.HilbertDatum CKSpecification CKPhysicalConsequences
open CausalTreeRealization PrefixReflection TreeRootBlocks TreeCoherentOperator
open DisjointCausalStrips CausalStripDistance CenterNormalization CausalCenterAverage

theorem standardTensorPower_binary (x : Space 2) : standardTensorPower x=binaryPure x x := by
  unfold standardTensorPower binaryPure
  congr 1
  funext i
  fin_cases i <;> rfl

@[expose] def projectedRankOne {β : ℝ} {d : CKData} (h : CKEquations 3 β d) (T u : ℝ) :
    (tensor (spaceDatum 2) (spaceDatum 2)).Carrier :=
  pure _ _ (prefixVector h T u) (prefixVector h T u)

theorem projectedRankOne_clamped_continuous {β : ℝ} {d : CKData}
    (h : CKEquations 3 β d) (T : ℝ) : Continuous (fun u => projectedRankOne h T (max 0 u)) := by
  have hp := prefixVector_clamped_continuous h (physical_bounds_of_equations h) T
  exact (Completion.continuous_coe _).comp (TensorProduct.continuous_tmul.comp (hp.prodMk hp))

theorem projectedRankOne_continuousOn {β : ℝ} {d : CKData}
    (h : CKEquations 3 β d) (T : ℝ) : ContinuousOn (projectedRankOne h T) (Ici 0) := by
  apply (projectedRankOne_clamped_continuous h T).continuousOn.congr
  intro u hu
  change 0≤u at hu
  simp only [max_eq_right hu]

theorem projected_row_intervalIntegrable {β : ℝ} {d : CKData}
    (h : CKEquations 3 β d) (T : ℝ) {a b t : ℝ}
    (ha : 0≤a) (hab : a≤b) (hbt : b≤t) :
    IntervalIntegrable (fun u => d.R t u • projectedRankOne h T u) volume a b :=
  ((CausalStripIntegralBound.response_continuousOn_interval h ha hbt).smul
    ((projectedRankOne_continuousOn h T).mono (fun u hu => ha.trans hu.1))).intervalIntegrable_of_Icc hab

theorem prefix_root_frame {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {t : ℝ} (ht : 0≤t) (T : ℝ) :
    rootHS (prefixVector h T t) = (β*Real.sqrt 3) •
      ∫ u in (0:ℝ)..t,d.R t u • projectedRankOne h T u := by
  have hf := ckTreeState_prefix_root_frame_original h (physical_bounds_of_equations h) ht T
  change binaryEquiv (graftTensorAdjoint 2 (timePrefix T (ckTreeState h t))) = _
  simp only [Nat.reduceSub,Nat.cast_ofNat] at hf
  rw [hf,map_smul]
  have hi := binaryEquiv.toLinearIsometry.intervalIntegral_comp_comm
    (fun u => d.R t u • standardTensorPower (timePrefix T (ckTreeState h u))) (a:=0) (b:=t) (μ:=volume)
  apply congrArg (fun z => (β*Real.sqrt 3) • z)
  calc
    binaryEquiv (∫u in (0:ℝ)..t,d.R t u • standardTensorPower (timePrefix T (ckTreeState h u))) =
        ∫u in (0:ℝ)..t,binaryEquiv (d.R t u • standardTensorPower (timePrefix T (ckTreeState h u))) := hi.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only
      rw [map_smul,standardTensorPower_binary,binaryEquiv_pure]
      rfl

theorem rootHS_smul (a : ℝ) (x : Space 2) : rootHS (a • x)=a • rootHS x := by
  simp only [rootHS,map_smul]

@[expose] def recentRootRow {β : ℝ} {d : CKData} (h : CKEquations 3 β d) (t T : ℝ) :=
  ∫ u in T..t,d.R t u • projectedRankOne h T u

theorem prefix_root_split {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {T t : ℝ} (hT : 0≤T) (hTt : T≤t) :
    rootHS (prefixVector h T t)=(β*Real.sqrt 3) •
      (stateOperatorRow h t T+recentRootRow h t T) := by
  rw [prefix_root_frame h (hT.trans hTt),
    ←intervalIntegral.integral_add_adjacent_intervals
      (projected_row_intervalIntegrable h T le_rfl hT hTt)
      (projected_row_intervalIntegrable h T hT hTt le_rfl)]
  congr 2
  unfold stateOperatorRow
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hT] at hu
  have hc : prefixVector h T u=ckTreeState h u :=
    ckTreeState_timePrefix h (physical_bounds_of_equations h) hu.1 hu.2
  change d.R t u • pure (spaceDatum 2) (spaceDatum 2) (prefixVector h T u) (prefixVector h T u) = _
  rw [hc]
  rfl

theorem normalized_root_split {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {L t : ℝ} (hT : 0≤t-L) (hL : 0≤L) :
    rootHS (normalizedCenter h t L)=
      (β*Real.sqrt 3/‖prefixVector h (t-L) t‖) •
        (stateOperatorRow h t (t-L)+recentRootRow h t (t-L)) := by
  have he : localCenter h (t-L) L=prefixVector h (t-L) t := by
    unfold localCenter
    rw [sub_add_cancel]
  rw [normalizedCenter,he,unitize,rootHS_smul,prefix_root_split h hT (by linarith),smul_smul]
  congr 1
  ring

end SphericalAging.ActualCausalRootFrame
