module

public import SphericalAging.ActualSphereOnlyForkMomentTheorem

public section

/-! One genuine actual Fisher dimension subsequence supports the native
finite-fork comparison and every realizing stationary cluster. The
subsequence is selected before the cluster or its waiting-time sequence. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SphericalAging.ActualSphereOnlyForkRealization
open FiniteModel CKSpecification StationaryClusterInputs StrongBackwardDefect
open ActualForkL2Estimate ActualSphereRestrictedFisherBudget
open ActualSphereOnlyForkMomentTheorem ActualSphereOnlyForkMomentComparison
open ActualSphereOnlyForkUniformL2 ActualSphereCKBridges ActualSphereFisherTheorem
open AnnealedHamiltonianEnergyStein

/-- Actual extraction data and its already proved finite-fork consequences.
This is constructed below from the actual sphere SDE, rather than supplied
as a density, concentration, or stationary-limit premise. -/
structure Realization {p : ℕ} {β : ℝ≥0} {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) where
  extraction : ℕ→ℕ
  fisher : ℝ→ℝ
  strictMono : StrictMono extraction
  nonnegative : ∀s,0≤fisher s
  majorant : FisherMajorant p β d fisher
  localL1 : ∀t : ℝ,Tendsto (fun j => ∫w in Ioc 0 t,
    |full (N:=dim (extraction j)) (p:=p) β (dim (extraction j)+1)
      (modelRadius_pos (dim (extraction j))) w-fisher w|) atTop (𝓝 0)
  finiteComparison : ∀j,FiniteComparison (N:=dim (extraction j)) (p:=p) β
    (dim (extraction j)+1) (modelRadius_pos (dim (extraction j)))
  orderedUniformL2 : ∀{T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ},
    Cluster h T c r ell q→(∀n,0≤T n)→∀{L : ℝ},0≤L→∀{ε : ℝ},0<ε→
      ∀ᶠn in atTop,∀ᶠj in atTop,∀a∈Icc 0 L,∀b∈Icc 0 L,
        centeredError (N:=dim (extraction j)) (p:=p) β
          (dim (extraction j)+1) (modelRadius_pos (dim (extraction j)))
          (T n) a b (c (a+b))<ε
  stationaryL2 : ∀{T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ},
    Cluster h T c r ell q→(∀n,0≤T n)→
      StationaryL2Conclusion (p:=p) β (fun j => dim (extraction j))
        (fun j => dim (extraction j)+1)
        (fun j => modelRadius_pos (dim (extraction j))) T c

/-- A single actual dimension extraction suffices for all cluster profiles
and all realizing waiting sequences. Only the CK solution and a diverging
sequence of dimensions are supplied. -/
theorem exists_actual_realization {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j)
    (hTop : Tendsto dim atTop atTop) : Nonempty (Realization h dim) := by
  obtain ⟨φ,aF,hφ,han,hF,_hmass,_hac,_hclock,hFI,_hlate⟩ :=
    actual_FisherMajorant β h dim hDim hTop
  have htop : Tendsto (fun j => dim (φ j)) atTop atTop := hTop.comp hφ.tendsto_atTop
  have hd2 (j : ℕ) : 2≤dim (φ j) := by have hh:=hDim (φ j);omega
  have hbridge := canonical_MeanBridge h.spin_ge_three β h.beta_pos d h
    (fun j => dim (φ j)) htop
  refine ⟨⟨φ,aF,hφ,han,hF,hFI,?_,?_,?_⟩⟩
  · intro j a b e k hk
    exact actual_fork_moment_comparison (hd2 j) (by have hp:=h.spin_ge_three;omega)
      β (dim (φ j)+1) (modelRadius_pos (dim (φ j))) (modelRadius_sq (dim (φ j))) a b e hk
  · intro T c r ell q H hT L hL ε hε
    exact actual_fork_ordered_uniform_L2 H hT (fun j => dim (φ j)) hd2 htop
      (fun j => dim (φ j)+1) (fun j => modelRadius_pos (dim (φ j)))
      (fun j => modelRadius_sq (dim (φ j))) hbridge hF.integrable han hFI hL hε
  · intro T c r ell q H hT L hL
    exact actual_fork_overlap_concentration H hT (fun j => dim (φ j)) hd2 htop
      (fun j => dim (φ j)+1) (fun j => modelRadius_pos (dim (φ j)))
      (fun j => modelRadius_sq (dim (φ j))) hbridge hF.integrable han hFI hL

theorem Realization.dimension_ge_three {p : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {dim : ℕ→ℕ} (F : Realization h dim)
    (hDim : ∀j,3≤dim j) (j : ℕ) : 3≤dim (F.extraction j) := hDim (F.extraction j)

theorem Realization.dimension_tendsto {p : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {dim : ℕ→ℕ} (F : Realization h dim)
    (hTop : Tendsto dim atTop atTop) :
    Tendsto (fun j => dim (F.extraction j)) atTop atTop := hTop.comp F.strictMono.tendsto_atTop

end SphericalAging.ActualSphereOnlyForkRealization
