module

public import SphericalAging.JointLpRepresentative
public import Mathlib.Analysis.Convex.Integral

public section

/-! A higher-Lp ball is closed and convex in the actual L² topology.
This permits genuine L²-valued FTC integrals to retain higher moments. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal
namespace SphericalAging.LpTwoHigherBall
set_option maxHeartbeats 240000
set_option backward.isDefEq.respectTransparency false
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {μ : Measure Ω}

@[expose] def higherBall (p C : ℝ≥0∞) : Set (Lp E 2 μ) := {x | eLpNorm (x : Ω→E) p μ≤C}

theorem higherBall_closed (p C : ℝ≥0∞) : IsClosed (higherBall (E:=E) (μ:=μ) p C) := by
  have hh : IsSeqClosed (higherBall (E:=E) (μ:=μ) p C) := by
    intro f x hf hlim
    obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
    exact Lp.eLpNorm_le_of_ae_tendsto (.of_forall (fun n => hf (ns n)))
      (fun n => Lp.aestronglyMeasurable (f (ns n))) (Lp.aestronglyMeasurable x) hae
  exact hh.isClosed

theorem higherBall_convex (p C : ℝ≥0∞) (hp : 1≤p) : Convex ℝ (higherBall (E:=E) (μ:=μ) p C) := by
  intro x hx y hy a b ha hb hab
  have he : ((a • x+b • y : Lp E 2 μ):Ω→E)=ᵐ[μ] a • (x:Ω→E)+b • (y:Ω→E) := by
    filter_upwards [Lp.coeFn_add (a • x) (b • y),Lp.coeFn_smul a x,Lp.coeFn_smul b y]
      with omega hsum hx hy
    rw [hsum,Pi.add_apply,hx,hy]
    rfl
  change eLpNorm ((a • x+b • y : Lp E 2 μ):Ω→E) p μ≤C
  rw [eLpNorm_congr_ae he]
  calc
    _≤eLpNorm (a • (x:Ω→E)) p μ+eLpNorm (b • (y:Ω→E)) p μ := eLpNorm_add_le hp
    _=ENNReal.ofReal a*eLpNorm (x:Ω→E) p μ+ENNReal.ofReal b*eLpNorm (y:Ω→E) p μ := by
      rw [eLpNorm_const_smul,eLpNorm_const_smul]
      simp only [←ofReal_norm,Real.norm_of_nonneg ha,Real.norm_of_nonneg hb]
    _≤ENNReal.ofReal a*C+ENNReal.ofReal b*C := add_le_add (mul_le_mul_right hx _) (mul_le_mul_right hy _)
    _=C := by rw [←add_mul,←ENNReal.ofReal_add ha hb,hab];simp

variable [CompleteSpace E]

theorem integral_higherBall {A : Type*} [MeasurableSpace A] {ν : Measure A} [IsProbabilityMeasure ν]
    (F : A→Lp E 2 μ) (hF : Integrable F ν) (p C : ℝ≥0∞) (hp : 1≤p)
    (hbound : ∀ᵐa∂ν,eLpNorm (F a : Ω→E) p μ≤C) :
    eLpNorm ((∫a,F a∂ν : Lp E 2 μ):Ω→E) p μ≤C :=
  (higherBall_convex (E:=E) (μ:=μ) p C hp).integral_mem (higherBall_closed (E:=E) (μ:=μ) p C) hbound hF

end SphericalAging.LpTwoHigherBall
