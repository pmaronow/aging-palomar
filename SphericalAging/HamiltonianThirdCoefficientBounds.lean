module

public import SphericalAging.HamiltonianSecondCoefficientBounds

public section

/-! True global third-derivative Lipschitz bounds of the actual cutoff
Hamiltonian coefficients, obtained from their smooth compact supports. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HamiltonianThirdCoefficientBounds
open HardSphereDynamics VariationalCoefficients
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}
local instance : NormedAddCommGroup (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance

theorem third_derivative_lipschitz {g : State N→ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) : ∃L : ℝ≥0,LipschitzWith L (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) :=
  ContDiff.lipschitzWith_of_hasCompactSupport (hs.fderiv (𝕜:=ℝ) |>.fderiv (𝕜:=ℝ) |>.fderiv (𝕜:=ℝ))
    (((hg.fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)) (by simp)

theorem cutoffDrift_thirdDerivative_uniform_lipschitz (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0<R) : ∃L : ℝ≥0,∀i : Fin N,
      LipschitzWith L (fderiv ℝ (fderiv ℝ (fderiv ℝ (CutoffSDE.cutoffDrift β J R hR i)))) := by
  classical
  have hs (i : Fin N) : HasCompactSupport (CutoffSDE.cutoffDrift β J R hR i) :=
    (cutoffCoefficient_hasCompactSupport R hR (hamiltonianDrift β J)).comp_left
      (g:=fun x : State N => x i) (by rfl)
  choose L hL using (fun i : Fin N => third_derivative_lipschitz (cutoffDrift_contDiff β J R hR i) (hs i))
  exact ⟨∑i,L i,fun i => (hL i).weaken (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i))⟩

theorem cutoffNoise_thirdDerivative_uniform_lipschitz (R : ℝ) (hR : 0<R) :
    ∃L : ℝ≥0,∀i j : Fin N,
      LipschitzWith L (fderiv ℝ (fderiv ℝ (fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j)))) := by
  classical
  have hs (i j : Fin N) : HasCompactSupport (CutoffSDE.cutoffNoise N R hR i j) :=
    (cutoffCoefficient_hasCompactSupport R hR (fun x : State N => noiseColumn x j)).comp_left
      (g:=fun x : State N => x i) (by rfl)
  choose L hL using (fun q : Fin N×Fin N => third_derivative_lipschitz (cutoffNoise_contDiff R hR q.1 q.2) (hs q.1 q.2))
  exact ⟨∑q,L q,fun i j => (hL (i,j)).weaken (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ (i,j)))⟩
end SphericalAging.HamiltonianThirdCoefficientBounds
