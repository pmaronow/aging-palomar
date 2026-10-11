module

public import SphericalAging.ThirdVariationalSDE
public import SphericalAging.OperatorTaylorRemainder

public section

/-! Exact third-flow Taylor error decomposition. The two mixed
first-response remainders retain fixed multipliers, so their true L²
little-o bounds do not require sixteenth moments. -/
noncomputable section
open scoped NNReal ContDiff
namespace SphericalAging.ThirdVariationPointwiseError
open HardSphereDynamics
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}
local instance : NormedAddCommGroup (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance

lemma bilinear_bound (H : State N→L[ℝ] State N→L[ℝ] ℝ) {L : ℝ}
    (hH : ‖H‖≤L) (u v : State N) : ‖H u v‖≤L*‖u‖*‖v‖ :=
  ((H u).le_opNorm v).trans (mul_le_mul_of_nonneg_right
    ((H.le_opNorm u).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _))) (norm_nonneg _))

lemma trilinear_bound (H : State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) {L : ℝ}
    (hH : ‖H‖≤L) (u v w : State N) : ‖H u v w‖≤L*‖u‖*‖v‖*‖w‖ :=
  bilinear_bound (H u) ((H.le_opNorm u).trans
      (mul_le_mul_of_nonneg_right hH (norm_nonneg _))) v w

/-- The literal Hessian-source derivative error has quadratic terms and
exactly two first-response remainders paired with fixed vectors. -/
theorem hessian_variation_error_bound {g : State N→ℝ} (hg : ContDiff ℝ ∞ g)
    {L M A : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ g))
    (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
    (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ (fderiv ℝ g))))
    (x y d ux uy vx vy qu qv : State N) :
    ‖fderiv ℝ (fderiv ℝ g) y uy vy-fderiv ℝ (fderiv ℝ g) x ux vx-
      fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x d ux vx-
      fderiv ℝ (fderiv ℝ g) x qu vx-fderiv ℝ (fderiv ℝ g) x ux qv‖≤
      (A:ℝ)*‖y-x‖^2*‖uy‖*‖vy‖+
      (M:ℝ)*‖y-x-d‖*‖uy‖*‖vy‖+
      (M:ℝ)*‖d‖*‖uy-ux‖*‖vy‖+
      (M:ℝ)*‖d‖*‖ux‖*‖vy-vx‖+
      (L:ℝ)*‖uy-ux-qu‖*‖vx‖+
      (L:ℝ)*‖uy-ux-qu‖*‖vy-vx‖+
      (L:ℝ)*‖qu‖*‖vy-vx‖+
      (L:ℝ)*‖ux‖*‖vy-vx-qv‖ := by
  let H := fderiv ℝ (fderiv ℝ g) x
  let Q := fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x
  let C := fderiv ℝ (fderiv ℝ g) y-H-Q (y-x)
  have hH : ‖H‖≤(L:ℝ) := norm_fderiv_le_of_lipschitz ℝ hL
  have hQ : ‖Q‖≤(M:ℝ) := norm_fderiv_le_of_lipschitz ℝ hM
  have hC : ‖C‖≤(A:ℝ)*‖y-x‖^2 := OperatorTaylorRemainder.taylor_remainder_bound
    ((hg.fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)) hA x y
  have he : fderiv ℝ (fderiv ℝ g) y uy vy-H ux vx-Q d ux vx-H qu vx-H ux qv=
      C uy vy+Q (y-x-d) uy vy+Q d (uy-ux) vy+Q d ux (vy-vx)+
      H (uy-ux-qu) vx+H (uy-ux-qu) (vy-vx)+H qu (vy-vx)+H ux (vy-vx-qv) := by
    dsimp [C]
    simp only [map_sub,ContinuousLinearMap.sub_apply]
    ring
  rw [he]
  have ht : ‖C uy vy+Q (y-x-d) uy vy+Q d (uy-ux) vy+Q d ux (vy-vx)+
      H (uy-ux-qu) vx+H (uy-ux-qu) (vy-vx)+H qu (vy-vx)+H ux (vy-vx-qv)‖≤
      ‖C uy vy‖+‖Q (y-x-d) uy vy‖+‖Q d (uy-ux) vy‖+‖Q d ux (vy-vx)‖+
      ‖H (uy-ux-qu) vx‖+‖H (uy-ux-qu) (vy-vx)‖+‖H qu (vy-vx)‖+‖H ux (vy-vx-qv)‖ := by
    calc
      _ ≤ ‖C uy vy+Q (y-x-d) uy vy+Q d (uy-ux) vy+Q d ux (vy-vx)+H (uy-ux-qu) vx+H (uy-ux-qu) (vy-vx)+H qu (vy-vx)‖+‖H ux (vy-vx-qv)‖ := norm_add_le _ _
      _ ≤ _ := by
        gcongr
        calc
          _ ≤ ‖C uy vy+Q (y-x-d) uy vy+Q d (uy-ux) vy+Q d ux (vy-vx)+H (uy-ux-qu) vx+H (uy-ux-qu) (vy-vx)‖+‖H qu (vy-vx)‖ := norm_add_le _ _
          _ ≤ _ := by
            gcongr
            calc
              _ ≤ ‖C uy vy+Q (y-x-d) uy vy+Q d (uy-ux) vy+Q d ux (vy-vx)+H (uy-ux-qu) vx‖+‖H (uy-ux-qu) (vy-vx)‖ := norm_add_le _ _
              _ ≤ _ := by
                gcongr
                calc
                  _ ≤ ‖C uy vy+Q (y-x-d) uy vy+Q d (uy-ux) vy+Q d ux (vy-vx)‖+‖H (uy-ux-qu) vx‖ := norm_add_le _ _
                  _ ≤ _ := by
                    gcongr
                    calc
                      _ ≤ ‖C uy vy+Q (y-x-d) uy vy+Q d (uy-ux) vy‖+‖Q d ux (vy-vx)‖ := norm_add_le _ _
                      _ ≤ _ := by
                        gcongr
                        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
  apply ht.trans
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (by simpa only [mul_assoc] using bilinear_bound C hC uy vy)
    (trilinear_bound Q hQ (y-x-d) uy vy))
    (trilinear_bound Q hQ d (uy-ux) vy))
    (trilinear_bound Q hQ d ux (vy-vx)))
    (bilinear_bound H hH (uy-ux-qu) vx))
    (bilinear_bound H hH (uy-ux-qu) (vy-vx)))
    (bilinear_bound H hH qu (vy-vx)))
    (bilinear_bound H hH ux (vy-vx-qv))

end SphericalAging.ThirdVariationPointwiseError
