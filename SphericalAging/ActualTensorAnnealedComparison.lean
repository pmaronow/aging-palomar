module

public import SphericalAging.ActualSphereTensorCutoffCurrent
public import SphericalAging.ForkFisherMomentTransfer

public section

/-! The exact finite annealed comparison for the literal actual tensor
semigroup product. All derivative, gradient and Fisher estimates come
from the actual SDE and honest positive forward density. -/
noncomputable section
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualTensorAnnealedComparison
open Set Filter MeasureTheory FiniteModel GaussianLandscape SphereFisherHelly
open SphereBadEventFisherMass SphereGoodEventFisherClock
open ActualSphereTensorProductCurrent ActualSphereTensorCurrentBounds ActualSphereTensorCutoffCurrent
open scoped Topology NNReal

theorem actualTensorPairing_annealed_comparison {N p k : ℕ}
    (hN : 2≤N) (hp : 2≤p) (hk : 1≤k) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (E : FisherDensity N p β)
    {T a d : ℝ} (hT : 0≤T) (ha : 0≤a) (hd : 0≤d)
    (hmeas : AEStronglyMeasurable (fun J =>
      actualTensorPairing (k:=k) β R hR E J T a d a-
        actualTensorPairing (k:=k) β R hR E J T a d 0) (disorderLaw N p)) :
    |∫J,actualTensorPairing (k:=k) β R hR E J T a d a-
      actualTensorPairing (k:=k) β R hR E J T a d 0 ∂disorderLaw N p|≤
      (2*(k:ℝ)*Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*(a+d)))*
        Real.sqrt (a*(∫w in T..(T+a),E.full w))+2*Real.exp (-(N:ℝ)) := by
  have hn : 0<N := by omega
  let F (J : Disorder N p) (w : ℝ) := actualTensorPairing (k:=k) β R hR E J T a d (w-T)
  let D (J : Disorder N p) (w : ℝ) := actualTensorCurrent (k:=k) β R hR E J T a d (w-T)
  have hF J : Continuous (F J) :=
    (actualTensorPairing_continuous hn β R hR E J T a d).comp (continuous_id.sub continuous_const)
  have hD J : Continuous (D J) :=
    (actualTensorCurrent_continuous hn β R hR E J T a d).comp (continuous_id.sub continuous_const)
  have hder J w (hw : w∈Ioo T (T+a)) : HasDerivAt (F J) (D J w) w := by
    have hh := (actualTensorPairing_hasDerivAt (k:=k) hn β R hR hNR E J T a d (w-T)
      (by linarith [hw.1]) (by linarith [hw.2]) (by linarith [hw.1])).comp w
        ((hasDerivAt_id w).sub_const T)
    convert hh using 1 <;> simp only [mul_one,F,D,Function.comp_def,id_eq]
  have hA : 0≤cutoff p := by unfold cutoff;linarith [landscapeThreshold_pos p]
  have hbound J (hJ : J∈goodEvent N p (cutoff p)) w (hw : w∈Icc T (T+a)) :
      (D J w)^2≤(2*(k:ℝ)*Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*(a+d)))^2*
        (SphereRotationGeometry.fisherInformation β J (E.ρ J w)/(N:ℝ)) := by
    have hh := actualTensorCurrent_square_bound_cutoff hn hp hk β R hR hNR E J T a d
      (cutoff p) hT hd hA hJ (show w-T∈Icc 0 a by constructor <;> linarith [hw.1,hw.2])
    have he : T+(w-T)=w := by ring
    simpa only [he,D] using hh
  have hδ : AEStronglyMeasurable (fun J => F J (T+a)-F J T) (disorderLaw N p) := by
    simpa only [F,add_sub_cancel_left,sub_self] using hmeas
  have habs J : |F J (T+a)-F J T|≤2 := by
    dsimp only [F]
    rw [add_sub_cancel_left,sub_self]
    have h1 := actualTensorPairing_abs_le_one (k:=k) hn β R hR hNR E J T a d a (by linarith)
    have h0 := actualTensorPairing_abs_le_one (k:=k) hn β R hR hNR E J T a d 0 (by linarith)
    exact (abs_sub _ _).trans (by linarith)
  have hh := ForkFisherMomentTransfer.annealed_current_increment_bound hN (by omega : 1≤p)
    β.coe_nonneg E hT (by linarith : T≤T+a) (by positivity : 0≤2*(k:ℝ)*Real.exp
      ((β:ℝ)*(p:ℝ)^2*cutoff p*(a+d))) hF hD hder hbound hδ habs
  simpa only [F,add_sub_cancel_left,sub_self,add_sub_cancel_left] using hh

end SphericalAging.ActualTensorAnnealedComparison
