module

public import SphericalAging.OrthogonalForkSupremumTransport

public section

/-! The published normalized spatial modulus in Huang--Sellke Lemma 3.1,
derived for the actual ordered pure-p fork Hamiltonian. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.OrthogonalForkSpatialModulus
open Set MeasureTheory FiniteModel GaussianLandscape GaussianOrthogonalForkCovariance
  OrthogonalForkSupremumTransport
variable {N p K : ℕ}

theorem actual_source_HS_3_1 (hN : 0<N) (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (a b δ r q ι : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hδ : 0<δ) (hδr : δ≤r) (hrq : r≤q) (hq1 : q≤1) (hι : 0≤ι)
    (x x' : Vector N) (hxnorm : ‖x‖^2=(N:ℝ)*r) (hxx' : ‖x‖=‖x'‖)
    (hdist : ‖x-x'‖≤ι*Real.sqrt N) (J : ForkDisorder N p K)
    (R : ℝ) (hR : 0≤R) (hland : ∀i,landscapeNorm N p (J i)≤R) :
    |GaussianFixedBaseForkConcentration.supremum a b r q x J-
      GaussianFixedBaseForkConcentration.supremum a b r q x' J|≤
      12*(p:ℝ)*R*ι/Real.sqrt δ := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hsN : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNr
  have hsδ : 0<Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hnorm : Real.sqrt N*Real.sqrt δ≤‖x‖ := by
    calc
      _=Real.sqrt ((N:ℝ)*δ) := (Real.sqrt_mul hNr.le δ).symm
      _≤Real.sqrt ((N:ℝ)*r) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hδr hNr.le)
      _=‖x‖ := by rw [←hxnorm,Real.sqrt_sq (norm_nonneg _)]
  have hxpos : 0<‖x‖ := (mul_pos hsN hsδ).trans_le hnorm
  have hx : x≠0 := norm_pos_iff.mp hxpos
  have hratio : ‖x-x'‖/‖x‖≤ι/Real.sqrt δ := by
    calc
      _≤ι*Real.sqrt N/‖x‖ := div_le_div_of_nonneg_right hdist hxpos.le
      _≤ι*Real.sqrt N/(Real.sqrt N*Real.sqrt δ) :=
        div_le_div_of_nonneg_left (mul_nonneg hι hsN.le) (mul_pos hsN hsδ) hnorm
      _=_ := by field_simp
  have hh := actual_fixedBase_supremum_transport_bound hN hp hK hKN a b r q ha hab hb
    (hδ.le.trans hδr) hrq hq1 x x' hxnorm hxx' hx J R hR hland
  apply hh.trans
  have ht := mul_le_mul_of_nonneg_left hratio
    (show 0≤12*(p:ℝ)*R by positivity)
  convert ht using 1 <;> ring

end SphericalAging.OrthogonalForkSpatialModulus
