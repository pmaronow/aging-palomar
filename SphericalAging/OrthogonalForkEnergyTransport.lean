module

public import SphericalAging.OrthogonalForkBasepointTransport

public section

/-! The actual same-disorder energy displacement bound of Huang--Sellke
Lemma 3.1, with its landscape event explicit. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.OrthogonalForkEnergyTransport
open Set MeasureTheory FiniteModel GaussianLandscape ForkEnergyComparison
  GaussianOrthogonalForkCovariance CloseOrthogonalTransport OrthogonalForkBasepointTransport
open scoped InnerProductSpace BigOperators
variable {N p K : ℕ}

theorem actual_averagedIncrement_transport_bound (hN : 0<N) (hK : 0<K)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (x x' : Vector N) (hxx' : ‖x‖=‖x'‖) (hx : x≠0)
    (y : Fin K→Vector N) (r q : ℝ) (hr1 : r≤1) (hq1 : q≤1)
    (hf : OrthogonalFork x y r q) (J : ForkDisorder N p K)
    (R : ℝ) (hR : 0≤R) (hland : ∀i,landscapeNorm N p (J i)≤R) :
    |averagedIncrement a b x y J-
      averagedIncrement a b x' (fun i => transport x x' (y i)) J|≤
      12*(p:ℝ)*R*‖x-x'‖/‖x‖ := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hKr : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  have hxb : ‖x‖≤Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    rw [hf.base_norm]
    nlinarith
  have hyb i : ‖y i‖≤Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    rw [hf.leaf_norm i]
    nlinarith
  let B := 4*(p:ℝ)*R*(N:ℝ)*‖x-x'‖/‖x‖
  have hB : 0≤B := by dsimp only [B];positivity
  have hH (i : Option (Fin K)) (z : Vector N) (hz : ‖z‖≤Real.sqrt N) :
      |Hamiltonian N p (J i) z-Hamiltonian N p (J i) (transport x x' z)|≤B := by
    apply (Hamiltonian_transport_difference hN (J i) x x' z hx hz).trans
    dsimp only [B]
    gcongr
    exact hland i
  have hbase := hH none x hxb
  rw [transport_base hxx'] at hbase
  have hs0 : 0≤Real.sqrt a := Real.sqrt_nonneg _
  have hs1 : Real.sqrt a≤1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith
  have ht0 : 0≤Real.sqrt (b-a) := Real.sqrt_nonneg _
  have ht1 : Real.sqrt (b-a)≤1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith
  have hi (i : Fin K) : |increment a b x y i J-
      increment a b x' (fun j => transport x x' (y j)) i J|≤3*B := by
    have hleaf := hH none (y i) (hyb i)
    have hfresh := hH (some i) (y i) (hyb i)
    have he : increment a b x y i J-increment a b x' (fun j => transport x x' (y j)) i J=
        Real.sqrt a*((Hamiltonian N p (J none) (y i)-
          Hamiltonian N p (J none) (transport x x' (y i)))-
            (Hamiltonian N p (J none) x-Hamiltonian N p (J none) x'))+
        Real.sqrt (b-a)*(Hamiltonian N p (J (some i)) (y i)-
          Hamiltonian N p (J (some i)) (transport x x' (y i))) := by
      simp only [increment,sharedIncrement,block]
      ring
    rw [he]
    calc
      _≤|Real.sqrt a*((Hamiltonian N p (J none) (y i)-
          Hamiltonian N p (J none) (transport x x' (y i)))-
            (Hamiltonian N p (J none) x-Hamiltonian N p (J none) x'))|+
        |Real.sqrt (b-a)*(Hamiltonian N p (J (some i)) (y i)-
          Hamiltonian N p (J (some i)) (transport x x' (y i)))| := abs_add_le _ _
      _≤Real.sqrt a*(B+B)+Real.sqrt (b-a)*B := by
        rw [abs_mul,abs_mul,abs_of_nonneg hs0,abs_of_nonneg ht0]
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ hs0
          exact (abs_sub _ _).trans (add_le_add hleaf hbase)
        · exact mul_le_mul_of_nonneg_left hfresh ht0
      _≤3*B := by nlinarith
  have hsum : |∑i,increment a b x y i J-
      ∑i,increment a b x' (fun j => transport x x' (y j)) i J|≤(K:ℝ)*(3*B) := by
    rw [←Finset.sum_sub_distrib]
    calc
      _≤∑i,|increment a b x y i J-increment a b x' (fun j => transport x x' (y j)) i J| :=
        Finset.abs_sum_le_sum_abs _ _
      _≤∑_i : Fin K,3*B := Finset.sum_le_sum (fun i _ => hi i)
      _=_ := by simp
  rw [averagedIncrement,averagedIncrement,←sub_div,abs_div,abs_of_pos (mul_pos hKr hNr)]
  apply (div_le_div_of_nonneg_right hsum (mul_pos hKr hNr).le).trans_eq
  dsimp only [B]
  field_simp
  ring

end SphericalAging.OrthogonalForkEnergyTransport
