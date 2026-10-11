module

public import SphericalAging.GaussianForkNetConcentration
public import SphericalAging.GaussianForkBasepointExpectation
public import SphericalAging.OrthogonalForkSpatialModulus
public import SphericalAging.GaussianLandscape

public section

/-! Actual uniform basepoint concentration for the ordered pure-p fork
supremum. The net, Gaussian supremum tails, same-disorder spatial modulus,
constant spherical expectation and landscape tails are all derived. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianForkUniformConcentration
open Set MeasureTheory ProbabilityTheory FiniteModel GaussianLandscape
open GaussianOrthogonalForkCovariance GaussianForkNetConcentration GaussianForkBasepointExpectation
open scoped BigOperators
variable {N p K : ℕ}

@[expose] def landscapeCeiling (p : ℕ) : ℝ := landscapeThreshold p+4
@[expose] def mesh (p : ℕ) (δ ε : ℝ) : ℝ := ε*Real.sqrt δ/(24*(p:ℝ)*landscapeCeiling p)

theorem fork_landscape_bad_bound (hN : 2≤N) (hp : 0<p) :
    (forkLaw N p K).real {J | ∃i,landscapeCeiling p<landscapeNorm N p (J i)}≤
      ((K:ℝ)+1)*Real.exp (-(N:ℝ)) := by
  have hs : {J : ForkDisorder N p K | ∃i,landscapeCeiling p<landscapeNorm N p (J i)}=
      ⋃i,{J | landscapeCeiling p<landscapeNorm N p (J i)} := by ext J;simp
  rw [hs]
  calc
    _≤∑i : Option (Fin K),(forkLaw N p K).real {J | landscapeCeiling p<landscapeNorm N p (J i)} :=
      measureReal_iUnion_fintype_le _
    _≤∑_i : Option (Fin K),Real.exp (-(N:ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      have hMeas : MeasurableSet {J : Disorder N p | landscapeCeiling p<landscapeNorm N p J} :=
        measurableSet_lt measurable_const (landscapeNorm_continuous N p).measurable
      have hh := (measurePreserving_eval (fun _ : Option (Fin K) => disorderLaw N p) i).hasLaw.measureReal_eq
        hMeas
      exact hh.trans_le (landscape_exponential_dimension_bound hN hp)
    _=_ := by simp

theorem actual_uniform_fork_probability_bound (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (a b δ r q ε : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hδ : 0<δ) (hδr : δ≤r) (hrq : r≤q) (hq1 : q≤1) (hε : 0<ε) :
    (forkLaw N p K).real {J | ∃x : Vector N,‖x‖^2=(N:ℝ)*r ∧
      ε≤|GaussianFixedBaseForkConcentration.supremum a b r q x J-
        ∫J',GaussianFixedBaseForkConcentration.supremum a b r q x J' ∂forkLaw N p K|}≤
      2*(1+2/mesh p δ ε)^N*Real.exp (-((K:ℝ)*N)*ε^2/(8*(Real.pi/2)^2))+
        ((K:ℝ)+1)*Real.exp (-(N:ℝ)) := by
  have hN : 0<N := by omega
  have hR : 0<landscapeCeiling p := by
    dsimp only [landscapeCeiling]
    linarith [landscapeThreshold_pos p]
  have hpReal : 0<(p:ℝ) := Nat.cast_pos.mpr (by omega)
  have hη : 0<mesh p δ ε := by dsimp only [mesh];positivity
  obtain ⟨S,hS,hcov,hcard,hNet⟩ := exists_sphere_net_concentration hp hK hKN a b r q ha hab hb
    (hδ.le.trans hδr) hrq hq1 (mesh p δ ε) (ε/2) hη (by positivity)
  let F := fun x J => GaussianFixedBaseForkConcentration.supremum (p:=p) (K:=K) a b r q x J-
    ∫J',GaussianFixedBaseForkConcentration.supremum a b r q x J' ∂forkLaw N p K
  let BadNet := {J : ForkDisorder N p K | ∃x∈S,ε/2≤|F x J|}
  let BadLandscape := {J : ForkDisorder N p K | ∃i,landscapeCeiling p<landscapeNorm N p (J i)}
  have hsubset : {J | ∃x : Vector N,‖x‖^2=(N:ℝ)*r ∧ ε≤|F x J|}⊆BadNet∪BadLandscape := by
    intro J hJ
    obtain ⟨x,hx,hdev⟩ := hJ
    by_cases hbad : J∈BadLandscape
    · exact Or.inr hbad
    have hland : ∀i,landscapeNorm N p (J i)≤landscapeCeiling p := by
      intro i
      exact le_of_not_gt (fun hi => hbad ⟨i,hi⟩)
    obtain ⟨y,hy,hxy⟩ := hcov x hx
    have hn : ‖x‖=‖y‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (hx.trans (hS y hy).symm)
    have hMean := expectation_equal_norm hp hK hKN a b r q ha hab hb
      (hδ.le.trans hδr) hrq hq1 x y hx hn
    have hL := OrthogonalForkSpatialModulus.actual_source_HS_3_1 hN hp hK hKN a b δ r q
      (mesh p δ ε) ha hab hb hδ hδr hrq hq1 hη.le x y hx hn
      (by simpa only [dist_eq_norm] using hxy) J (landscapeCeiling p) hR.le hland
    have hmesh : 12*(p:ℝ)*landscapeCeiling p*mesh p δ ε/Real.sqrt δ=ε/2 := by
      dsimp only [mesh]
      have hs := (Real.sqrt_pos.mpr hδ).ne'
      field_simp
      ring
    rw [hmesh] at hL
    have hid : F x J-F y J=GaussianFixedBaseForkConcentration.supremum a b r q x J-
        GaussianFixedBaseForkConcentration.supremum a b r q y J := by
      dsimp only [F]
      rw [hMean]
      ring
    have hF : |F x J-F y J|≤ε/2 := by rw [hid];exact hL
    refine Or.inl ⟨y,hy,?_⟩
    have habs : |F x J|≤|F x J-F y J|+|F y J| := by
      have hh := abs_add_le (F x J-F y J) (F y J)
      rw [sub_add_cancel] at hh
      exact hh
    linarith
  change (forkLaw N p K).real {J | ∃x : Vector N,‖x‖^2=(N:ℝ)*r ∧ ε≤|F x J|}≤_
  have hNet' : (forkLaw N p K).real BadNet≤
      2*(1+2/mesh p δ ε)^N*Real.exp (-((K:ℝ)*N)*ε^2/(8*(Real.pi/2)^2)) := by
    exact hNet.trans_eq (by congr 2;ring)
  exact (measureReal_mono hsubset).trans ((measureReal_union_le _ _).trans
    (add_le_add hNet' (fork_landscape_bad_bound (by omega) (by omega))))

end SphericalAging.GaussianForkUniformConcentration
