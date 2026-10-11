module

public import SphericalAging.HamiltonianOneReplicaEdgeComparison
public import SphericalAging.GaussianForkBasepointExpectation
public import SphericalAging.OrthogonalForkMaximizer
public import SphericalAging.PurePSharedLinearMoment

public section

/-! A genuine finite-N expected orthogonal-fork edge ceiling. The full ordered
polynomial remainder is compared to a linear Gaussian process; the shared
first variation is bounded by its actual tangent-gradient envelope. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianForkExpectedEdgeUpper
open Set MeasureTheory ProbabilityTheory FiniteModel GaussianComparison
open GaussianOrthogonalForkCovariance GaussianFixedBaseForkConcentration
open HamiltonianOneReplicaEdgeCoefficients HamiltonianOneReplicaEdgeComparison
open OrthogonalForkMaximizer OrthogonalForkNonempty PurePSharedLinearMoment
open scoped BigOperators InnerProductSpace
variable {N p K : ℕ}
local instance : NormedAddCommGroup (Vector N→L[ℝ]ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Vector N→L[ℝ]ℝ) := ContinuousLinearMap.toNormedSpace

 theorem shared_fresh_pair_hasLaw (i : Fin K) :
    HasLaw (fun J : ForkDisorder N p K => (J none,J (some i)))
      ((disorderLaw N p).prod (disorderLaw N p)) (forkLaw N p K) := by
  have hi : iIndepFun (fun j : Option (Fin K) => fun J : ForkDisorder N p K => J j)
      (forkLaw N p K) := iIndepFun_pi (X:=fun _ => id) (fun _ => aemeasurable_id)
  exact (hi.indepFun (by simp : (none : Option (Fin K))≠some i)).hasLaw_prod
    (measurePreserving_eval (fun _ : Option (Fin K) => disorderLaw N p) none).hasLaw
    (measurePreserving_eval (fun _ : Option (Fin K) => disorderLaw N p) (some i)).hasLaw

@[expose]  def forkRemainderSup (a b r q : ℝ) (x : Vector N) (i : Fin K)
    (J : ForkDisorder N p K) : ℝ :=
  singleSup a b x (fun y : LeafDomain N K x r q => y.1 i-x) (J none,J (some i))

 theorem incrementMap_continuous (x : Vector N) (r q : ℝ) (i : Fin K) :
    Continuous (fun y : LeafDomain N K x r q => y.1 i-x) :=
  ((continuous_apply i).comp continuous_subtype_val).sub continuous_const

 theorem forkRemainderSup_integrable (hKN : K<N) {r q : ℝ}
    (hr : 0≤r) (hrq : r≤q) (a b : ℝ) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*r) (i : Fin K) :
    Integrable (forkRemainderSup (p:=p) a b r q x i) (forkLaw N p K) := by
  letI : CompactSpace (LeafDomain N K x r q) :=
    isCompact_iff_compactSpace.mp (forkSet_isCompact x r q (hr.trans hrq))
  letI := leafDomain_nonempty hKN x r q hr hrq hx
  exact (shared_fresh_pair_hasLaw (N:=N) (p:=p) i).integrable_comp
    (singleSup_integrable a b x _ (incrementMap_continuous x r q i))

 theorem forkRemainderSup_expectation_le (hN : 0<N) (hp : 2≤p) (hKN : K<N)
    {a b r q : ℝ} (ha : 0≤a) (hab : a≤b) (hr : 0≤r) (hrq : r≤q)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*r) (i : Fin K) :
    (∫J : ForkDisorder N p K,forkRemainderSup a b r q x i J ∂forkLaw N p K)/(N:ℝ)≤
      Real.sqrt ((q-r)*edgeRate p a b r q) := by
  letI : CompactSpace (LeafDomain N K x r q) :=
    isCompact_iff_compactSpace.mp (forkSet_isCompact x r q (hr.trans hrq))
  letI := leafDomain_nonempty hKN x r q hr hrq hx
  have he := (shared_fresh_pair_hasLaw (N:=N) (p:=p) i).integral_comp
    (singleSup_integrable a b x _ (incrementMap_continuous x r q i)).aestronglyMeasurable
  change (∫J : ForkDisorder N p K,forkRemainderSup a b r q x i J ∂forkLaw N p K)=_ at he
  rw [he]
  have hc := singleSup_expectation_bound hN hp ha hab hr (sub_nonneg.mpr hrq) x hx
    (fun y : LeafDomain N K x r q => y.1 i-x) (incrementMap_continuous x r q i)
    (fun y => y.2.increment_base i) (fun y => orthogonalFork_increment_norm y.2 i)
  simpa only [add_sub_cancel] using hc

 theorem singleRemainder_le_singleSup {I : Type*} [TopologicalSpace I] [CompactSpace I]
    (a b : ℝ) (x : Vector N) (u : I→Vector N) (hu : Continuous u)
    (J : Disorder N p×Disorder N p) (i : I) :
    singleRemainder a b x (u i) J ≤ singleSup a b x u J := by
  have hc : Continuous (fun i : I => singleRemainder a b x (u i) J) := by
    unfold singleRemainder
    exact (continuous_const.mul (((Hamiltonian_contDiff J.1).continuous.comp
      (continuous_const.add hu)).sub continuous_const |>.sub
      ((fderiv ℝ (Hamiltonian N p J.1) x).continuous.comp hu))).add
      (continuous_const.mul ((Hamiltonian_contDiff J.2).continuous.comp (continuous_const.add hu)))
  exact le_csSup (isCompact_range hc).bddAbove (mem_range_self i)

 theorem averagedIncrement_decomposition (a b : ℝ) (x : Vector N) (y : Fin K→Vector N)
    (J : ForkDisorder N p K) :
    averagedIncrement a b x y J=Real.sqrt a*linearAverage x (fun i => y i-x) (J none)+
      (∑i,singleRemainder a b x (y i-x) (J none,J (some i)))/((K:ℝ)*N) := by
  unfold averagedIncrement increment sharedIncrement block linearAverage singleRemainder
  simp only [add_sub_cancel,inner_gradient_left]
  rw [←mul_div_assoc,Finset.mul_sum,←add_div,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

 theorem actual_supremum_upper (hN : 0<N) (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    {a b r q : ℝ} (ha : 0≤a) (hab : a≤b) (hb : b≤1) (hr : 0≤r) (hrq : r≤q) (hq1 : q≤1)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*r) (J : ForkDisorder N p K) :
    supremum a b r q x J≤Real.sqrt a*forkLinearEnvelope x (q-r) J+
      (∑i,forkRemainderSup a b r q x i J)/((K:ℝ)*N) := by
  letI : CompactSpace (LeafDomain N K x r q) :=
    isCompact_iff_compactSpace.mp (forkSet_isCompact x r q (hr.trans hrq))
  obtain ⟨y,hy,hmax⟩ := actual_fork_maximizer hN hp hK hKN a b r q ha hab hb hr hrq hq1 x hx J
  rw [←hmax,averagedIncrement_decomposition]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans
      (fork_linearAverage_abs_le hN hK hrq x y hy J)) (Real.sqrt_nonneg _)
  · apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    exact singleRemainder_le_singleSup a b x _ (incrementMap_continuous x r q i)
      (J none,J (some i)) (⟨y,hy⟩ : LeafDomain N K x r q)

 theorem actual_expected_edge_upper (hN : 0<N) (hp : 2≤p) (hK : 0<K) (hKN : K<N)
    {a b r q : ℝ} (ha : 0≤a) (hab : a≤b) (hb : b≤1) (hr : 0≤r) (hrq : r≤q) (hq1 : q≤1)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*r) :
    (∫J : ForkDisorder N p K,supremum a b r q x J ∂forkLaw N p K)≤
      Real.sqrt ((q-r)*(b*(p:ℝ)*q^(p-1)-a*(p:ℝ)*r^(p-1)))+
      Real.sqrt (a*(p:ℝ)*r^(p-1)*(q-r)/K) := by
  have hI := GaussianForkBasepointExpectation.supremum_integrable (p:=p) (by omega) hK hKN
    a b r q ha hab hb hr hrq hq1 x hx
  have hL := forkLinearEnvelope_integrable (p:=p) (K:=K) x (q-r)
  have hR := fun i : Fin K => forkRemainderSup_integrable (p:=p) hKN hr hrq a b x hx i
  have hupper := integral_mono hI ((hL.const_mul (Real.sqrt a)).add
    ((integrable_finset_sum _ (fun i _ => hR i)).div_const ((K:ℝ)*N)))
    (actual_supremum_upper hN (by omega) hK hKN ha hab hb hr hrq hq1 x hx)
  simp only [Pi.add_apply] at hupper
  rw [integral_add (hL.const_mul _) ((integrable_finset_sum _ (fun i _ => hR i)).div_const _),
    integral_const_mul,integral_div,integral_finset_sum _ (fun i _ => hR i)] at hupper
  have hsum : (∑i : Fin K,(∫J,forkRemainderSup a b r q x i J ∂forkLaw N p K))/((K:ℝ)*N)≤
      Real.sqrt ((q-r)*edgeRate p a b r q) := by
    have hh : (∑i : Fin K,(∫J,forkRemainderSup a b r q x i J ∂forkLaw N p K)/(N:ℝ))≤
        ∑i : Fin K,Real.sqrt ((q-r)*edgeRate p a b r q) :=
      Finset.sum_le_sum (fun i _ => forkRemainderSup_expectation_le hN hp hKN ha hab hr hrq x hx i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.sum_div] at hh
    have he : (∑i : Fin K,(∫J,forkRemainderSup a b r q x i J ∂forkLaw N p K))/((K:ℝ)*N)=
        ((∑i : Fin K,(∫J,forkRemainderSup a b r q x i J ∂forkLaw N p K))/(N:ℝ))/(K:ℝ) := by ring
    rw [he]
    exact (div_le_div_of_nonneg_right hh (Nat.cast_nonneg K)).trans_eq
      (mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hK.ne'))
  have hs := mul_le_mul_of_nonneg_left
    (forkLinearEnvelope_expectation_le hN hp hK hr (sub_nonneg.mpr hrq) x hx) (Real.sqrt_nonneg a)
  have he : Real.sqrt a*Real.sqrt ((p:ℝ)*r^(p-1)*(q-r)/K)=
      Real.sqrt (a*(p:ℝ)*r^(p-1)*(q-r)/K) := by
    rw [←Real.sqrt_mul ha]
    congr 1
    ring
  exact hupper.trans (by rw [←he];unfold edgeRate at hsum;linarith)

end SphericalAging.HamiltonianForkExpectedEdgeUpper
