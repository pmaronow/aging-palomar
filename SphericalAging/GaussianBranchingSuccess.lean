module

public import SphericalAging.IndependentBranchingSuccessEvent
public import SphericalAging.GaussianLinearMixtureLaw

public section

/-! Genuine Gaussian instantiation of the full independently branching
success lower bound. Every leaf marginal is derived from the actual Gaussian
mixture law, including an initial deterministic zero root. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianBranchingSuccess
open Set MeasureTheory ProbabilityTheory IndependentBranchingSuccess
  IndependentBranchingSuccessEvent ConditionalCloneSuccessJensen GaussianLinearMixtureLaw
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def update (a b : ℕ→ℝ) (d : ℕ) (s g : E) : E := a d•s+b d•g

theorem update_measurable (a b : ℕ→ℝ) (d : ℕ) :
    Measurable (Function.uncurry (update (E:=E) a b d)) :=
  (mixture (E:=E) (a d) (b d)).measurable

theorem singleMean_stationary (a b : ℕ→ℝ) (h : ∀j,(a j)^2+(b j)^2=1)
    (f : E→ℝ) (hf : Measurable f) (hb : ∀s,0≤f s ∧ f s≤1) (d : ℕ) :
    (∫s,singleMean (stdGaussian E) (update a b) f d s ∂stdGaussian E)=
      ∫s,f s ∂stdGaussian E := by
  induction d with
  | zero => rfl
  | succ d ih =>
    let m : E→ℝ := singleMean (stdGaussian E) (update a b) f d
    have hm : Measurable m := singleMean_measurable (stdGaussian E) (update a b)
      (update_measurable a b) f hf d
    have hmb s : 0≤m s ∧ m s≤1 := singleMean_bounds (stdGaussian E) (update a b)
      (update_measurable a b) f hf hb d s
    have hjm : Measurable (fun z : E×E => m (update a b d z.1 z.2)) :=
      hm.comp (update_measurable a b d)
    have hji := bounded_integrable ((stdGaussian E).prod (stdGaussian E)) _ hjm
      (fun z => hmb _)
    change (∫s,∫g,m (update a b d s g) ∂stdGaussian E ∂stdGaussian E)=_
    rw [←integral_prod _ hji]
    have hmp := mixture_measurePreserving (E:=E) (a d) (b d) (h d)
    have ht : (∫z,m (update a b d z.1 z.2) ∂(stdGaussian E).prod (stdGaussian E))=
        ∫s,m s ∂stdGaussian E := by
      change (∫z,m (a d•z.1+b d•z.2) ∂(stdGaussian E).prod (stdGaussian E))=_
      rw [←integral_map_of_stronglyMeasurable hmp.measurable hm.stronglyMeasurable,hmp.map_eq]
    exact ht.trans ih

/-- A true shared standard Gaussian seed and fresh independent noises produce
joint terminal success at least the marginal success to the number of leaves. -/
theorem actual_gaussian_tree_success_lower (K : ℕ) (a b : ℕ→ℝ)
    (h : ∀j,(a j)^2+(b j)^2=1) (B : Set E) (hB : MeasurableSet B) (d : ℕ) :
    ((stdGaussian E).real B)^(K^d)≤
      ((stdGaussian E).prod (treeLaw (stdGaussian E) K d)).real
        (event K (update a b) B d) := by
  have hf : Measurable (B.indicator (fun _ => (1:ℝ))) := measurable_const.indicator hB
  have hb s : 0≤B.indicator (fun _ => (1:ℝ)) s ∧
      B.indicator (fun _ => (1:ℝ)) s≤1 := by by_cases hs : s∈B <;> simp [hs]
  have hh := actual_tree_success_probability_lower (stdGaussian E) (stdGaussian E) K
    (update a b) (update_measurable a b) B hB d
  rw [singleMean_stationary a b h _ hf hb d,integral_indicator_const (1:ℝ) hB] at hh
  simpa only [smul_eq_mul,mul_one] using hh

/-- The first actual Gaussian disclosure may start from the deterministic
zero root, exactly as in the branching Hamiltonian construction. -/
theorem actual_zero_root_gaussian_tree_success_lower (K : ℕ) (a b : ℕ→ℝ)
    (h : ∀j,(a j)^2+(b j)^2=1) (d : ℕ) (ha : a d=0) (hb : b d=1)
    (B : Set E) (hB : MeasurableSet B) :
    ((stdGaussian E).real B)^(K^(d+1))≤
      ((Measure.dirac (0:E)).prod (treeLaw (stdGaussian E) K (d+1))).real
        (event K (update a b) B (d+1)) := by
  have hf : Measurable (B.indicator (fun _ => (1:ℝ))) := measurable_const.indicator hB
  have hfb s : 0≤B.indicator (fun _ => (1:ℝ)) s ∧
      B.indicator (fun _ => (1:ℝ)) s≤1 := by by_cases hs : s∈B <;> simp [hs]
  have hh := actual_tree_success_probability_lower (Measure.dirac (0:E)) (stdGaussian E) K
    (update a b) (update_measurable a b) B hB (d+1)
  rw [integral_dirac] at hh
  simp only [singleMean,update,ha,hb,zero_smul,one_smul,zero_add] at hh
  rw [singleMean_stationary a b h _ hf hfb d,integral_indicator_const (1:ℝ) hB] at hh
  simpa only [smul_eq_mul,mul_one] using hh

end SphericalAging.GaussianBranchingSuccess
