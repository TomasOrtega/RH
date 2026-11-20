import Mathlib

open scoped ContDiff Topology

namespace GlobalTheory

open Filter

/- English proof (translation)
Establish `hterm : ∀ a, TendstoLocallyUniformly (fun j y => f a j y • L a) (fun y => ψ a y • L a) atTop`. Introduce `a`. Establish `hu : UniformContinuous (fun z : ℂ => z • L a)` using `((ContinuousLinearMap.id ℂ ℂ).smulRight (L a)).uniformContinuous`. Conclude with `hu.comp_tendstoLocallyUniformly (h a)`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `fun u hu x => ⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`.

Conclude with `(hterm a).add ih`.
-/
theorem tendstoLocallyUniformly_sum_smul_const {E : Type} [TopologicalSpace E] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℂ F] {A : Type} (s : Finset A) (L : A → F)
    (f : A → ℕ → E → ℂ) (ψ : A → E → ℂ)
    (h : ∀ a, TendstoLocallyUniformly (f a) (ψ a) atTop) :
    TendstoLocallyUniformly (fun j y => ∑ a ∈ s, f a j y • L a)
      (fun y => ∑ a ∈ s, ψ a y • L a) atTop := by
  classical
  have hterm : ∀ a, TendstoLocallyUniformly (fun j y => f a j y • L a)
      (fun y => ψ a y • L a) atTop := by
    intro a
    have hu : UniformContinuous (fun z : ℂ => z • L a) :=
      ((ContinuousLinearMap.id ℂ ℂ).smulRight (L a)).uniformContinuous
    exact hu.comp_tendstoLocallyUniformly (h a)
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact fun u hu x => ⟨Set.univ, Filter.univ_mem,
      Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hterm a).add ih

/- English proof (translation)
Introduce `E _ _ A _ v c hvc φ g ψ hg hφ hψ y`. Establish `hdecomp : (fun j z => fderiv ℝ (g j) z) = fun j z => ∑ a, fderiv ℝ (g j) z (v a) • (c a).smulRight (1 : ℂ)`. Use function extensionality and compare the values at `j z`. Use `ContinuousLinearMap.ext fun x => ?_` and prove the remaining obligations. Use `conv_lhs => rw [← hvc x]`.

Simplify using `only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.smulRight_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `[Complex.real_smul, mul_comm]`. Establish `hconv : TendstoLocallyUniformly (fun j z => fderiv ℝ (g j) z) (fun z => ∑ a, ψ a z • (c a).smulRight (1 : ℂ)) Filter.atTop`. Rewrite using `[hdecomp]`.

Conclude with `tendstoLocallyUniformly_sum_smul_const Finset.univ (fun a => (c a).smulRight (1 : ℂ)) (fun a j z => fderiv ℝ (g j) z (v a)) ψ hψ`. Establish `hfd : HasFDerivAt φ (∑ a, ψ a y • (c a).smulRight (1 : ℂ)) y` using `hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ (hconv.tendstoLocallyUniformlyOn (s := Set.univ)) (fun n z _ => (hg n z).hasFDerivAt) (fun z _ => (hφ.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ z)) (Set.mem_univ y)`. Use `⟨hfd.differentiableAt, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hfd.fderiv]`. Establish `h1 : Filter.Tendsto (fun j => fderiv ℝ (g j) y (v a)) Filter.atTop (𝓝 ((∑ b, ψ b y • (c b).smulRight (1 : ℂ)) (v a)))` using `((ContinuousLinearMap.apply ℝ ℂ (v a)).continuous.tendsto _).comp ((hconv.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ y))`.

Establish `h2 : Filter.Tendsto (fun j => fderiv ℝ (g j) y (v a)) Filter.atTop (𝓝 (ψ a y))` using `((hψ a).tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ y)`. Conclude with `tendsto_nhds_unique h1 h2`.
-/
theorem differentiableAt_of_tendstoLocallyUniformly_directional :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ (φ : E → ℂ) (g : ℕ → E → ℂ) (ψ : A → E → ℂ), (∀ j, Differentiable ℝ (g j)) → TendstoLocallyUniformly g φ Filter.atTop → (∀ a, TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (ψ a) Filter.atTop) → ∀ y, DifferentiableAt ℝ φ y ∧ ∀ a, fderiv ℝ φ y (v a) = ψ a y := by
  intro E _ _ A _ v c hvc φ g ψ hg hφ hψ y
  classical
  have hdecomp : (fun j z => fderiv ℝ (g j) z) =
      fun j z => ∑ a, fderiv ℝ (g j) z (v a) • (c a).smulRight (1 : ℂ) := by
    funext j z
    refine ContinuousLinearMap.ext fun x => ?_
    conv_lhs => rw [← hvc x]
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Complex.real_smul, mul_comm]
  have hconv : TendstoLocallyUniformly (fun j z => fderiv ℝ (g j) z)
      (fun z => ∑ a, ψ a z • (c a).smulRight (1 : ℂ)) Filter.atTop := by
    rw [hdecomp]
    exact tendstoLocallyUniformly_sum_smul_const Finset.univ (fun a => (c a).smulRight (1 : ℂ))
      (fun a j z => fderiv ℝ (g j) z (v a)) ψ hψ
  have hfd : HasFDerivAt φ (∑ a, ψ a y • (c a).smulRight (1 : ℂ)) y :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      (hconv.tendstoLocallyUniformlyOn (s := Set.univ))
      (fun n z _ => (hg n z).hasFDerivAt)
      (fun z _ => (hφ.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ z))
      (Set.mem_univ y)
  refine ⟨hfd.differentiableAt, fun a => ?_⟩
  rw [hfd.fderiv]
  have h1 : Filter.Tendsto (fun j => fderiv ℝ (g j) y (v a)) Filter.atTop
      (𝓝 ((∑ b, ψ b y • (c b).smulRight (1 : ℂ)) (v a))) :=
    ((ContinuousLinearMap.apply ℝ ℂ (v a)).continuous.tendsto _).comp
      ((hconv.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ y))
  have h2 : Filter.Tendsto (fun j => fderiv ℝ (g j) y (v a)) Filter.atTop (𝓝 (ψ a y)) :=
    ((hψ a).tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ y)
  exact tendsto_nhds_unique h1 h2

end GlobalTheory
