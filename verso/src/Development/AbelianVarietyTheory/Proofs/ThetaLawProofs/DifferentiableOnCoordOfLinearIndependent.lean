import Mathlib

namespace GlobalTheory

open Filter Topology

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Use `DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _` and prove the remaining obligations. Conclude with `(HasFDerivAt.finset_prod (fun i _ => (h (σ i) i).hasFDerivAt)).differentiableAt`.
-/
theorem differentiableAt_det_of_entries {E I : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype I] [DecidableEq I] (A : E → Matrix I I ℂ) (x : E)
    (h : ∀ i j, DifferentiableAt ℂ (fun e => A e i j) x) :
    DifferentiableAt ℂ (fun e => (A e).det) x := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  exact (HasFDerivAt.finset_prod (fun i _ => (h (σ i) i).hasFDerivAt)).differentiableAt

/- English proof (translation)
Introduce `E Z I _ _ _ W Th F c hW hTh hF hli hc k e₀ he₀`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Establish `hnh : W ∈ 𝓝 e₀` using `hW.mem_nhds he₀`. Establish `hspan : Submodule.span ℂ (Set.range (flip (fun k => Th k e₀))) = ⊤` using `span_flip_eq_top_iff_linearIndependent.2 (hli e₀ he₀)`. Establish `hl : ∀ i : I, ∃ l : Z →₀ ℂ, ∀ j, (∑ z ∈ l.support, l z * Th j e₀ z) = (1 : Matrix I I ℂ) i j`.

Introduce `i`. Establish `hm : (fun j => (1 : Matrix I I ℂ) i j) ∈ Submodule.span ℂ (Set.range (flip (fun k => Th k e₀)))`. Rewrite using `[hspan]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨l, hl⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 hm`.

Use `⟨l, fun j => ?_⟩` and prove the remaining obligations. Use `congrFun hl j` as an intermediate fact. Simplify `this` using `[Finsupp.sum, flip, Finset.sum_apply]`. Use `choose l hl using hl`. Set `A : E → Matrix I I ℂ` to `fun e => Matrix.of fun i j => ∑ z ∈ (l i).support, l i z * Th j e z`.

Set `b : E → I → ℂ` to `fun e i => ∑ z ∈ (l i).support, l i z * F e z`. Establish `hA0 : A e₀ = 1`. Use extensionality with `i j`. Conclude with `hl i j`. Establish `hAd : ∀ i j, DifferentiableAt ℂ (fun e => A e i j) e₀`.

Introduce `i j`. Simplify using `only [A, Matrix.of_apply]`. Conclude with `DifferentiableAt.fun_sum fun z _ => ((hTh j z).differentiableAt hnh).const_mul _`. Establish `hbd : ∀ i, DifferentiableAt ℂ (fun e => b e i) e₀`. Introduce `i`.

Conclude with `DifferentiableAt.fun_sum fun z _ => ((hF z).differentiableAt hnh).const_mul _`. Establish `hdet` using `differentiableAt_det_of_entries A e₀ hAd`. Establish `hne : (A e₀).det ≠ 0` using `by rw [hA0]; simp`. Establish `hnum : DifferentiableAt ℂ (fun e => ((A e).updateCol k (b e)).det) e₀`. Use `differentiableAt_det_of_entries _ e₀ fun i j => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.updateCol_apply]`. Distinguish the cases in `h : j = k`. Simplify `hbd i` using `[h]`. Simplify `hAd i j` using `[h]`. Establish `hb : ∀ e ∈ W, b e = (A e).mulVec (c e)`.

Introduce `e he`. Use function extensionality and compare the values at `i`. Simplify using `only [b, A, Matrix.mulVec, dotProduct, Matrix.of_apply, hc e he, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun z _ => by ring`.

Use `(hnum.mul (hdet.inv hne)).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hnh, hdet.continuousAt.eventually_ne hne] with e he hne'`. Establish `h1 : ((A e).updateCol k (b e)).det = (A e).det * c e k`. Rewrite using `[← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, hb e he, Matrix.mulVec_mulVec, Matrix.adjugate_mul]`. Simplify using `[Matrix.smul_mulVec]`.

Simplify using `only [Pi.mul_apply, Pi.inv_apply, h1]`. Clear the denominators using the available nonvanishing facts.
-/
theorem differentiableOn_coord_of_linearIndependent :
    ∀ (E Z I : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype I] (W : Set E) (Th : I → E → Z → ℂ) (F : E → Z → ℂ) (c : E → I → ℂ), IsOpen W → (∀ k z, DifferentiableOn ℂ (fun e => Th k e z) W) → (∀ z, DifferentiableOn ℂ (fun e => F e z) W) → (∀ e ∈ W, LinearIndependent ℂ (fun k => Th k e)) → (∀ e ∈ W, ∀ z, F e z = ∑ k, c e k * Th k e z) → ∀ k, DifferentiableOn ℂ (fun e => c e k) W := by
  intro E Z I _ _ _ W Th F c hW hTh hF hli hc k e₀ he₀
  classical
  apply DifferentiableAt.differentiableWithinAt
  have hnh : W ∈ 𝓝 e₀ := hW.mem_nhds he₀
  have hspan : Submodule.span ℂ (Set.range (flip (fun k => Th k e₀))) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.2 (hli e₀ he₀)
  have hl : ∀ i : I, ∃ l : Z →₀ ℂ, ∀ j, (∑ z ∈ l.support, l z * Th j e₀ z) = (1 : Matrix I I ℂ) i j := by
    intro i
    have hm : (fun j => (1 : Matrix I I ℂ) i j) ∈
        Submodule.span ℂ (Set.range (flip (fun k => Th k e₀))) := by
      rw [hspan]; trivial
    obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hm
    refine ⟨l, fun j => ?_⟩
    have := congrFun hl j
    simpa [Finsupp.sum, flip, Finset.sum_apply] using this
  choose l hl using hl
  let A : E → Matrix I I ℂ := fun e => Matrix.of fun i j => ∑ z ∈ (l i).support, l i z * Th j e z
  let b : E → I → ℂ := fun e i => ∑ z ∈ (l i).support, l i z * F e z
  have hA0 : A e₀ = 1 := by
    ext i j; exact hl i j
  have hAd : ∀ i j, DifferentiableAt ℂ (fun e => A e i j) e₀ := by
    intro i j
    simp only [A, Matrix.of_apply]
    exact DifferentiableAt.fun_sum fun z _ => ((hTh j z).differentiableAt hnh).const_mul _
  have hbd : ∀ i, DifferentiableAt ℂ (fun e => b e i) e₀ := by
    intro i
    exact DifferentiableAt.fun_sum fun z _ => ((hF z).differentiableAt hnh).const_mul _
  have hdet := differentiableAt_det_of_entries A e₀ hAd
  have hne : (A e₀).det ≠ 0 := by rw [hA0]; simp
  have hnum : DifferentiableAt ℂ (fun e => ((A e).updateCol k (b e)).det) e₀ := by
    refine differentiableAt_det_of_entries _ e₀ fun i j => ?_
    simp only [Matrix.updateCol_apply]
    by_cases h : j = k
    · simpa [h] using hbd i
    · simpa [h] using hAd i j
  have hb : ∀ e ∈ W, b e = (A e).mulVec (c e) := by
    intro e he
    funext i
    simp only [b, A, Matrix.mulVec, dotProduct, Matrix.of_apply, hc e he, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun z _ => by ring
  refine (hnum.mul (hdet.inv hne)).congr_of_eventuallyEq ?_
  filter_upwards [hnh, hdet.continuousAt.eventually_ne hne] with e he hne'
  have h1 : ((A e).updateCol k (b e)).det = (A e).det * c e k := by
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, hb e he, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul]
    simp [Matrix.smul_mulVec]
  simp only [Pi.mul_apply, Pi.inv_apply, h1]
  field_simp

end GlobalTheory
