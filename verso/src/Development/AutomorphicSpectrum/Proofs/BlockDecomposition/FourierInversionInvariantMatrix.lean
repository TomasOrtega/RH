import Mathlib
open MeasureTheory

namespace GlobalTheory.CompanionTheory.BigCell

/- English proof (translation)
Introduce `A _ _ ν _ ψ ι _ _ Bm hsym hemb hmap t f hf hint hinv`. Establish `hψ : ∀ (s : Finset ι) (h : ι → A), ψ (∑ i ∈ s, h i) = ∏ i ∈ s, ψ (h i)`. Introduce `s h`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]`. Establish `hsplit : ∀ (g : A → ℂ) (x w : ι → A), (∏ i, g (x i)) * ψ (dotProduct x w) = ∏ i, (g (x i) * ψ (x i * w i))`. Introduce `g x w`. Rewrite using `[Finset.prod_mul_distrib]`.

Use `congr 1`. Conclude with `hψ Finset.univ _`. Establish `key : ∀ w : ι → A, ∫ x : ι → A, (∏ i, t (x i)) * ψ (dotProduct x w) ∂(Measure.pi fun _ : ι => ν) = ∏ i, f (w i)`. Introduce `w`. Repeatedly rewrite using `[hsplit t]`.

Rewrite using `[integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun i x => t x * ψ (x * w i))]`. Conclude with `Finset.prod_congr rfl fun i _ => (hf (w i)).symm`. Use `⟨fun y => key _, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Integrable (fun w : ι → A => ∏ i, f (w i)) (Measure.pi fun _ : ι => ν)` using `Integrable.fintype_prod (fun _ => hint)`. Rewrite `h1` using `[← hmap]`.

Conclude with `(hemb.integrable_map_iff).1 h1`. Introduce `z`. Establish `hdot : ∀ y : ι → A, dotProduct y (Bm.mulVec z) = dotProduct (Bm.mulVec y) z`. Introduce `y`. Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose Bm y, ← hsym.eq]`.

Simplify using `[hsym.eq]`. Establish `hG : ∫ y : ι → A, (∏ i, f (Bm.mulVec y i)) * ψ (dotProduct y (Bm.mulVec z)) ∂(Measure.pi fun _ : ι => ν) = ∫ w : ι → A, (∏ i, f (w i)) * ψ (dotProduct w z) ∂((Measure.pi fun _ : ι => ν).map (fun x => Bm.mulVec x))`. Rewrite using `[hemb.integral_map]`. Repeatedly rewrite using `[hdot]`. Rewrite using `[hG, hmap]`.

Repeatedly rewrite using `[hsplit f]`. Rewrite using `[integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun i x => f x * ψ (x * z i))]`. Conclude with `Finset.prod_congr rfl fun i _ => hinv (z i)`.
-/
theorem fourier_prod_symm_preserving :
    ∀ (A : Type) [CommRing A] [MeasurableSpace A] (ν : Measure A) [SigmaFinite ν] (ψ : AddChar A ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] (Bm : Matrix ι ι A), Bm.IsSymm → MeasurableEmbedding (fun x : ι → A => Bm.mulVec x) → (Measure.pi fun _ : ι => ν).map (fun x => Bm.mulVec x) = (Measure.pi fun _ : ι => ν) → ∀ (t f : A → ℂ), (∀ y, f y = ∫ x, t x * ψ (x * y) ∂ν) → Integrable f ν → (∀ z, ∫ b, f b * ψ (b * z) ∂ν = t (-z)) → (∀ y, ∫ x : ι → A, (∏ i, t (x i)) * ψ (dotProduct x (Bm.mulVec y)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, f (Bm.mulVec y i)) ∧ Integrable (fun y : ι → A => ∏ i, f (Bm.mulVec y i)) (Measure.pi fun _ : ι => ν) ∧ ∀ z : ι → A, ∫ y : ι → A, (∏ i, f (Bm.mulVec y i)) * ψ (dotProduct y (Bm.mulVec z)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, t (-(z i)) := by
  intro A _ _ ν _ ψ ι _ _ Bm hsym hemb hmap t f hf hint hinv
  have hψ : ∀ (s : Finset ι) (h : ι → A), ψ (∑ i ∈ s, h i) = ∏ i ∈ s, ψ (h i) := by
    intro s h
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  have hsplit : ∀ (g : A → ℂ) (x w : ι → A),
      (∏ i, g (x i)) * ψ (dotProduct x w) = ∏ i, (g (x i) * ψ (x i * w i)) := by
    intro g x w
    rw [Finset.prod_mul_distrib]
    congr 1
    exact hψ Finset.univ _
  have key : ∀ w : ι → A, ∫ x : ι → A, (∏ i, t (x i)) * ψ (dotProduct x w)
      ∂(Measure.pi fun _ : ι => ν) = ∏ i, f (w i) := by
    intro w
    simp_rw [hsplit t]
    rw [integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun i x => t x * ψ (x * w i))]
    exact Finset.prod_congr rfl fun i _ => (hf (w i)).symm
  refine ⟨fun y => key _, ?_, ?_⟩
  · have h1 : Integrable (fun w : ι → A => ∏ i, f (w i)) (Measure.pi fun _ : ι => ν) :=
      Integrable.fintype_prod (fun _ => hint)
    rw [← hmap] at h1
    exact (hemb.integrable_map_iff).1 h1
  · intro z
    have hdot : ∀ y : ι → A, dotProduct y (Bm.mulVec z) = dotProduct (Bm.mulVec y) z := by
      intro y
      rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose Bm y, ← hsym.eq]
      simp [hsym.eq]
    have hG : ∫ y : ι → A, (∏ i, f (Bm.mulVec y i)) * ψ (dotProduct y (Bm.mulVec z))
          ∂(Measure.pi fun _ : ι => ν)
        = ∫ w : ι → A, (∏ i, f (w i)) * ψ (dotProduct w z)
          ∂((Measure.pi fun _ : ι => ν).map (fun x => Bm.mulVec x)) := by
      rw [hemb.integral_map]
      simp_rw [hdot]
    rw [hG, hmap]
    simp_rw [hsplit f]
    rw [integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun i x => f x * ψ (x * z i))]
    exact Finset.prod_congr rfl fun i _ => hinv (z i)

end GlobalTheory.CompanionTheory.BigCell
