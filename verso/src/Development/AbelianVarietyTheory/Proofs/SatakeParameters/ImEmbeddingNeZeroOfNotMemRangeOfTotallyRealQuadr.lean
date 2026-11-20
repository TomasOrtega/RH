import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Introduce `h`. Use `set φ := w.embedding with hφ`. Establish `hF : ∀ c : F, (φ (algebraMap F E c)).im = 0`. Introduce `c`. Establish `hr : ComplexEmbedding.IsReal (φ.comp (algebraMap F E))` using `InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)`.

Use `ComplexEmbedding.isReal_iff.1 hr` as an intermediate fact. Establish `h2` using `RingHom.congr_fun this c`. Conclude with `Complex.conj_eq_iff_im.1 h2`. Establish `hli : LinearIndependent F ![(1 : E), θ]`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `s t hst`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Simplify using `at hst`. Conclude with `⟨hst, rfl⟩`.

It suffices to derive a contradiction. Apply `hθ` to reduce the goal to its premises. Use `⟨-(s / t), ?_⟩` and prove the remaining obligations. Establish `: t • θ = -(s • (1 : E))` using `eq_neg_of_add_eq_zero_right hst`. Rewrite `this` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`.

Establish `ht' : algebraMap F E t ≠ 0` using `by simpa using ht`. Rewrite using `[map_neg, map_div₀]`. Clear the denominators using the available nonvanishing facts. Rewrite `this` using `[mul_comm]`. Take the linear combination `-this`.

Establish `hspan : Submodule.span F (Set.range ![(1 : E), θ]) = ⊤`. Apply `hli.span_eq_top_of_card_eq_finrank` to reduce the goal to its premises. Simplify using `[Algebra.IsQuadraticExtension.finrank_eq_two F E]`. Establish `hall : ∀ z : E, (φ z).im = 0`. Introduce `z`.

Establish `hz : z ∈ Submodule.span F (Set.range ![(1 : E), θ])` using `hspan ▸ Submodule.mem_top`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun F).1 hz`. Rewrite using `[← hc, Fin.sum_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Algebra.smul_def, mul_one, map_add, map_mul, Complex.add_im, Complex.mul_im, hF, h, zero_mul, mul_zero, add_zero]`. Establish `hreal : ComplexEmbedding.IsReal φ`.

Rewrite using `[ComplexEmbedding.isReal_iff]`. Use `ext1 z`. Conclude with `Complex.conj_eq_iff_im.2 (hall z)`. Conclude with `InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w) (InfinitePlace.isReal_iff.2 hreal)`.
-/
theorem im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E]
    (w : InfinitePlace E) (θ : E) (hθ : θ ∉ Set.range (algebraMap F E)) :
    (w.embedding θ).im ≠ 0 := by
  intro h
  set φ := w.embedding with hφ
  have hF : ∀ c : F, (φ (algebraMap F E c)).im = 0 := by
    intro c
    have hr : ComplexEmbedding.IsReal (φ.comp (algebraMap F E)) :=
      InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
    have := ComplexEmbedding.isReal_iff.1 hr
    have h2 := RingHom.congr_fun this c
    exact Complex.conj_eq_iff_im.1 h2
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hθ
      refine ⟨-(s / t), ?_⟩
      have : t • θ = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at this
      have ht' : algebraMap F E t ≠ 0 := by simpa using ht
      rw [map_neg, map_div₀]
      field_simp
      rw [mul_comm] at this
      linear_combination -this
  have hspan : Submodule.span F (Set.range ![(1 : E), θ]) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank
    simp [Algebra.IsQuadraticExtension.finrank_eq_two F E]
  have hall : ∀ z : E, (φ z).im = 0 := by
    intro z
    have hz : z ∈ Submodule.span F (Set.range ![(1 : E), θ]) := hspan ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hz
    rw [← hc, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Algebra.smul_def,
      mul_one, map_add, map_mul, Complex.add_im, Complex.mul_im, hF, h, zero_mul, mul_zero,
      add_zero]
  have hreal : ComplexEmbedding.IsReal φ := by
    rw [ComplexEmbedding.isReal_iff]
    ext1 z
    exact Complex.conj_eq_iff_im.2 (hall z)
  exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
    (InfinitePlace.isReal_iff.2 hreal)

/- English proof (translation)
The claim follows from `im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic`.
-/
example : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w : InfinitePlace E) (θ : E), θ ∉ Set.range (algebraMap F E) → (w.embedding θ).im ≠ 0 :=
  im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic

end GlobalTheory
