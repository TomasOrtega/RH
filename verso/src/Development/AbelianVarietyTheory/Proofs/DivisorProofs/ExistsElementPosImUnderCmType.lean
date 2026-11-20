import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRangeEmbeddingPi
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMTypeImPos

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi`. Consider the case `exact _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi`. Consider the case `(apply _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi ..)`.
-/
theorem denseRange_embeddings : DenseRange fun (x : E) (w : InfinitePlace E) => w.embedding x := by
  first
  | exact @_root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi
  | exact _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi
  | (apply _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi ..)

/- English proof (translation)
Set `f : I → (InfinitePlace E → ℂ) → ℝ` to `fun i z => if (InfinitePlace.mk (φ i)).embedding = φ i then (z (InfinitePlace.mk (φ i))).im else -(z (InfinitePlace.mk (φ i))).im`. Establish `hfc : ∀ i, Continuous (f i)`. Introduce `i`. Distinguish the cases in `h : (InfinitePlace.mk (φ i)).embedding = φ i`. Simplify using `only [f, h, if_true]`.

Conclude with `Complex.continuous_im.comp (continuous_apply _)`. Simplify using `only [f, h, if_false]`. Conclude with `(Complex.continuous_im.comp (continuous_apply _)).neg`. Set `U : Set (InfinitePlace E → ℂ)` to `{z | ∀ i, 0 < f i z}`. Establish `hU : IsOpen U`.

Establish `: U = ⋂ i, {z | 0 < f i z}` using `by ext z; simp [U]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hfc i)`. Set `y : InfinitePlace E → ℂ` to `fun w => if ∃ j, w.embedding = φ j then Complex.I else -Complex.I`. Establish `hy : y ∈ U`.

Introduce `i`. Establish `hnr : ¬ ComplexEmbedding.IsReal (φ i)` using `InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex _)`. Break down `InfinitePlace.embedding_mk_eq (φ i) with h | h` into its components or cases. Establish `hex : ∃ j, (InfinitePlace.mk (φ i)).embedding = φ j` using `⟨i, h⟩`. Simplify using `[f, y, h, hex]`.

Establish `hne : (InfinitePlace.mk (φ i)).embedding ≠ φ i`. Rewrite using `[h]`. Conclude with `fun h' => hnr (ComplexEmbedding.isReal_iff.2 h')`. Establish `hex : ¬ ∃ j, (InfinitePlace.mk (φ i)).embedding = φ j`. Introduce and unpack `⟨j, hj⟩`.

Take `⟨k, _, hk⟩` from `hφ (InfinitePlace.mk (φ i)).embedding`. Establish `hi : i = k` using `hk i (Or.inr h)`. Establish `hj' : j = k` using `hk j (Or.inl hj)`. Substitute `hi` using the available equality. Substitute `hj'` using the available equality.

Conclude with `hne hj`. Simplify using `[f, y, hne, hex]`. Take `⟨θ, hθ⟩` from `denseRange_embeddings.exists_mem_open hU ⟨y, hy⟩`. Use `⟨θ, fun i => ?_⟩` and prove the remaining obligations. Use `hθ i` as an intermediate fact.

Break down `InfinitePlace.embedding_mk_eq (φ i) with h | h` into its components or cases. Simplify `this` using `[f, h]`. Distinguish the cases in `h' : (InfinitePlace.mk (φ i)).embedding = φ i`. Simplify `this` using `[f, h']`. Simplify using `only [f, h', if_false] at this`.

Rewrite `this` using `[h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_im_pos (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) : ∃ θ : E, ∀ i, 0 < (φ i θ).im := by
  classical

  let f : I → (InfinitePlace E → ℂ) → ℝ := fun i z =>
    if (InfinitePlace.mk (φ i)).embedding = φ i then (z (InfinitePlace.mk (φ i))).im
    else -(z (InfinitePlace.mk (φ i))).im
  have hfc : ∀ i, Continuous (f i) := by
    intro i
    by_cases h : (InfinitePlace.mk (φ i)).embedding = φ i
    · simp only [f, h, if_true]
      exact Complex.continuous_im.comp (continuous_apply _)
    · simp only [f, h, if_false]
      exact (Complex.continuous_im.comp (continuous_apply _)).neg
  let U : Set (InfinitePlace E → ℂ) := {z | ∀ i, 0 < f i z}
  have hU : IsOpen U := by
    have : U = ⋂ i, {z | 0 < f i z} := by ext z; simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hfc i)

  let y : InfinitePlace E → ℂ := fun w => if ∃ j, w.embedding = φ j then Complex.I else -Complex.I
  have hy : y ∈ U := by
    intro i
    have hnr : ¬ ComplexEmbedding.IsReal (φ i) :=
      InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex _)
    rcases InfinitePlace.embedding_mk_eq (φ i) with h | h
    · have hex : ∃ j, (InfinitePlace.mk (φ i)).embedding = φ j := ⟨i, h⟩
      simp [f, y, h, hex]
    · have hne : (InfinitePlace.mk (φ i)).embedding ≠ φ i := by
        rw [h]; exact fun h' => hnr (ComplexEmbedding.isReal_iff.2 h')
      have hex : ¬ ∃ j, (InfinitePlace.mk (φ i)).embedding = φ j := by
        rintro ⟨j, hj⟩
        obtain ⟨k, _, hk⟩ := hφ (InfinitePlace.mk (φ i)).embedding
        have hi : i = k := hk i (Or.inr h)
        have hj' : j = k := hk j (Or.inl hj)
        subst hi; subst hj'
        exact hne hj
      simp [f, y, hne, hex]
  obtain ⟨θ, hθ⟩ := denseRange_embeddings.exists_mem_open hU ⟨y, hy⟩
  refine ⟨θ, fun i => ?_⟩
  have := hθ i
  rcases InfinitePlace.embedding_mk_eq (φ i) with h | h
  · simpa [f, h] using this
  · by_cases h' : (InfinitePlace.mk (φ i)).embedding = φ i
    · simpa [f, h'] using this
    · simp only [f, h', if_false] at this
      rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_im] at this
      linarith

end GlobalTheory.CMTypeImPos

/- English proof (translation)
The claim follows from `GlobalTheory.CMTypeImPos.exists_im_pos`.
-/
example : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∃ θ : E, ∀ i, 0 < (φ i θ).im := GlobalTheory.CMTypeImPos.exists_im_pos
