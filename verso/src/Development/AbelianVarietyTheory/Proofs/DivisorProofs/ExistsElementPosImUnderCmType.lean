import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRangeEmbeddingPi
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMTypeImPos

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
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
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Substitute using the available equality. Substitute using the available equality. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Simplify to obtain the desired conclusion from the available facts. Consider separately whether the proposition holds or fails. Simplify to obtain the desired conclusion from the available facts.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
example : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∃ θ : E, ∀ i, 0 < (φ i θ).im := GlobalTheory.CMTypeImPos.exists_im_pos
