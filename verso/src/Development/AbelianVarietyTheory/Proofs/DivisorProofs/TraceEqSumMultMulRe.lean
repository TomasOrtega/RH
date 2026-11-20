import Mathlib

namespace GlobalTheory.TraceRealEmbeddingSum

open NumberField

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem re_embedding_mk {F : Type} [Field F] (φ : F →+* ℂ) (x : F) :
    ((InfinitePlace.mk φ).embedding x).re = (φ x).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h <;>
    simp [h, ComplexEmbedding.conjugate_coe_eq]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem trace_eq_sum_mult_mul_re {F : Type} [Field F] [NumberField F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) =
      ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  classical

  have htr : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ σ : F →ₐ[ℚ] ℂ, σ x := by
    rw [← trace_eq_sum_embeddings ℂ (K := ℚ) (L := F), eq_ratCast]
  have hre : ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re := by
    have h := congrArg Complex.re htr
    rw [Complex.ratCast_re, Complex.re_sum] at h
    rw [h, ← (RingHom.equivRatAlgHom F ℂ).sum_comp]
    rfl

  rw [hre, ← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hfib : ∀ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w),
      (φ x).re = (w.embedding x).re := by
    intro φ hφ
    rw [(Finset.mem_filter.mp hφ).2.symm, re_embedding_mk]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    nsmul_eq_mul]

end GlobalTheory.TraceRealEmbeddingSum
