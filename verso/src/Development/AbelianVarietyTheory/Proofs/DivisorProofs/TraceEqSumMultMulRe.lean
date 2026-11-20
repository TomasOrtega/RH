import Mathlib

namespace GlobalTheory.TraceRealEmbeddingSum

open NumberField

/- English proof (translation)
Apply the tactic sequence `rcases InfinitePlace.embedding_mk_eq φ with h | h <;>`. Simplify using `[h, ComplexEmbedding.conjugate_coe_eq]`.
-/
theorem re_embedding_mk {F : Type} [Field F] (φ : F →+* ℂ) (x : F) :
    ((InfinitePlace.mk φ).embedding x).re = (φ x).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h <;>
    simp [h, ComplexEmbedding.conjugate_coe_eq]

/- English proof (translation)
Establish `htr : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ σ : F →ₐ[ℚ] ℂ, σ x`. Rewrite using `[← trace_eq_sum_embeddings ℂ (K := ℚ) (L := F), eq_ratCast]`. Establish `hre : ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re`. Establish `h` using `congrArg Complex.re htr`. Rewrite `h` using `[Complex.ratCast_re, Complex.re_sum]`.

Rewrite using `[h, ← (RingHom.equivRatAlgHom F ℂ).sum_comp]`. Both sides reduce to the same expression. Rewrite using `[hre, ← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => InfinitePlace.mk φ)]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hfib : ∀ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w), (φ x).re = (w.embedding x).re`.

Introduce `φ hφ`. Rewrite using `[(Finset.mem_filter.mp hφ).2.symm, re_embedding_mk]`. Rewrite using `[Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]`.
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
