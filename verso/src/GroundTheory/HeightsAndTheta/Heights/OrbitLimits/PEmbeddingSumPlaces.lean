import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsEmbeddingSumPlaces
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace

open scoped Classical in

/- English proof (translation)
Introduce `F _ _ g hg`. Rewrite using `[← Finset.univ.sum_fiberwise (fun σ => InfinitePlace.mk σ)]`. Use `Finset.sum_congr rfl (fun w _ => ?_)` and prove the remaining obligations. Establish `h : ∀ σ ∈ ({σ | InfinitePlace.mk σ = w} : Finset (F →+* ℂ)), g σ = g w.embedding`. Introduce `σ hσ`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ`. Substitute `hσ` using the available equality. Break down `embedding_mk_eq σ with h | h` into its components or cases. Rewrite using `[h]`. Rewrite using `[h, hg]`.

Rewrite using `[Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]`. Use `congr 1`. Conclude with `card_filter_mk_eq w` after adjusting the coercions.
-/
theorem EmbeddingSumPlaces.proof : EmbeddingSumPlaces.Statement := by
  intro F _ _ g hg
  rw [← Finset.univ.sum_fiberwise (fun σ => InfinitePlace.mk σ)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have h : ∀ σ ∈ ({σ | InfinitePlace.mk σ = w} : Finset (F →+* ℂ)), g σ = g w.embedding := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    subst hσ
    rcases embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h, hg]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  congr 1
  exact_mod_cast card_filter_mk_eq w

end GroundTheory.Heights₂.Heights.Targets
