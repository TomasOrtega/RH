import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix NumberField IsDedekindDomain
open scoped NNReal TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormInf

/- English proof (translation)
Use `letI : Algebra F ℂ := w.embedding.toAlgebra`. Rewrite using `[← InfinitePlace.norm_embedding_eq]`. Establish `e : w.embedding (Algebra.norm F y) = ∏ σ : E →ₐ[F] ℂ, σ y` using `Algebra.norm_eq_prod_embeddings F ℂ y`. Rewrite using `[e, norm_prod, ← AlgHom.card F E ℂ]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `h ⟨σ.toRingHom, RingHom.ext σ.commutes⟩` after adjusting the coercions. Use `_ = (c : ℝ) ^ Fintype.card (E →ₐ[F] ℂ) := by rw [Finset.prod_const, Finset.card_univ]`.
-/
theorem infPlace_norm_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace F) (y : E) (c : ℝ≥0) (h : ∀ τ : GlobalTheory.AdelicU.EmbOver E w, ‖τ.1 y‖₊ ≤ c) :
    w (Algebra.norm F y) ≤ (c : ℝ) ^ Module.finrank F E := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  rw [← InfinitePlace.norm_embedding_eq]
  have e : w.embedding (Algebra.norm F y) = ∏ σ : E →ₐ[F] ℂ, σ y := Algebra.norm_eq_prod_embeddings F ℂ y
  rw [e, norm_prod, ← AlgHom.card F E ℂ]
  calc ∏ σ : E →ₐ[F] ℂ, ‖σ y‖ ≤ ∏ _σ : E →ₐ[F] ℂ, (c : ℝ) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun σ _ => by
          exact_mod_cast h ⟨σ.toRingHom, RingHom.ext σ.commutes⟩
    _ = (c : ℝ) ^ Fintype.card (E →ₐ[F] ℂ) := by rw [Finset.prod_const, Finset.card_univ]

/- English proof (translation)
Introduce `D w y c h` and use `infPlace_norm_le w y c h`.
-/
theorem main : ∀ (D : D7) (w : InfinitePlace D.host.F) (y : D.host.E) (c : ℝ≥0), (∀ τ : GlobalTheory.AdelicU.EmbOver D.host.E w, ‖τ.1 y‖₊ ≤ c) → w (Algebra.norm D.host.F y) ≤ (c : ℝ) ^ Module.finrank D.host.F D.host.E :=
  fun D w y c h => infPlace_norm_le w y c h

end GlobalTheory.NormInf
