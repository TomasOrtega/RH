import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix NumberField IsDedekindDomain
open scoped NNReal TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormFin
open GlobalTheory.AdelicU

/- English proof (translation)
Rewrite using `[← absBar_algebraMap F v, ← IsScalarTower.algebraMap_apply, Algebra.norm_eq_prod_embeddings F (FvBar F v) y]`. Rewrite using `[show absBar F v (∏ τ : E →ₐ[F] FvBar F v, τ y) = ∏ τ : E →ₐ[F] FvBar F v, absBar F v (τ y) from map_prod (valBar F v) _ _]`. Rewrite using `[← AlgHom.card F E (FvBar F v), ← Finset.card_univ]`. Use `Finset.prod_le_pow_card _ _ _ fun τ _ => ?_` and prove the remaining obligations. Use `le_absFin F v τ ((1 : Fv F v) ⊗ₜ[F] y)` as an intermediate fact.

Simplify using `using this`.
-/
theorem nnnorm_algebraMap_norm_le (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (y : E) :
    ‖algebraMap F (Fv F v) (Algebra.norm F y)‖₊ ≤
      absFin F v ((1 : Fv F v) ⊗ₜ[F] y) ^ Module.finrank F E := by
  rw [← absBar_algebraMap F v, ← IsScalarTower.algebraMap_apply,
    Algebra.norm_eq_prod_embeddings F (FvBar F v) y]
  rw [show absBar F v (∏ τ : E →ₐ[F] FvBar F v, τ y) = ∏ τ : E →ₐ[F] FvBar F v, absBar F v (τ y) from
    map_prod (valBar F v) _ _]
  rw [← AlgHom.card F E (FvBar F v), ← Finset.card_univ]
  refine Finset.prod_le_pow_card _ _ _ fun τ _ => ?_
  have := le_absFin F v τ ((1 : Fv F v) ⊗ₜ[F] y)
  simpa using this

/- English proof (translation)
The claim follows from `nnnorm_algebraMap_norm_le D.host.F v y`.
-/
theorem normFin_le (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (y : D.host.E) :
    ‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F y)‖₊ ≤
      GlobalTheory.AdelicU.absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] y) ^ Module.finrank D.host.F D.host.E :=
  nnnorm_algebraMap_norm_le D.host.F v y

end GlobalTheory.NormFin
