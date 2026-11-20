import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormPrincipleOfIsCyclicStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNormFromBaseChangeBaseChangePropertiesStatement

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem exists_isReal_embedding_eq_hom {F : Type} [Field F] (σ : F →+* ℝ) :
    ∃ (v : InfinitePlace F) (hv : v.IsReal), InfinitePlace.embedding_of_isReal hv = σ := by
  have hr : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hv : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := ⟨_, hr, rfl⟩
  refine ⟨_, hv, ?_⟩
  ext x
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hr]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem hasseNorm : GlobalTheory.Published.HasseNorm := by
  intro K L _ _ _ _ _ hG hC a ha hf hi
  refine GlobalTheory.T.hasseNormPrinciple_of_isCyclic K L hG hC a ha ⟨hf, fun alg => ?_⟩
  obtain ⟨v, hv, hσ⟩ := exists_isReal_embedding_eq_hom (algebraMap K ℝ)
  let φ : v.Completion →ₐ[K] ℝ :=
    { InfinitePlace.Completion.extensionEmbeddingOfIsReal hv with
      commutes' := fun x => by
        rw [← hσ]
        exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm x) }
  exact (GlobalTheory.T.isNormFromBaseChange_base_change_properties K L).1 v.Completion ℝ φ a (hi v)

end GlobalTheory.CNorm
