import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import GroundTheory.GlobalFields.TateThesis.AdelicChar
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CharEx

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem exists_isCharAF : ∀ (F : Type) [Field F] [NumberField F], ∃ ψ, IsCharAF F ψ := by
  intro F _ _
  refine ⟨Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar F), ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar (K := F))
  · intro x
    exact Circle.norm_coe _
  · intro a
    show ((GroundTheory.Global.adelicChar F _ : Circle) : ℂ) = 1
    rw [GroundTheory.Global.adelicChar_algebraMap]
    rfl
  · by_contra h
    push Not at h
    apply GroundTheory.Global.adelicChar_ne_one (K := F)
    ext x
    exact h x

end GlobalTheory.CompanionTheory.SW.CharEx
