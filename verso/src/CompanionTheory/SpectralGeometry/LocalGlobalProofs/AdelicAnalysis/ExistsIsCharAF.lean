import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import GroundTheory.GlobalFields.TateThesis.AdelicChar
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CharEx

/- English proof (translation)
Introduce `F _ _`. Use `⟨Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar F), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar (K := F))`. Introduce `x`. Conclude with `Circle.norm_coe _`.

Introduce `a show ((GroundTheory.Global.adelicChar F _ : Circle) : ℂ) = 1`. Rewrite using `[GroundTheory.Global.adelicChar_algebraMap]`. Both sides reduce to the same expression. Assume the negation of the conclusion as `h push Not at h`. Apply `GroundTheory.Global.adelicChar_ne_one (K := F)` to reduce the goal to its premises.

Use extensionality with `x`. Conclude with `h x`.
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
