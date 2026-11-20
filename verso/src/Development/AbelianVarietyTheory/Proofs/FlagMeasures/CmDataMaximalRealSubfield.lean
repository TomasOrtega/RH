import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPositiveAdd

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.StdDefinite

open GlobalTheory.AutInhab

/- English proof (translation)
Take `⟨σ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Establish `hne : ∃ z : K, star z ≠ z`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `haveI := hK.1`.

Use `IsTotallyComplex.complexEmbedding_not_isReal σ ?_` and prove the remaining obligations. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `z`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, ← hK.2.1, hcon]`. Use `haveI : IsCMField K := GlobalTheory.LeastExponentCompare.isCMField_of_conj K star hK.2.1 hne`.

Use `⟨hK, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _, fun a => ⟨fun h => ?_, ?_⟩⟩` and prove the remaining obligations. Use `⟨⟨a, fun φ => ?_⟩, rfl⟩` and prove the remaining obligations. Use `hK.2.1 φ a` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `this.symm`.

Introduce and unpack `⟨b, rfl⟩`. Apply `σ.injective` to reduce the goal to its premises. Rewrite using `[hK.2.1]`. Conclude with `b.2 σ`.
-/
theorem cmData_maximalRealSubfield {K : Type} [Field K] [NumberField K] [StarRing K]
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : Formalism.BasicNotions.CMData (maximalRealSubfield K) K := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hne : ∃ z : K, star z ≠ z := by
    by_contra hcon
    push Not at hcon
    haveI := hK.1
    refine IsTotallyComplex.complexEmbedding_not_isReal σ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext z
    rw [ComplexEmbedding.conjugate_coe_eq, ← hK.2.1, hcon]
  haveI : IsCMField K := GlobalTheory.LeastExponentCompare.isCMField_of_conj K star hK.2.1 hne
  refine ⟨hK, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _, fun a => ⟨fun h => ?_, ?_⟩⟩
  · refine ⟨⟨a, fun φ => ?_⟩, rfl⟩
    have := hK.2.1 φ a
    rw [h] at this
    exact this.symm
  · rintro ⟨b, rfl⟩
    apply σ.injective
    rw [hK.2.1]
    exact b.2 σ

end GlobalTheory.StdDefinite
