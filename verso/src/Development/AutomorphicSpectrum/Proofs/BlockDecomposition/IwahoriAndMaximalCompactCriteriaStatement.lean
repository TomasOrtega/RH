import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIwahoriAndMaximalCompactCriteria.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.iwahori_and_maximal_compact_criteria : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (g : GLw n w), (g ∈ iwGL n w ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ (∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) ∧ ∀ i j, j < i → Valued.v (g.val i j) < 1) ∧ (g ∈ GlobalTheory.LFun.KGL w n ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) := by
  first | exact @GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries | exact GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries | (intros; apply GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries <;> assumption)
