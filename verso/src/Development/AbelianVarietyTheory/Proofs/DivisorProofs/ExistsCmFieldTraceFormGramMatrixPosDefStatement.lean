import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmFieldTraceFormGramMatrixPosDef
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TraceLattice.exists_traceForm_matrix` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCmFieldTraceFormGramMatrixPosDef.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.exists_cmField_traceForm_gram_matrix_posDef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ) (ρ0 : 𝓞 E →+* Matrix (Fin m) (Fin m) ℤ), 1 ≤ m ∧ B0.transpose = B0 ∧ (B0.map (Int.cast : ℤ → ℝ)).PosDef ∧ ∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (H.bar a) := by
  first | exact @GlobalTheory.TraceLattice.exists_traceForm_matrix | exact GlobalTheory.TraceLattice.exists_traceForm_matrix | (intros; apply GlobalTheory.TraceLattice.exists_traceForm_matrix <;> assumption)
