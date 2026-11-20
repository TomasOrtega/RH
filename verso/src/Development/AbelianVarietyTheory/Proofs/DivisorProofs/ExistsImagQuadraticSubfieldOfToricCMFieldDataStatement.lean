import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImagQuadraticSubfieldOfToricCMFieldData
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QuadInHost.exists_quadField` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsImagQuadraticSubfieldOfToricCMFieldData.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_imagQuadratic_subfield_of_toricCMFieldData : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → d % 4 = 3 → ∀ (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ K : IntermediateField ℚ E, Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ ∃ φK : K →+* ℂ, (∀ i, (φ i).comp (algebraMap K E) = φK) ∧ (starRingEnd ℂ).comp φK ≠ φK ∧ IsLatOf φK 1 Λ := by
  first | exact @GlobalTheory.QuadInHost.exists_quadField | exact GlobalTheory.QuadInHost.exists_quadField | (intros; apply GlobalTheory.QuadInHost.exists_quadField <;> assumption)
