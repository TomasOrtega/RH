import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaUnitaryUpperTriangular
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExpStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraAnalyticityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudoCoefficientUnitaryPqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraCharactersOfInputsStatement
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIwasawaUnitaryUpperTriangular.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.iwasawa_unitary_upper_triangular : ∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ), IsUnit g → ∃ k ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ b : Matrix (Fin m) (Fin m) ℂ, g = k * b ∧ b.BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular | exact GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular | (intros; apply GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular <;> assumption)
