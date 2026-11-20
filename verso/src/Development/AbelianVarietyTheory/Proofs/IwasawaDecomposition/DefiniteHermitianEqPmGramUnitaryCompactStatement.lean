import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteHermitianEqPmGramUnitaryCompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
import Formalism.SatakeDualWeyl.Statement
import Formalism.FormalDegreeBessel.StatementG
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DefiniteFrame.definite_frame` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDefiniteHermitianEqPmGramUnitaryCompact.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.definite_hermitian_eq_pm_gram_unitary_compact : ∀ (n p q : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Formalism.UG.HasSignature J p q → (p = 0 ∨ q = 0) → (∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ (J = Bᴴ * B ∨ J = -(Bᴴ * B))) ∧ IsCompact (Formalism.QuantumDeterminants.UH J) := by
  first | exact @GlobalTheory.DefiniteFrame.definite_frame | exact GlobalTheory.DefiniteFrame.definite_frame | (intros; apply GlobalTheory.DefiniteFrame.definite_frame <;> assumption)
