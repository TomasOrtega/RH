import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFstUniqueSylvester
import Mathlib
import Formalism.SatakeDualWeyl.Statement

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FHasSignatureFstUniqueSylvester.lean&line=116#L116)
-/
theorem _root_.GlobalTheory.T.hasSignature_fst_unique_sylvester : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {a b a' b' : ℕ}, Formalism.UG.HasSignature J a b → Formalism.UG.HasSignature J a' b' → a = a' := by
  first | exact @GlobalTheory.SylvesterInertia.hasSignature_fst_unique | exact GlobalTheory.SylvesterInertia.hasSignature_fst_unique | (intros; apply GlobalTheory.SylvesterInertia.hasSignature_fst_unique <;> assumption)
