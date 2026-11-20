import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianFormCharPoly
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EllHermGlobal.exists_charpoly_herm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsHermitianFormCharPoly.lean&line=217#L217)
-/
theorem _root_.GlobalTheory.T.exists_hermitian_form_char_poly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → ∃ M G : Matrix (Fin n) (Fin n) E, M.charpoly = P ∧ IsUnit G ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom G = G ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * G * M = G := by
  first | exact @GlobalTheory.EllHermGlobal.exists_charpoly_herm | exact GlobalTheory.EllHermGlobal.exists_charpoly_herm | (intros; apply GlobalTheory.EllHermGlobal.exists_charpoly_herm <;> assumption)
