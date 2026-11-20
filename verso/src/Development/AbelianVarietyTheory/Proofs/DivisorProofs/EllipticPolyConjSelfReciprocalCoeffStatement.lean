import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolyConjSelfReciprocalCoeff
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConjSelfRecip.ell_coeff_conj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEllipticPolyConjSelfReciprocalCoeff.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.elliptic_poly_conj_selfReciprocal_coeff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → P.coeff 0 ≠ 0 ∧ ∀ k ≤ n, P.coeff 0 * IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) := by
  first | exact @GlobalTheory.ConjSelfRecip.ell_coeff_conj | exact GlobalTheory.ConjSelfRecip.ell_coeff_conj | (intros; apply GlobalTheory.ConjSelfRecip.ell_coeff_conj <;> assumption)
