import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawNatMultipleAddMulLaws
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NMul.nmul_laws` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormalGroupLawNatMultipleAddMulLaws.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.formalGroupLawNatMultiple_add_mul_laws : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ m n : ℕ, (∀ i, constantCoeff (nmul μ n i) = 0) ∧ nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) ∧ (∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i)) ∧ nmul μ 1 = fun i => X i := by
  first | exact @GlobalTheory.NMul.nmul_laws | exact GlobalTheory.NMul.nmul_laws | (intros; apply GlobalTheory.NMul.nmul_laws <;> assumption)
