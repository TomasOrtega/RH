import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormalGroupLawHomFormalGroupLawNatMultiple
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NMulHom.isHom_nmul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsFormalGroupLawHomFormalGroupLawNatMultiple.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.isFormalGroupLawHom_formalGroupLawNatMultiple : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ n, IsHom μ μ (nmul μ n) := by
  first | exact @GlobalTheory.NMulHom.isHom_nmul | exact GlobalTheory.NMulHom.isHom_nmul | (intros; apply GlobalTheory.NMulHom.isHom_nmul <;> assumption)
