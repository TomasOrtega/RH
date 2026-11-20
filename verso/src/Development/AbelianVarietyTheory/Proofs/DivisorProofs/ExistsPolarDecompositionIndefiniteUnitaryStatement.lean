import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarDecompositionIndefiniteUnitary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped Matrix
open Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPolarDecompositionIndefiniteUnitary.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.exists_polar_decomposition_indefiniteUnitary : ∀ (R S : ℕ) (u : Mat R S), uᴴ * Jm R S * u = Jm R S → ∃ k q : Mat R S, kᴴ * Jm R S * k = Jm R S ∧
    Jm R S * k = k * Jm R S ∧ qᴴ * Jm R S * q = Jm R S ∧ Jm R S * q * Jm R S * q = 1 ∧ u = k * q * q := by
  first | exact @GlobalTheory.UnitaryPolar.polar | exact GlobalTheory.UnitaryPolar.polar | (intros; apply GlobalTheory.UnitaryPolar.polar <;> assumption)
