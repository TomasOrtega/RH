import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianCongrOfPositiveIndexEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HermCongruence.congr_of_sigPosH_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHermitianCongrOfPositiveIndexEq.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.hermitian_congr_of_positiveIndex_eq : ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian), A.det ≠ 0 → B.det ≠ 0 → sigPosH hA = sigPosH hB → ∃ Z : GL (Fin n) ℂ, B = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (Z : Matrix (Fin n) (Fin n) ℂ) := by
  first | exact @GlobalTheory.HermCongruence.congr_of_sigPosH_eq | exact GlobalTheory.HermCongruence.congr_of_sigPosH_eq | (intros; apply GlobalTheory.HermCongruence.congr_of_sigPosH_eq <;> assumption)
