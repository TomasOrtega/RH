import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCongruenceKernelTraceCharacter
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
open GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.congChar_exists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsCongruenceKernelTraceCharacter.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.exists_congruenceKernel_trace_character : ∀ (R A : Type) [CommRing R] [IsDomain R] [AddCommGroup A] (a : ℕ) (c : R), c ≠ 0 → ∀ (φ : R →+ A), (∀ x, φ (c * x) = 0) → ∀ B : Matrix (Fin a) (Fin a) R, ∃ lam : (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {c}))).ker →* Multiplicative A, ∀ g (x : Matrix (Fin a) (Fin a) R), (g.1 : Matrix (Fin a) (Fin a) R) = 1 + c • x → lam g = Multiplicative.ofAdd (φ (B * x).trace) := by
  first | exact @GlobalTheory.congChar_exists | exact GlobalTheory.congChar_exists | (intros; apply GlobalTheory.congChar_exists; all_goals assumption)
