import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitSigmaEqMulHilbert90InvAlg
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsUnitSigmaEqMulHilbert90InvAlg.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_unit_sigma_eq_mul_invAlg : ∀ (K : UQ) (B : InvAlg K) (u : B.A), u * B.σ u = 1 → ∃ β : B.Aˣ, B.σ (β : B.A) = β * u := by
  first | exact @GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma | exact GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma | (intros; apply GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma <;> assumption)
