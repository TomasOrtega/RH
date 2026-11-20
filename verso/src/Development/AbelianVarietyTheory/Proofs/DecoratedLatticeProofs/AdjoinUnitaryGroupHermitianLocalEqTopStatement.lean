import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdjoinUnitaryGroupHermitianLocalEqTop
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FAdjoinUnitaryGroupHermitianLocalEqTop.lean&line=176#L176)
-/
theorem _root_.GlobalTheory.T.adjoin_unitaryGroup_hermitian_local_eq_top : ∀ (R : Type) [CommRing R] [IsLocalRing R] (s : R →+* R), (∀ x, s (s x) = x) → (∃ δ : R, IsUnit (δ - s δ)) → ∀ n : ℕ, 3 ≤ n → ∀ G : Matrix (Fin n) (Fin n) R, cT s G = G → IsUnit G → Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' (UJ s G : Set (GL (Fin n) R))) = ⊤ := by
  first | exact @GlobalTheory.UnitaryGen.adjoin_unitary_eq_top | exact GlobalTheory.UnitaryGen.adjoin_unitary_eq_top | (intros; apply GlobalTheory.UnitaryGen.adjoin_unitary_eq_top <;> assumption)
