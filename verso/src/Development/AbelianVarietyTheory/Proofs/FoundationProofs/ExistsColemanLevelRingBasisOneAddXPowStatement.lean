import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsColemanLevelRingBasisOneAddXPow
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Col.lev_basis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsColemanLevelRingBasisOneAddXPow.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.exists_colemanLevelRing_basis_one_add_X_pow : ∀ (R : Type) [CommRing R] (p m : ℕ) [hp : Fact p.Prime], IsAdicComplete (Ideal.span {(p : R)}) R → ∃ b : Module.Basis (Fin (Nat.totient (p ^ m))) R (lev R p m), ∀ i, b i = ev R p m ((1 + X) ^ (i : ℕ)) := by
  first | exact @GlobalTheory.Col.lev_basis | exact GlobalTheory.Col.lev_basis | (intros; apply GlobalTheory.Col.lev_basis <;> assumption)
