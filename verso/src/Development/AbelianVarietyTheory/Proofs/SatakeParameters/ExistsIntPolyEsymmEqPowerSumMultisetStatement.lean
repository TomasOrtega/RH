import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntPolyEsymmEqPowerSumMultiset
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
open GlobalTheory.Cong
/- English proof (citation)
Apply `GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsIntPolyEsymmEqPowerSumMultiset.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_intPoly_esymm_eq_powerSum_multiset : ∀ a n : ℕ, 1 ≤ n → ∃ P : MvPolynomial (Fin (a + 1)) ℤ, ∀ s : Multiset ℂ, Multiset.card s = a → MvPolynomial.aeval (fun j : Fin (a + 1) => s.esymm j) P = (s.map (· ^ n)).sum := by
  first | exact @GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq | exact GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq | (intros; apply GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq <;> assumption)
