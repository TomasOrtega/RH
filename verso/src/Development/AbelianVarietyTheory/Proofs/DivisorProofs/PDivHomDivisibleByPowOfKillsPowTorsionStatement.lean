import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivHomDivisibleByPowOfKillsPowTorsion
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPDivHomDivisibleByPowOfKillsPowTorsion.lean&line=176#L176)
-/
theorem _root_.GlobalTheory.T.pDivHom_divisible_by_pow_of_kills_pow_torsion : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (m : ℕ) (f : G ⟶ H), f.conv m = 1 → ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ m • g := by
  first | exact @GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one | exact GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one | (intros; apply GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one <;> assumption)
