import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCharEqOfIsReducedFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_pow_char_eq_of_isReduced_finite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPowCharEqOfIsReducedFinite.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_pow_char_eq_of_isReduced_finite' : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A], ∀ a : A, ∃ b : A, a = b ^ p := by
  first | exact @GlobalTheory.exists_pow_char_eq_of_isReduced_finite | exact GlobalTheory.exists_pow_char_eq_of_isReduced_finite | (intros; apply GlobalTheory.exists_pow_char_eq_of_isReduced_finite <;> assumption)
