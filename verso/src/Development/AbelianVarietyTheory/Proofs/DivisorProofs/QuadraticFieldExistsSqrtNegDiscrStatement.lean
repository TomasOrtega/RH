import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFieldExistsSqrtNegDiscr
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_sq_eq_neg_of_discr_eq_neg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuadraticFieldExistsSqrtNegDiscr.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.quadraticField_exists_sqrt_neg_discr : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (h2 : Module.finrank ℚ K = 2) (hd : discr K = -(d : ℤ)), ∃ δ : K, δ ^ 2 = -(d : K) := by
  first | exact @GlobalTheory.exists_sq_eq_neg_of_discr_eq_neg | exact GlobalTheory.exists_sq_eq_neg_of_discr_eq_neg | (intros; apply GlobalTheory.exists_sq_eq_neg_of_discr_eq_neg <;> assumption)
