import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweQuotientFiniteLengthFockPolynomials
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HoweR.fock_pack` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHoweQuotientFiniteLengthFockPolynomials.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.howeQuotientFiniteLength_fockPolynomials : ∀ (P Q R S : ℕ) (x : ℂ), Pack (fockAct2 P Q R S) (coinv P Q R S x) := by
  first | exact @GlobalTheory.HoweR.fock_pack | exact GlobalTheory.HoweR.fock_pack | (intros; apply GlobalTheory.HoweR.fock_pack <;> assumption)
