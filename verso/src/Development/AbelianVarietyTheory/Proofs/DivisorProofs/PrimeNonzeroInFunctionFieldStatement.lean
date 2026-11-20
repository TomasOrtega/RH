import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeNonzeroInFunctionField
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Vert.Model.natCast_prime_ne_zero_kbar` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrimeNonzeroInFunctionField.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.prime_nonzero_in_function_field : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] (B : GlobalTheory.Vert.Model O), ((p : ℕ) : Kbar B.X) ≠ 0 := by
  first | exact @GlobalTheory.Vert.Model.natCast_prime_ne_zero_kbar | exact GlobalTheory.Vert.Model.natCast_prime_ne_zero_kbar | (intros; apply GlobalTheory.Vert.Model.natCast_prime_ne_zero_kbar <;> assumption)
