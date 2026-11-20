import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsLocalPrimeAinf.lean&line=281#L281)
-/
theorem _root_.GlobalTheory.T.exists_local_prime_ainf : ∀ (l : ℕ) [Fact l.Prime], ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) := by
  first | exact @GlobalTheory.MemLoc.exists_locPrime_tied | exact GlobalTheory.MemLoc.exists_locPrime_tied | (intros; apply GlobalTheory.MemLoc.exists_locPrime_tied <;> assumption)
