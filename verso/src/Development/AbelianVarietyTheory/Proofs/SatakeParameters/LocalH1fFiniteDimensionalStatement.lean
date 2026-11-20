import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalH1fFiniteDimensional
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocalH1Finiteness.finite_H1fV_matRep` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLocalH1fFiniteDimensional.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.local_h1f_finite_dimensional : Formalism.GaloisCohomology.LocalFinitenessK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (k : ℕ) (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1), Continuous (fun g => M g) → (∀ g a b, ‖((M g a b : ↥LL.1) : Om l)‖ ≤ 1) → Module.Finite ↥LL.1 (FiniteCohomology (P.PD K) (matRep M)) := by
  first | exact @GlobalTheory.LocalH1Finiteness.finite_H1fV_matRep | exact GlobalTheory.LocalH1Finiteness.finite_H1fV_matRep | (intros; apply GlobalTheory.LocalH1Finiteness.finite_H1fV_matRep <;> assumption)
