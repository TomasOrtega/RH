import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NearPiSepComplete
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNearPiSepComplete.lean&line=197#L197)
-/
theorem _root_.GlobalTheory.T.nearPi_sep_complete_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ), (∀ x : RW LL, (∀ m, NearPi AI LL s m x) → ∃ r, x = (l : RW LL) * r) ∧ ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, NearPi AI LL s (i + k) (f i)) → ∃ x, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  first | exact @GlobalTheory.Decompl.nearPi_sep_complete | exact GlobalTheory.Decompl.nearPi_sep_complete | (intros; apply GlobalTheory.Decompl.nearPi_sep_complete <;> assumption)
