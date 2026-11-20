import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Per.FracInv.tied_frac_invariant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FRatioInvariantInK0.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.ratio_invariant_in_K0 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, P.actQ g a * b = a * P.actQ g b) → ∃ c : ↥(K0 K), a = algebraMap ↥(K0 K) P.R.B c * b := by
  first | exact @GlobalTheory.Per.FracInv.tied_frac_invariant | exact GlobalTheory.Per.FracInv.tied_frac_invariant | (intros; apply GlobalTheory.Per.FracInv.tied_frac_invariant <;> assumption)
