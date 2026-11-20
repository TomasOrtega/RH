import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPlusFrobeniusStableSubringInFilZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.CrisPlus.plus_props` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBcrisPlusFrobeniusStableSubringInFilZero.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.bcrisPlus_frobeniusStable_subring_in_filZero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), (∀ b, Plus T b → Plus T (P.φB b)) ∧ (∀ b, Plus T b → ∀ j, ev P j b ∈ Fil P 0) ∧ (∀ a b, Plus T a → Plus T b → Plus T (a + b) ∧ Plus T (a * b)) ∧ (∀ q : ℚ_[l], Plus T (algebraMap ℚ_[l] P.R.B q)) ∧ (∀ x : Formalism.Per.Ainf l, Plus T (T.eB.symm (Formalism.Per.aB l x))) ∧ Plus T P.tB := by
  first | exact @GlobalTheory.PMon.CrisPlus.plus_props | exact GlobalTheory.PMon.CrisPlus.plus_props | (intros; apply GlobalTheory.PMon.CrisPlus.plus_props <;> assumption)
