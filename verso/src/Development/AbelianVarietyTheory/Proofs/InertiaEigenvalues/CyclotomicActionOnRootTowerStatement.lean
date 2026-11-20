import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicActionOnRootTower
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCyclotomicActionOnRootTower.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.cyclotomic_action_on_root_tower : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (u : ℕ), (P.χQ g : ℚ_[l]) = (u : ℚ_[l]) → ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j ^ u := by
  first | exact @GlobalTheory.ExpImage.actT_εroot_eq_pow | exact GlobalTheory.ExpImage.actT_εroot_eq_pow | (intros; apply GlobalTheory.ExpImage.actT_εroot_eq_pow <;> assumption)
