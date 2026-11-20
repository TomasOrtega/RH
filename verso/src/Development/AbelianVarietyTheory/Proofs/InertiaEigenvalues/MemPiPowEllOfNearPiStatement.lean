import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPiPowEllOfNearPi
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Decompl.mem_pow_pi_of_nearPi` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMemPiPowEllOfNearPi.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.mem_pi_pow_ell_of_nearPi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (m : ℕ) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), NearPi AI LL s m (inclR LL (E.tie.io a)) → ∃ a1 a2 : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), a = letπ ^ m * a1 + (l : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) * a2 := by
  first | exact @GlobalTheory.Decompl.mem_pow_pi_of_nearPi | exact GlobalTheory.Decompl.mem_pow_pi_of_nearPi | (intros; apply GlobalTheory.Decompl.mem_pow_pi_of_nearPi <;> assumption)
