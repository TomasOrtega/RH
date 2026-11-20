import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingImageSaturatedAdicClosed
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FEtaleRingImageSaturatedAdicClosed.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.etaleRing_image_saturated_adicClosed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ (x : RW LL) (e : W.EE), (l : RW LL) * x = E.tie.ioE e → ∃ e', x = E.tie.ioE e') ∧ ∀ x : RW LL, (∀ k : ℕ, ∃ e r, x - E.tie.ioE e = (l : RW LL) ^ k * r) → ∃ e, x = E.tie.ioE e := by
  first | exact @GlobalTheory.Decompl.Sat.ioE_saturated_closed | exact GlobalTheory.Decompl.Sat.ioE_saturated_closed | (intros; apply GlobalTheory.Decompl.Sat.ioE_saturated_closed <;> assumption)
