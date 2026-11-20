import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardHodgeTateJumpsCrystallineEqDim
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCardHodgeTateJumpsCrystallineEqDim.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.card_hodgeTate_jumps_crystalline_eq_dim : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (V : Type) [AddCommGroup V] [Module ↥LL.1 V]
      [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
      (ρ : Representation ↥LL.1 ↥(GK K) V) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ),
      IsCrys (P.PD K) ρ →
      (∀ i τ, tableLineDegreeTwo.Over (H.W K 1 LL hA.2.2).emb i τ → ∀ a, multV (P.PD K) ρ τ a = (U i).count a) →
      ∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 V := by
  first | exact @GlobalTheory.Per.LetterJumps.card_jumps_letter | exact GlobalTheory.Per.LetterJumps.card_jumps_letter | (intros; apply GlobalTheory.Per.LetterJumps.card_jumps_letter <;> assumption)
