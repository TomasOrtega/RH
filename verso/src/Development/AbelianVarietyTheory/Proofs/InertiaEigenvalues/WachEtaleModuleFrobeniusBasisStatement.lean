import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachEtaleModuleFrobeniusBasis
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtaleFrob.phi_basis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWachEtaleModuleFrobeniusBasis.lean&line=148#L148)
-/
theorem _root_.GlobalTheory.T.wachEtaleModule_frobenius_basis : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ (r : ℕ) (b b' : Module.Basis (Fin r) W.EE (W.DD T)), ∀ j, b' j = W.φD T (b j) := by
  first | exact @GlobalTheory.EtaleFrob.phi_basis | exact GlobalTheory.EtaleFrob.phi_basis | (intros; apply GlobalTheory.EtaleFrob.phi_basis <;> assumption)
