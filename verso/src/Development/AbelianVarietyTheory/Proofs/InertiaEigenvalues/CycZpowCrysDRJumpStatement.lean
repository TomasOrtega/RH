import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZpowCrysDRJump
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CycPow.cyc_zpow_crys_dR_jump` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCycZpowCrysDRJump.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.cyc_zpow_crys_dR_jump_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (k : ℤ), IsCrys (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ IsDR (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) τ a = if a = -k then 1 else 0 := by
  first | exact @GlobalTheory.CycPow.cyc_zpow_crys_dR_jump | exact GlobalTheory.CycPow.cyc_zpow_crys_dR_jump | (intros; apply GlobalTheory.CycPow.cyc_zpow_crys_dR_jump <;> assumption)
