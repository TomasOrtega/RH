import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFlagStepLocallyStandardDualCoeffOne
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.locStd_exists_flag_coef_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsFlagStepLocallyStandardDualCoeffOne.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_flagStep_locallyStandard_dualCoeff_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r) (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r), ∃ v ∈ Formalism.MainNotions.S.LocNG.img n (Fr.LamStd L), v ∈ Fr.Fj (a.val + 1) ∧ H.h v (Fr.es a) = 1 := by
  first | exact @GlobalTheory.locStd_exists_flag_coef_one | exact GlobalTheory.locStd_exists_flag_coef_one | (intros; apply GlobalTheory.locStd_exists_flag_coef_one <;> assumption)
