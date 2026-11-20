import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleArcDatumGivesArcProperty
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.admissibleArcDatum_gives_arcProperty` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAdmissibleArcDatumGivesArcProperty.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.arcCoordinatesCaseA_of_admArcA_of_P1free_of_adm11 : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → RamifiedCoefficientChains.adm11 D → UnusedSlot80.ArcLiftingCoordinates D HW F Cm := by
  first | exact @GlobalTheory.admissibleArcDatum_gives_arcProperty | exact GlobalTheory.admissibleArcDatum_gives_arcProperty | (intros; apply GlobalTheory.admissibleArcDatum_gives_arcProperty <;> assumption)
