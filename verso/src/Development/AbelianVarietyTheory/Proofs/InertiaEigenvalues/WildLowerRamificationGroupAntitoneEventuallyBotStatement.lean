import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildLowerRamificationGroupAntitoneEventuallyBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.Ram.wild_antitone_and_eventually_bot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWildLowerRamificationGroupAntitoneEventuallyBot.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L], Antitone (wild K L) ∧ ∃ m, wild K L m = ⊥ := by
  first | exact @GlobalTheory.PMon.Ram.wild_antitone_and_eventually_bot | exact GlobalTheory.PMon.Ram.wild_antitone_and_eventually_bot | (intros; apply GlobalTheory.PMon.Ram.wild_antitone_and_eventually_bot <;> assumption)
