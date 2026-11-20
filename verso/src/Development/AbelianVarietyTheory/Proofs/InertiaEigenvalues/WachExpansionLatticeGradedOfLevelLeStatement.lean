import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeGradedOfLevelLe
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NL.GradedLat.graded_of_level_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWachExpansionLatticeGradedOfLevelLe.lean&line=253#L253)
-/
theorem _root_.GlobalTheory.T.wachExpansionLattice_graded_of_level_le : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ s) = 1 → Full (Di (HW l) h T i) (Lat C h T i ζ) → Graded (Lat C h T i ζ) := by
  first | exact @GlobalTheory.NL.GradedLat.graded_of_level_le | exact GlobalTheory.NL.GradedLat.graded_of_level_le | (intros; apply GlobalTheory.NL.GradedLat.graded_of_level_le <;> assumption)
