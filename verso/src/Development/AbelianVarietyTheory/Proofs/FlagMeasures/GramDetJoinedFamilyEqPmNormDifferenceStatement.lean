import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramDetJoinedFamilyEqPmNormDifference
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GramDet.det_gram_sum_elim` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FGramDetJoinedFamilyEqPmNormDifference.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.gramDet_joinedFamily_eq_pm_norm_difference : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F) (hf : ∀ a b, H.h (f a) (f b) = if a = Fin.last r ∧ b = Fin.last r then -(algebraMap F E T) else 0) (hf' : ∀ a b, H.h (f' a) (f' b) = if a = Fin.last r ∧ b = Fin.last r then -(algebraMap F E T') else 0) (hD : IsUnit (H.Dl f f' (r + 1))), (H.gram (Sum.elim f f')).det = H.Gdet f f' T T' ∨ (H.gram (Sum.elim f f')).det = -H.Gdet f f' T T' := by
  first | exact @GlobalTheory.GramDet.det_gram_sum_elim | exact GlobalTheory.GramDet.det_gram_sum_elim | (intros; apply GlobalTheory.GramDet.det_gram_sum_elim <;> assumption)
