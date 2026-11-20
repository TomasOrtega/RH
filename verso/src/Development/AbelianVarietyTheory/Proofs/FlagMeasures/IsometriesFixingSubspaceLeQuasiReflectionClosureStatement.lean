import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometriesFixingSubspaceLeQuasiReflectionClosure
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HL.QReflGen.fixG_le_closure` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsometriesFixingSubspaceLeQuasiReflectionClosure.lean&line=274#L274)
-/
theorem _root_.GlobalTheory.T.isometriesFixingSubspace_le_quasiReflection_closure : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → fixG L Hm (Submodule.span E (Set.range x)) ≤ Subgroup.closure {g | ∃ a ∈ perp L Hm (Submodule.span E (Set.range x)), IsQRefl L Hm a g} := by
  first | exact @GlobalTheory.HL.QReflGen.fixG_le_closure | exact GlobalTheory.HL.QReflGen.fixG_le_closure | (intros; apply GlobalTheory.HL.QReflGen.fixG_le_closure <;> assumption)
