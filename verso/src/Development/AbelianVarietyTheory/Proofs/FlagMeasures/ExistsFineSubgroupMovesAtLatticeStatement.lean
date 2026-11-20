import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFineSubgroupMovesAtLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MoveFine.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsFineSubgroupMovesAtLattice.lean&line=478#L478)
-/
theorem _root_.GlobalTheory.T.exists_fineSubgroup_moves_at_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∃ B : AddSubgroup S.MW, Fine (S.refA (j + 1) Λ) (ind (S.Mv (j + 1) d Λ)) B ∧ ∀ w, S.Mv (j + 1) d Λ w → ∀ b ∈ B, S.moved Λ (w + b).1.1 (w + b).2.1 (S.sOf (w + b)) = S.moved Λ w.1.1 w.2.1 (S.sOf w) ∧ S.chiM j d Λ (w + b).1 (w + b).2.1 = S.chiM j d Λ w.1 w.2.1 ∧ (S.NoLeak Λ (w + b).2.1 ↔ S.NoLeak Λ w.2.1) := by
  first | exact @GlobalTheory.MoveFine.main | exact GlobalTheory.MoveFine.main | (intros; apply GlobalTheory.MoveFine.main <;> assumption)
