import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermDefectEqOfLatticeEq
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLocalTermDefectEqOfLatticeEq.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.localTerm_defect_eq_of_lattice_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d d' : LocNG.Datum P) (τ τ' : Term V M r), LocNG.IsTermOver P d τ → LocNG.IsTermOver P d' τ' → τ.abelian₂ = τ'.abelian₂ → (LocNG.BBne (H := H) τ ↔ LocNG.BBne (H := H) τ') := by
  first | exact @GlobalTheory.HL.LocDefect.bbne_of_lam_eq | exact GlobalTheory.HL.LocDefect.bbne_of_lam_eq | (intros; apply GlobalTheory.HL.LocDefect.bbne_of_lam_eq <;> assumption)
