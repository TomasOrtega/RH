import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRowAutomorphismsEqLatticeStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RowsOrb.card_autLz` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCardRowAutomorphismsEqLatticeStabilizer.lean&line=229#L229)
-/
theorem _root_.GlobalTheory.T.card_row_automorphisms_eq_lattice_stabilizer : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ Λ ∈ Y.what₂ u, Nat.card (autLz D (X.Fu u) Λ) = Nat.card (MulAction.stabilizer (GlobalTheory.RowsOrb.Gz X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  first | exact @GlobalTheory.RowsOrb.card_autLz | exact GlobalTheory.RowsOrb.card_autLz | (intros; apply GlobalTheory.RowsOrb.card_autLz <;> assumption)
