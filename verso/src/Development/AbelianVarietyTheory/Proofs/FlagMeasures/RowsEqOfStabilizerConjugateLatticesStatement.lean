import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsEqOfStabilizerConjugateLattices
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RowsOrb.rows_eq_of_conj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRowsEqOfStabilizerConjugateLattices.lean&line=332#L332)
-/
theorem _root_.GlobalTheory.T.rows_eq_of_stabilizer_conjugate_lattices : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ Λ₁ ∈ Y.what₂ u, ∀ Λ₂ ∈ Y.what₂ u, ∀ g : GlobalTheory.RowsOrb.Gz X u, g • GlobalTheory.RowsOrb.Lmap X u Λ₁ = GlobalTheory.RowsOrb.Lmap X u Λ₂ → Λ₁ = Λ₂ := by
  first | exact @GlobalTheory.RowsOrb.rows_eq_of_conj | exact GlobalTheory.RowsOrb.rows_eq_of_conj | (intros; apply GlobalTheory.RowsOrb.rows_eq_of_conj <;> assumption)
