import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionLocalDataPreservedDivisionLatticeChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLocalDataTransportDivision
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDivisionLocalDataPreservedDivisionLatticeChange.lean&line=148#L148)
-/
theorem _root_.GlobalTheory.T.divisionLocalData_preserved_divisionLatticeChange : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) (Y : DivX (w.D Z)) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), DivT n Y → Nonempty (DivT (nchTTr w Z N h n) (divTr (D := w.D Z) N h Y)) := by
  first | exact @GlobalTheory.Mem.Top.Bl.WitTr.divT_setDiv | exact GlobalTheory.Mem.Top.Bl.WitTr.divT_setDiv | (intros; apply GlobalTheory.Mem.Top.Bl.WitTr.divT_setDiv <;> assumption)
