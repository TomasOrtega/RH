import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPartitionRowsNumericDatumMemIcc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FFockPartitionRowsNumericDatumMemIcc.lean&line=141#L141)
-/
theorem _root_.GlobalTheory.T.fockPartitionRows_numericDatum_mem_Icc : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word), ∀ j ∈ (numDatumOfParameters D L).lifts, ∀ z, ∀ i < D.R.N (j - 1), 0 ≤ (numDatumOfParameters D L).nu (codeRec L u) j z i ∧ (((numDatumOfParameters D L).nu (codeRec L u) j z i : ℚ) : ℝ) ≤ 3 * L.sc.a := by
  first | exact @GlobalTheory.CoreHt.RowsRangeS.nu_numRec_mem | exact GlobalTheory.CoreHt.RowsRangeS.nu_numRec_mem | (intros; apply GlobalTheory.CoreHt.RowsRangeS.nu_numRec_mem <;> assumption)
